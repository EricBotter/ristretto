package ristretto.asm

import ristretto.asm.AsmSyntax._

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import ristretto.main.{Compiler => Errors}

object RegisterAllocation {

  val WORDSIZE = 8
  def wrapPrologueAndEpilogue(maxArgs: Int, map: Map[String, Operand], label: String, insns: List[Insn]): List[Insn] = {
    // On MacOS, we need to align the stack on 16-byte boundaries
    val unalignedSize = (map.size + maxArgs) * WORDSIZE
    // size: 0 -> 0 + 0 = 0
    // size: 4 -> 4 + 12 = 16
    // size: 8 -> 8 + 8 = 16
    // size: 12 -> 12 + 4 = 16
    // size: 16 -> 16 + 0 = 16
    // size: 20 -> 20 + 12 = 32
    // ...
    val size = unalignedSize + (16 - (unalignedSize % 16)) % 16
    Label(s"_$label") ::
      Push(BP()) ::
      Mov(SP(), BP()) ::
      Sub(Immediate(size), SP()) ::
      insns flatMap {
      // Replace Ret instructions with the epilogue
      case Ret() =>
        Add(Immediate(size), SP()) ::
          Pop1(BP()) ::
          Ret() ::
          Nil
      case insn =>
        insn :: Nil
    }
  }

  var callToArgNum: Map[String, Int] = Map()

  def liveness(proc: Proc): List[Set[AsmSyntax.Operand]] = {
    callToArgNum = Map()
    var args = 0
    for (stm <- proc.insns) stm match {
      case Mov(_, Arg(i)) => args = math.max(args, i)
      case Call(fun) =>
        callToArgNum += (fun.toString -> args)
        args = 0
      case _ =>
    }

    var live = new ListBuffer[Set[AsmSyntax.Operand]]
    live += Set.empty
    var changed = true
    while (changed) {
      changed = false
      for (stm <- proc.insns.reverse) {
        var current = live.last
        current = stm match {
          case Push(src@Pseudo(_)) => current + src
          case Pop1(dst@Pseudo(_)) => current - dst
          case Add(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Add(_, dst@Pseudo(_)) => current - dst
          case Add(src@Pseudo(_), _) => current + src
          case Sub(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Sub(_, dst@Pseudo(_)) => current - dst
          case Sub(src@Pseudo(_), _) => current + src
          case Mul(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Mul(_, dst@Pseudo(_)) => current - dst
          case Mul(src@Pseudo(_), _) => current + src
          case Div(dst@Pseudo(_)) => current - dst
          case Shl(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Shl(_, dst@Pseudo(_)) => current - dst
          case Shl(src@Pseudo(_), _) => current + src
          case Shr(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Shr(_, dst@Pseudo(_)) => current - dst
          case Shr(src@Pseudo(_), _) => current + src
          case Mov(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Mov(_, dst@Pseudo(_)) => current - dst
          case Mov(src@Pseudo(_), _) => current + src
          case And(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case And(_, dst@Pseudo(_)) => current - dst
          case And(src@Pseudo(_), _) => current + src
          case Xor(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Xor(_, dst@Pseudo(_)) => current - dst
          case Xor(src@Pseudo(_), _) => current + src
          case Or(src@Pseudo(_), dst@Pseudo(_)) => current - dst + src
          case Or(_, dst@Pseudo(_)) => current - dst
          case Or(src@Pseudo(_), _) => current + src
          case Cmp(r1@Pseudo(_), r2@Pseudo(_)) => current + r2 + r1
          case Cmp(_, r2@Pseudo(_)) => current + r2
          case Cmp(r1@Pseudo(_), _) => current + r1

          case Jmp(label) => current
          case JE(label) => current
          case JG(label) => current
          case JL(label) => current
          case JGE(label) => current
          case JLE(label) => current
          case JNE(label) => current
          case Call(fun) =>
            current ++ (for (i <- 0 to callToArgNum(fun.toString)) yield Arg(i))
          case Ret() => current
          case Label(location) => current
          case CommentInsn(_) => current
          case _ => current
        }
        live += current
      } // TODO - fix jumps and iterate again
    }
    live.toList.reverse
  }

  def inference(live: List[Set[AsmSyntax.Operand]]): Map[AsmSyntax.Operand, Set[AsmSyntax.Operand]] = {
    val out: mutable.Map[AsmSyntax.Operand, Set[AsmSyntax.Operand]] = mutable.Map.empty
    for (set <- live) {
      for (t1 <- set; t2 <- set) {
        if (t1 != t2) {
          out(t1) = out.getOrElse(t1, Set.empty) + t2
          out(t2) = out.getOrElse(t2, Set.empty) + t1
        }
      }
    }
    out.toMap
  }

  def registerArray: Array[AsmSyntax.Operand] = Array(
    DI(), SI(), AX(), BX(), CX(), DX(), R8(), R9(), R10(), R11(), R12(), R13(), R14(), R15()
  )

  def coloring(graph: Map[AsmSyntax.Operand, Set[AsmSyntax.Operand]],
               colors: Array[AsmSyntax.Operand])
  : Map[AsmSyntax.Operand, AsmSyntax.Operand] = {
    val available = mutable.Set[AsmSyntax.Operand]()
    var colored = Map[AsmSyntax.Operand, AsmSyntax.Operand]()

    for ((k,v) <- graph) {
      for (c <- colors) available += c
      for (n <- v) available -= colored.getOrElse(n, SP())
      if (available.isEmpty)
        Errors.fatalError("could not color the graph")
      colored = colored + (k -> available.last)
    }
    colored
  }

  def applyAllocation(proc: Proc, coloring: Map[AsmSyntax.Operand, AsmSyntax.Operand]): Proc = {
    Proc(proc.location, for (stm <- proc.insns) yield {
      //      println(stm)
      try {
        stm match {
          case Push(src@Pseudo(_)) => Push(coloring(src))
          case Pop1(dst@Pseudo(_)) => Pop1(coloring(dst))
          case Add(src@Pseudo(_), dst@Pseudo(_)) => Add(coloring(src), coloring(dst))
          case Add(src, dst@Pseudo(_)) => Add(src, coloring(dst))
          case Add(src@Pseudo(_), dst) => Add(coloring(src), dst)
          case Sub(src@Pseudo(_), dst@Pseudo(_)) => Sub(coloring(src), coloring(dst))
          case Sub(src, dst@Pseudo(_)) => Sub(src, coloring(dst))
          case Sub(src@Pseudo(_), dst) => Sub(coloring(src), dst)
          case Mul(src@Pseudo(_), dst@Pseudo(_)) => Mul(coloring(src), coloring(dst))
          case Mul(src, dst@Pseudo(_)) => Mul(src, coloring(dst))
          case Mul(src@Pseudo(_), dst) => Mul(coloring(src), dst)
          case Div(dst@Pseudo(_)) => Div(coloring(dst))
          case Shl(src@Pseudo(_), dst@Pseudo(_)) => Shl(coloring(src), coloring(dst))
          case Shl(src, dst@Pseudo(_)) => Shl(src, coloring(dst))
          case Shl(src@Pseudo(_), dst) => Shl(coloring(src), dst)
          case Shr(src@Pseudo(_), dst@Pseudo(_)) => Shr(coloring(src), coloring(dst))
          case Shr(src, dst@Pseudo(_)) => Shr(src, coloring(dst))
          case Shr(src@Pseudo(_), dst) => Shr(coloring(src), dst)
          case Mov(src@Pseudo(_), dst@Pseudo(_)) => Mov(coloring(src), coloring(dst))
          case Mov(src, dst@Pseudo(_)) => Mov(src, coloring(dst))
          case Mov(src@Pseudo(_), dst) => Mov(coloring(src), dst)
          case And(src@Pseudo(_), dst@Pseudo(_)) => And(coloring(src), coloring(dst))
          case And(src, dst@Pseudo(_)) => And(src, coloring(dst))
          case And(src@Pseudo(_), dst) => And(coloring(src), dst)
          case Xor(src@Pseudo(_), dst@Pseudo(_)) => Xor(coloring(src), coloring(dst))
          case Xor(src, dst@Pseudo(_)) => Xor(src, coloring(dst))
          case Xor(src@Pseudo(_), dst) => Xor(coloring(src), dst)
          case Or(src@Pseudo(_), dst@Pseudo(_)) => Or(coloring(src), coloring(dst))
          case Or(src, dst@Pseudo(_)) => Or(src, coloring(dst))
          case Or(src@Pseudo(_), dst) => Or(coloring(src), dst)
          case Cmp(r1@Pseudo(_), r2@Pseudo(_)) => Cmp(coloring(r1), coloring(r2))
          case Cmp(r1, r2@Pseudo(_)) => Cmp(r1, coloring(r2))
          case Cmp(r1@Pseudo(_), r2) => Cmp(coloring(r1), r2)

          case x => x
        }
      } catch {
        case _: NoSuchElementException => CommentInsn("Instruction removed (destination unused): " + stm)
      }
    })
  }

  def argAddress(i: Int): Operand = i match {
    case 0 => DI()
    case 1 => SI()
    case 2 => DX()
    case 3 => CX()
    case 4 => R8()
    case 5 => R9()
    case _ => Address(WORDSIZE * (i - 6), SP()) // 6 -> 0(sp), 7 -> 8(sp), 8 -> 16(sp), ...
  }

  def allocateArgs(proc: Proc): Proc = {
    Proc(proc.location, for (stm <- proc.insns) yield stm match {
      case Push(Arg(src)) => Push(argAddress(src))
      case Pop1(Arg(dst)) => Pop1(argAddress(dst))
      case Add(Arg(src), Arg(dst)) => Add(argAddress(src), argAddress(dst))
      case Add(src, Arg(dst)) => Add(src, argAddress(dst))
      case Add(Arg(src), dst) => Add(argAddress(src), dst)
      case Sub(Arg(src), Arg(dst)) => Sub(argAddress(src), argAddress(dst))
      case Sub(src, Arg(dst)) => Sub(src, argAddress(dst))
      case Sub(Arg(src), dst) => Sub(argAddress(src), dst)
      case Mul(Arg(src), Arg(dst)) => Mul(argAddress(src), argAddress(dst))
      case Mul(src, Arg(dst)) => Mul(src, argAddress(dst))
      case Mul(Arg(src), dst) => Mul(argAddress(src), dst)
      case Div(Arg(dst)) => Div(argAddress(dst))
      case Shl(Arg(src), Arg(dst)) => Shl(argAddress(src), argAddress(dst))
      case Shl(src, Arg(dst)) => Shl(src, argAddress(dst))
      case Shl(Arg(src), dst) => Shl(argAddress(src), dst)
      case Shr(Arg(src), Arg(dst)) => Shr(argAddress(src), argAddress(dst))
      case Shr(src, Arg(dst)) => Shr(src, argAddress(dst))
      case Shr(Arg(src), dst) => Shr(argAddress(src), dst)
      case Mov(Arg(src), Arg(dst)) => Mov(argAddress(src), argAddress(dst))
      case Mov(src, Arg(dst)) => Mov(src, argAddress(dst))
      case Mov(Arg(src), dst) => Mov(argAddress(src), dst)
      case And(Arg(src), Arg(dst)) => And(argAddress(src), argAddress(dst))
      case And(src, Arg(dst)) => And(src, argAddress(dst))
      case And(Arg(src), dst) => And(argAddress(src), dst)
      case Xor(Arg(src), Arg(dst)) => Xor(argAddress(src), argAddress(dst))
      case Xor(src, Arg(dst)) => Xor(src, argAddress(dst))
      case Xor(Arg(src), dst) => Xor(argAddress(src), dst)
      case Or(Arg(src), Arg(dst)) => Or(argAddress(src), argAddress(dst))
      case Or(src, Arg(dst)) => Or(src, argAddress(dst))
      case Or(Arg(src), dst) => Or(argAddress(src), dst)
      case Cmp(Arg(r1), Arg(r2)) => Cmp(argAddress(r1), argAddress(r2))
      case Cmp(r1, Arg(r2)) => Cmp(r1, argAddress(r2))
      case Cmp(Arg(r1), r2) => Cmp(argAddress(r1), r2)
      case _ => stm
    })
  }

  def paramAddress(i: Int): Operand = i match {
    case 0 => DI()
    case 1 => SI()
    case 2 => DX()
    case 3 => CX()
    case 4 => R8()
    case 5 => R9()
    case _ => Address(WORDSIZE * (i - 6 + 2), BP()) // 6 -> 16(bp), 7 -> 24(bp), 8 -> 32(bp)
  }

  def allocateParams(proc: Proc): Proc = {
    Proc(proc.location, for (stm <- proc.insns) yield stm match {
      case Push(Param(src)) => Push(paramAddress(src))
      case Pop1(Param(dst)) => Pop1(paramAddress(dst))
      case Add(Param(src), Param(dst)) => Add(paramAddress(src), paramAddress(dst))
      case Add(src, Param(dst)) => Add(src, paramAddress(dst))
      case Add(Param(src), dst) => Add(paramAddress(src), dst)
      case Sub(Param(src), Param(dst)) => Sub(paramAddress(src), paramAddress(dst))
      case Sub(src, Param(dst)) => Sub(src, paramAddress(dst))
      case Sub(Param(src), dst) => Sub(paramAddress(src), dst)
      case Mul(Param(src), Param(dst)) => Mul(paramAddress(src), paramAddress(dst))
      case Mul(src, Param(dst)) => Mul(src, paramAddress(dst))
      case Mul(Param(src), dst) => Mul(paramAddress(src), dst)
      case Div(Param(dst)) => Div(paramAddress(dst))
      case Shl(Param(src), Param(dst)) => Shl(paramAddress(src), paramAddress(dst))
      case Shl(src, Param(dst)) => Shl(src, paramAddress(dst))
      case Shl(Param(src), dst) => Shl(paramAddress(src), dst)
      case Shr(Param(src), Param(dst)) => Shr(paramAddress(src), paramAddress(dst))
      case Shr(src, Param(dst)) => Shr(src, paramAddress(dst))
      case Shr(Param(src), dst) => Shr(paramAddress(src), dst)
      case Mov(Param(src), Param(dst)) => Mov(paramAddress(src), paramAddress(dst))
      case Mov(src, Param(dst)) => Mov(src, paramAddress(dst))
      case Mov(Param(src), dst) => Mov(paramAddress(src), dst)
      case And(Param(src), Param(dst)) => And(paramAddress(src), paramAddress(dst))
      case And(src, Param(dst)) => And(src, paramAddress(dst))
      case And(Param(src), dst) => And(paramAddress(src), dst)
      case Xor(Param(src), Param(dst)) => Xor(paramAddress(src), paramAddress(dst))
      case Xor(src, Param(dst)) => Xor(src, paramAddress(dst))
      case Xor(Param(src), dst) => Xor(paramAddress(src), dst)
      case Or(Param(src), Param(dst)) => Or(paramAddress(src), paramAddress(dst))
      case Or(src, Param(dst)) => Or(src, paramAddress(dst))
      case Or(Param(src), dst) => Or(paramAddress(src), dst)
      case Cmp(Param(r1), Param(r2)) => Cmp(paramAddress(r1), paramAddress(r2))
      case Cmp(r1, Param(r2)) => Cmp(r1, paramAddress(r2))
      case Cmp(Param(r1), r2) => Cmp(paramAddress(r1), r2)
      case _ => stm
    })
  }

  def regalloc(root: Root): Root = {
    Root(
      for (
        proc <- root.procs
      ) yield {
        val proc2 = allocateArgs(proc)
        val proc3 = allocateParams(proc2)

        val live = liveness(proc3)
        val graph = inference(live)
        val colors = coloring(graph, registerArray)
        val end = applyAllocation(proc3, colors)
        Proc(end.location, wrapPrologueAndEpilogue(
          callToArgNum.max._2,
          Map.empty,
          proc.location, end.insns))
      }
    )
  }
}
