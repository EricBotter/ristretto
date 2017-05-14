package ristretto.asm

import ristretto.asm.AsmSyntax._

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object RegisterAllocation {

  val WORDSIZE = 8

  def getPseudo(o: Operand): String = o match {
    case Pseudo(t) => t
    case Address(offset, base) => getPseudo(base)
    case _ => null
  }

  var callToArgs: Map[String, Int] = Map()

  def liveness(proc: Proc): List[Set[AsmSyntax.Operand]] = {
    callToArgs = Map()
    var args = 0
    for (stm <- proc.insns) stm match {
      case Mov(_, Arg(i)) => args = math.max(args, i)
      case Call(fun) =>
        callToArgs += (fun.toString -> args)
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
          case Push(src@(Pseudo(_) | Arg(_))) => current + src
          case Pop1(dst@(Pseudo(_) | Arg(_))) => current - dst
          case Add(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Add(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Add(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Sub(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Sub(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Sub(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Mul(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Mul(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Mul(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Div(dst@(Pseudo(_) | Arg(_))) => current - dst
          case Shl(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Shl(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Shl(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Shr(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Shr(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Shr(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Mov(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Mov(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Mov(src@(Pseudo(_) | Arg(_)), _) => current + src
          case And(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case And(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case And(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Xor(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Xor(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Xor(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Or(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => current - dst + src
          case Or(_, dst@(Pseudo(_) | Arg(_))) => current - dst
          case Or(src@(Pseudo(_) | Arg(_)), _) => current + src
          case Cmp(r1@(Pseudo(_) | Arg(_)), r2@(Pseudo(_) | Arg(_))) => current + r2 + r1
          case Cmp(_, r2@(Pseudo(_) | Arg(_))) => current + r2
          case Cmp(r1@(Pseudo(_) | Arg(_)), _) => current + r1

          case Jmp(label) => current
          case JE(label) => current
          case JG(label) => current
          case JL(label) => current
          case JGE(label) => current
          case JLE(label) => current
          case JNE(label) => current
          case Call(fun) =>
            current ++ (for (i <- 0 to callToArgs(fun.toString)) yield Arg(i))
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
    AX(), BX(), CX(), DX(), R8(), R9(), R10(), R11(), R12(), R13(), R14(), R15()
  )

  def argAddress(i: Int): Operand = i match {
    case 0 => DI()
    case 1 => SI()
    case 2 => DX()
    case 3 => CX()
    case 4 => R8()
    case 5 => R9()
    case _ => Address(WORDSIZE * (i - 6), SP()) // 6 -> 0(sp), 7 -> 8(sp), 8 -> 16(sp), ...
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

  def coloring(graph: Map[AsmSyntax.Operand, Set[AsmSyntax.Operand]],
               colors: Array[AsmSyntax.Operand])
  : Map[AsmSyntax.Operand, AsmSyntax.Operand] = {
    if (graph.isEmpty)
      return Map.empty
    if (colors.length == 0 && graph != Map.empty)
      throw new Exception // TODO - spilling
    val max_deg: AsmSyntax.Operand = graph.maxBy(_._2.size)._1
    val newgraph = for ((k, v) <- graph - max_deg) yield (k, v - max_deg)
    val chosen = colors.last
    coloring(newgraph, colors.dropRight(1)) + (max_deg -> chosen)
  }

  def applyAllocation(proc: Proc, coloring: Map[AsmSyntax.Operand, AsmSyntax.Operand]): Proc = {
    Proc(proc.location, for (stm <- proc.insns) yield {
//      println(stm)
      try {
        stm match {
          case Push(src@(Pseudo(_) | Arg(_))) => Push(coloring(src))
          case Pop1(dst@(Pseudo(_) | Arg(_))) => Pop1(coloring(dst))
          case Add(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Add(coloring(src), coloring(dst))
          case Add(src, dst@(Pseudo(_) | Arg(_))) => Add(src, coloring(dst))
          case Add(src@(Pseudo(_) | Arg(_)), dst) => Add(coloring(src), dst)
          case Sub(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Sub(coloring(src), coloring(dst))
          case Sub(src, dst@(Pseudo(_) | Arg(_))) => Sub(src, coloring(dst))
          case Sub(src@(Pseudo(_) | Arg(_)), dst) => Sub(coloring(src), dst)
          case Mul(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Mul(coloring(src), coloring(dst))
          case Mul(src, dst@(Pseudo(_) | Arg(_))) => Mul(src, coloring(dst))
          case Mul(src@(Pseudo(_) | Arg(_)), dst) => Mul(coloring(src), dst)
          case Div(dst@(Pseudo(_) | Arg(_))) => Div(coloring(dst))
          case Shl(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Shl(coloring(src), coloring(dst))
          case Shl(src, dst@(Pseudo(_) | Arg(_))) => Shl(src, coloring(dst))
          case Shl(src@(Pseudo(_) | Arg(_)), dst) => Shl(coloring(src), dst)
          case Shr(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Shr(coloring(src), coloring(dst))
          case Shr(src, dst@(Pseudo(_) | Arg(_))) => Shr(src, coloring(dst))
          case Shr(src@(Pseudo(_) | Arg(_)), dst) => Shr(coloring(src), dst)
          case Mov(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Mov(coloring(src), coloring(dst))
          case Mov(src, dst@(Pseudo(_) | Arg(_))) => Mov(src, coloring(dst))
          case Mov(src@(Pseudo(_) | Arg(_)), dst) => Mov(coloring(src), dst)
          case And(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => And(coloring(src), coloring(dst))
          case And(src, dst@(Pseudo(_) | Arg(_))) => And(src, coloring(dst))
          case And(src@(Pseudo(_) | Arg(_)), dst) => And(coloring(src), dst)
          case Xor(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Xor(coloring(src), coloring(dst))
          case Xor(src, dst@(Pseudo(_) | Arg(_))) => Xor(src, coloring(dst))
          case Xor(src@(Pseudo(_) | Arg(_)), dst) => Xor(coloring(src), dst)
          case Or(src@(Pseudo(_) | Arg(_)), dst@(Pseudo(_) | Arg(_))) => Or(coloring(src), coloring(dst))
          case Or(src, dst@(Pseudo(_) | Arg(_))) => Or(src, coloring(dst))
          case Or(src@(Pseudo(_) | Arg(_)), dst) => Or(coloring(src), dst)
          case Cmp(r1@(Pseudo(_) | Arg(_)), r2@(Pseudo(_) | Arg(_))) => Cmp(coloring(r1), coloring(r2))
          case Cmp(r1, r2@(Pseudo(_) | Arg(_))) => Cmp(r1, coloring(r2))
          case Cmp(r1@(Pseudo(_) | Arg(_)), r2) => Cmp(coloring(r1), r2)

          case x => x
        }
      } catch {
        case _: NoSuchElementException => CommentInsn("Instruction removed LUL")
      }
    })
  }

  def regalloc(root: Root): Root = {
    Root(
      for (
        proc <- root.procs
      ) yield {
        val live = liveness(proc)
        val graph = inference(live)
        val colors = coloring(graph, registerArray)
        applyAllocation(proc, colors)
      }
    )
  }
}
