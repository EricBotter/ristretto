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

  def liveness(proc: Proc): List[Set[String]] = {
    var live = new ListBuffer[Set[String]]
    live += Set.empty
    var changed = true
    while (changed) {
      changed = false
      for (stm <- proc.insns.reverse) {
        var current = live.last
        current = stm match {
          //          case Push(RegOrImm(r)) => current + r.toString
          //          case Pop1(RegOrImm(dst)) => current - dst.toString
          //          case Add(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Sub(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Mul(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Div(RegOrImm(dst)) => current - dst.toString
          //          case Shl(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Shr(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case And(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Xor(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Or(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Mov(RegOrImm(src), RegOrImm(dst)) => current - dst.toString + src.toString
          //          case Cmp(RegOrImm(r1), RegOrImm(r2)) => current + r1.toString + r2.toString
          //          case Call(RegOrImm(fun)) => current //TODO

          //          case Push(RegOrImm(r)) => current
          //          case Pop1(RegOrImm(dst)) => current
          //          case Add(RegOrImm(src), RegOrImm(dst)) => current
          //          case Sub(RegOrImm(src), RegOrImm(dst)) => current
          //          case Mul(RegOrImm(src), RegOrImm(dst)) => current
          //          case Div(RegOrImm(dst)) => current
          //          case Shl(RegOrImm(src), RegOrImm(dst)) => current
          //          case Shr(RegOrImm(src), RegOrImm(dst)) => current
          //          case And(RegOrImm(src), RegOrImm(dst)) => current
          //          case Xor(RegOrImm(src), RegOrImm(dst)) => current
          //          case Or(RegOrImm(src), RegOrImm(dst)) => current
          //          case Mov(RegOrImm(src), RegOrImm(dst)) => current
          //          case Cmp(RegOrImm(r1), RegOrImm(r2)) => current
          //          case Call(RegOrImm(fun)) => current
          //
          //          case Add(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Sub(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Mul(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Shl(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Shr(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case And(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Xor(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Or(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Mov(RegOrImm(src), dst) => current - getPseudo(dst)
          //          case Cmp(RegOrImm(r1), r2) => current + getPseudo(r2)
          //
          //          case Add(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Sub(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Mul(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Shl(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Shr(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case And(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Xor(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Or(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Mov(src, RegOrImm(dst)) => current + getPseudo(src)
          //          case Cmp(r1, RegOrImm(r2)) => current + getPseudo(r1)

          case Push(src) => current + getPseudo(src)
          case Pop1(dst) => current - getPseudo(dst)
          case Add(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Sub(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Mul(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Div(dst) => current - getPseudo(dst)
          case Shl(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Shr(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Mov(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case And(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Xor(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Or(src, dst) => current - getPseudo(dst) + getPseudo(src)
          case Cmp(r1, r2) => current + getPseudo(r1) + getPseudo(r2)
          case Jmp(label) => current
          case JE(label) => current
          case JG(label) => current
          case JL(label) => current
          case JGE(label) => current
          case JLE(label) => current
          case JNE(label) => current
          case Call(fun) => current // TODO
          case Ret() => current
          case Label(location) => current
          case CommentInsn(_) => current
        }
        live += current
        // println(stm)
      } // TODO - fix jumps and iterate again
    }
    live.toList.reverse
  }

  def inference(live: List[Set[String]]): Map[String, Set[String]] = {
    val out: mutable.Map[String, Set[String]] = mutable.Map.empty
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

  def colorsToRegisters: Array[AsmSyntax.Operand] = Array(
    AX(), BX(), CX(), DX(), R8(), R9(), R10(), R11(), R12(), R13(), R14(), R15()
  )

  def coloring(graph: Map[String, Set[String]], colors: Int): Map[String, AsmSyntax.Operand] = {
    if (graph.isEmpty)
      return Map.empty
    if (colors == 0 && graph != Map.empty)
      throw new Exception // TODO - spilling
    val max_deg: String = graph.maxBy(_._2.size)._1
    val newgraph = for ((k, v) <- graph - max_deg) yield (k, v - max_deg)
    coloring(newgraph, colors - 1) + (max_deg -> colorsToRegisters(colors - 1))
  }

  def applyAllocation(proc: Proc, coloring: Map[String, AsmSyntax.Operand]): Proc = {
    Proc(proc.location, for (stm <- proc.insns) yield stm match {
      //      case Push(RegOrImm(r)) => Push(r)
      //      case Pop1(RegOrImm(dst)) => Pop1(dst)
      //      case Add(RegOrImm(src), RegOrImm(dst)) => Add(src, dst)
      //      case Sub(RegOrImm(src), RegOrImm(dst)) => Sub(src, dst)
      //      case Mul(RegOrImm(src), RegOrImm(dst)) => Mul(src, dst)
      //      case Div(RegOrImm(dst)) => Div(dst)
      //      case Shl(RegOrImm(src), RegOrImm(dst)) => Shl(src, dst)
      //      case Shr(RegOrImm(src), RegOrImm(dst)) => Shr(src, dst)
      //      case And(RegOrImm(src), RegOrImm(dst)) => And(src, dst)
      //      case Xor(RegOrImm(src), RegOrImm(dst)) => Xor(src, dst)
      //      case Or(RegOrImm(src), RegOrImm(dst)) => Or(src, dst)
      //      case Mov(RegOrImm(src), RegOrImm(dst)) => Mov(src, dst)
      //      case Cmp(RegOrImm(r1), RegOrImm(r2)) => Cmp(r1, r2)
      //      case Call(RegOrImm(fun)) => Call(fun)
      //
      //      case Add(RegOrImm(src), dst) => Add(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Sub(RegOrImm(src), dst) => Sub(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Mul(RegOrImm(src), dst) => Mul(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Shl(RegOrImm(src), dst) => Shl(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Shr(RegOrImm(src), dst) => Shr(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case And(RegOrImm(src), dst) => And(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Xor(RegOrImm(src), dst) => Xor(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Or(RegOrImm(src), dst) => Or(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Mov(RegOrImm(src), dst) => Mov(src, coloring.getOrElse(getPseudo(dst), dst))
      //      case Cmp(RegOrImm(r1), r2) => Cmp(r1, coloring.getOrElse(getPseudo(r2), r2))
      //
      //      case Add(src, RegOrImm(dst)) => Add(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Sub(src, RegOrImm(dst)) => Sub(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Mul(src, RegOrImm(dst)) => Mul(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Shl(src, RegOrImm(dst)) => Shl(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Shr(src, RegOrImm(dst)) => Shr(coloring.getOrElse(getPseudo(src), src), dst)
      //      case And(src, RegOrImm(dst)) => And(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Xor(src, RegOrImm(dst)) => Xor(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Or(src, RegOrImm(dst)) => Or(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Mov(src, RegOrImm(dst)) => Mov(coloring.getOrElse(getPseudo(src), src), dst)
      //      case Cmp(r1, RegOrImm(r2)) => Cmp(coloring.getOrElse(getPseudo(r1), r1), r2)

      case Push(src) =>
        Push(coloring.getOrElse(getPseudo(src), src))
      case Pop1(dst) =>
        Pop1(coloring.getOrElse(getPseudo(dst), dst))
      case Add(src, dst) =>
        Add(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Sub(src, dst) =>
        Sub(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Mul(src, dst) =>
        Mul(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Div(dst) =>
        Div(coloring.getOrElse(getPseudo(dst), dst))
      case Shl(src, dst) =>
        Shl(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Shr(src, dst) =>
        Shr(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Mov(src, dst) =>
        Mov(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case And(src, dst) =>
        And(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Xor(src, dst) =>
        Xor(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Or(src, dst) =>
        Or(coloring.getOrElse(getPseudo(src), src),
          coloring.getOrElse(getPseudo(dst), dst))
      case Cmp(r1, r2) =>
        Cmp(coloring.getOrElse(getPseudo(r1), r1),
          coloring.getOrElse(getPseudo(r2), r2))
      case x@_ => x
    })
  }

  def regalloc(root: Root): Root = {
    Root(
      for (
        proc <- root.procs
      ) yield {
        val live = liveness(proc)
        val graph = inference(live)
        val colors = coloring(graph, colorsToRegisters.length)
        applyAllocation(proc, colors)
      }
    )
  }
}
