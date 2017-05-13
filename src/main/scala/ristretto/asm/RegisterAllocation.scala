package ristretto.asm

import ristretto.asm.AsmSyntax._
import ristretto.asm.SuboptimalRegisterAllocation.RegOrImm

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object RegisterAllocation {

  def getPseudo(o: Operand): List[String] = o match {
    case Pseudo(t) => t :: Nil
    case Address(offset, base) => getPseudo(base)
    case _ => Nil
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

          case Push(RegOrImm(r)) => current
          case Pop1(RegOrImm(dst)) => current
          case Add(RegOrImm(src), RegOrImm(dst)) => current
          case Sub(RegOrImm(src), RegOrImm(dst)) => current
          case Mul(RegOrImm(src), RegOrImm(dst)) => current
          case Div(RegOrImm(dst)) => current
          case Shl(RegOrImm(src), RegOrImm(dst)) => current
          case Shr(RegOrImm(src), RegOrImm(dst)) => current
          case And(RegOrImm(src), RegOrImm(dst)) => current
          case Xor(RegOrImm(src), RegOrImm(dst)) => current
          case Or(RegOrImm(src), RegOrImm(dst)) => current
          case Mov(RegOrImm(src), RegOrImm(dst)) => current
          case Cmp(RegOrImm(r1), RegOrImm(r2)) => current
          case Call(RegOrImm(fun)) => current

          case Push(src) => current ++ getPseudo(src)
          case Pop1(dst) => current -- getPseudo(dst)
          case Add(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Sub(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Mul(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Div(dst) => current -- getPseudo(dst)
          case Shl(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Shr(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Mov(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case And(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Xor(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Or(src, dst) => current -- getPseudo(dst) ++ getPseudo(src)
          case Cmp(r1, r2) => current ++ getPseudo(r1) ++ getPseudo(r2)
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

  def coloring(graph: Map[String, Set[String]], colors: Int): Map[String, Int] = {
    if (graph.isEmpty)
      return Map.empty
    if (colors == 0 && graph != Map.empty)
      throw new Exception
    val max_deg: String = graph.maxBy(_._2.size)._1
    var newgraph = for ((k,v) <- graph - max_deg) yield (k,v - max_deg)
    coloring(newgraph, colors - 1) + (max_deg -> colors)
  }

  def explore(root: Root): Unit = {
    for (
      proc <- root.procs
    ) {
      var live = liveness(proc)
      var graph = inference(live)
      println(coloring(graph, 3000))
    }
  }
}
