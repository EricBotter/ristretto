package ristretto.asm

import ristretto.frontend.Typer

// Perform register allocation on ASM ASTs.
// - Replace all Pseudo registers with spills (slow!)
// - Replace all Arg variables with parameter registers or stack accesses
// - Replace all Param variables with real registers. Assumes these only appear at the beginning.
// - Add the prologue and epilogue, dumping the parameters to the stack.
object SuboptimalRegisterAllocation {

  import ristretto.asm.AsmSyntax._
  import ristretto.main.{Compiler => Errors}

  type TempName = String
  type OffsetMap = Map[TempName, Operand]

  val WORDSIZE = 8

  def wrapPrologueAndEpilogue(maxArgs: Int, map: OffsetMap, label: String, insns: List[Insn]): List[Insn] = {
    // On MacOS, we need to align the stack on 16-byte boundaries
    val unalignedSize = frameSize(map) + maxArgs * WORDSIZE
    // size: 0 -> 0 + 0 = 0
    // size: 4 -> 4 + 12 = 16
    // size: 8 -> 8 + 8 = 16
    // size: 12 -> 12 + 4 = 16
    // size: 16 -> 16 + 0 = 16
    // size: 20 -> 20 + 12 = 32
    // ...
    val size = unalignedSize + ((16 - unalignedSize) % 16)
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

  def regalloc(t: Root): Root = t match {
    case Root(procs) =>
      Root(procs map {
        case proc@Proc(label, insns) =>
          val map = buildOffsetMap(insns)
          val maxArgs = (0 :: collectArgs(insns).map(_ + 1)).max
          Proc(label, wrapPrologueAndEpilogue(maxArgs, map, label, regalloc(map, insns)))
      })
  }

  def frameSize(map: OffsetMap): Int = {
    WORDSIZE * map.size
  }

  // This is x86-64 SysV ABI-specific
  // This first 6 arguments are passed in registers.
  // The rest on the stack.
  def argAddress(i: Int, f: String) = Typer.functions(f).args(i) match {
    case Typer.FloatType() =>
      Typer.functions(f).args.splitAt(i)._1.count(_.isInstanceOf[Typer.FloatType]) match {
        case 0 => XMM0()
        case 1 => XMM1()
        case 2 => XMM2()
        case 3 => XMM3()
        case 4 => XMM4()
        case 5 => XMM5()
        case 6 => XMM6()
        case 7 => XMM7()
        case n =>
          val x = Typer.functions(f).args.splitAt(i)._1.count(!_.isInstanceOf[Typer.FloatType])
          if (x < 6)
            Address(WORDSIZE * (n - 8), SP())
          else
            Address(WORDSIZE * ((x - 6) + n - 8), SP())
      }
    case _ =>
      Typer.functions(f).args.splitAt(i)._1.count(!_.isInstanceOf[Typer.FloatType]) match {
        case 0 => DI()
        case 1 => SI()
        case 2 => DX()
        case 3 => CX()
        case 4 => R8()
        case 5 => R9()
        case n =>
          val x = Typer.functions(f).args.splitAt(i)._1.count(_.isInstanceOf[Typer.FloatType])
          if (x < 8)
            Address(WORDSIZE * (n - 6), SP())
          else
            Address(WORDSIZE * ((x - 8) + n - 6), SP())
      }

  }

  def paramAddress(i: Int, f: String) = Typer.functions(f).args(i) match {
    case Typer.FloatType() =>
      Typer.functions(f).args.splitAt(i)._1.count(_.isInstanceOf[Typer.FloatType]) match {
        case 0 => XMM0()
        case 1 => XMM1()
        case 2 => XMM2()
        case 3 => XMM3()
        case 4 => XMM4()
        case 5 => XMM5()
        case 6 => XMM6()
        case 7 => XMM7()
        case n =>
          val x = Typer.functions(f).args.splitAt(i)._1.count(!_.isInstanceOf[Typer.FloatType])
          if (x < 6)
            Address(WORDSIZE * (n - 8 + 2), BP())
          else
            Address(WORDSIZE * ((x - 6) + n - 8 + 2), BP())
      }
    case _ =>
      Typer.functions(f).args.splitAt(i)._1.count(!_.isInstanceOf[Typer.FloatType]) match {
        case 0 => DI()
        case 1 => SI()
        case 2 => DX()
        case 3 => CX()
        case 4 => R8()
        case 5 => R9()
        case n =>
          val x = Typer.functions(f).args.splitAt(i)._1.count(_.isInstanceOf[Typer.FloatType])
          if (x < 8)
            Address(WORDSIZE * (n - 6 + 2), BP())
          else
            Address(WORDSIZE * ((x - 8) + n - 6 + 2), BP())
      }

  }

  def buildOffsetMap(insns: List[Insn]): OffsetMap = {
    // Pseudo registers are at a negative offset from the base pointer
    val localMap = collectPseudos(insns).distinct.zipWithIndex collect {
      case (x, i) =>
        // 0 -> -8, 1 -> -16, 2 -> -24, ...
        (x, Address(WORDSIZE * (-i - 1), BP()))
    }

    localMap.toMap
  }

  def collectPseudos(insns: List[Insn]): List[TempName] = {
    for {
      insn <- insns
      x <- collectPseudos(insn)
    } yield x
  }

  def collectPseudos(insn: Insn): List[TempName] = insn match {
    case Push(src) => collectPseudos(src)
    case Pop1(dst) => collectPseudos(dst)
    case Add(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Sub(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Mul(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Div(dst) => collectPseudos(dst)
    case AddF(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case SubF(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case MulF(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case DivF(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Shl(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Shr(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Mov(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case MovF(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case And(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Xor(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Or(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case I2F(src, dst) => collectPseudos(src) ++ collectPseudos(dst)
    case Cmp(r1, r2) => collectPseudos(r1) ++ collectPseudos(r2)
    case CmpF(r1, r2) => collectPseudos(r1) ++ collectPseudos(r2)
    case Jmp(label) => Nil
    case JE(label) => Nil
    case JG(label) => Nil
    case JL(label) => Nil
    case JGE(label) => Nil
    case JLE(label) => Nil
    case JNE(label) => Nil
    case JA(label) => Nil
    case JAE(label) => Nil
    case JB(label) => Nil
    case JBE(label) => Nil
    case Call(fun) => collectPseudos(fun)
    case Ret() => Nil
    case Label(location) => Nil
    case CommentInsn(_) => Nil
  }

  def collectPseudos(e: Operand): List[TempName] = e match {
    case Pseudo(t) => t :: Nil
    case Address(offset, base) => collectPseudos(base)
    case _ => Nil
  }

  def collectArgs(insns: List[Insn]): List[Int] = {
    for {
      insn <- insns
      x <- collectArgs(insn)
    } yield x
  }

  def collectArgs(insn: Insn): List[Int] = insn match {
    case Push(src) => collectArgs(src)
    case Pop1(dst) => collectArgs(dst)
    case Add(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Sub(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Mul(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Div(dst) => collectArgs(dst)
    case AddF(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case SubF(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case MulF(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case DivF(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Shl(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Shr(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Mov(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case MovF(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case And(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Xor(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Or(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case I2F(src, dst) => collectArgs(src) ++ collectArgs(dst)
    case Cmp(r1, r2) => collectArgs(r1) ++ collectArgs(r2)
    case CmpF(r1, r2) => collectArgs(r1) ++ collectArgs(r2)
    case Jmp(label) => Nil
    case JE(label) => Nil
    case JG(label) => Nil
    case JL(label) => Nil
    case JGE(label) => Nil
    case JLE(label) => Nil
    case JNE(label) => Nil
    case JA(label) => Nil
    case JAE(label) => Nil
    case JB(label) => Nil
    case JBE(label) => Nil
    case Call(fun) => collectArgs(fun)
    case Ret() => Nil
    case Label(location) => Nil
    case CommentInsn(_) => Nil
  }

  def collectArgs(e: Operand): List[Int] = e match {
    case Arg(i, _) => i :: Nil
    case Address(offset, base) => collectArgs(base)
    case _ => Nil
  }

  def regalloc(map: OffsetMap, insns: List[Insn]): List[Insn] = {
    for {
      insn <- insns
      insn2 <- regalloc(map, insn)
    } yield insn2
  }

  object Reg {
    def unapply(op: Operand): Option[Operand] = op match {
      case r@AX() => Some(r)
      case r@BX() => Some(r)
      case r@CX() => Some(r)
      case r@DX() => Some(r)
      case r@DI() => Some(r)
      case r@SI() => Some(r)
      case r@SP() => Some(r)
      case r@BP() => Some(r)
      case r@R8() => Some(r)
      case r@R9() => Some(r)
      case r@R10() => Some(r)
      case r@R11() => Some(r)
      case r@R12() => Some(r)
      case r@R13() => Some(r)
      case r@R14() => Some(r)
      case r@R15() => Some(r)
      case _ => None
    }
  }

  object RegF {
    def unapply(op: Operand): Option[Operand] = op match {
      case r@XMM1() => Some(r)
      case r@XMM2() => Some(r)
      case r@XMM3() => Some(r)
      case r@XMM4() => Some(r)
      case r@XMM5() => Some(r)
      case r@XMM6() => Some(r)
      case r@XMM7() => Some(r)
      case r@XMM8() => Some(r)
      case r@XMM9() => Some(r)
      case r@XMM10() => Some(r)
      case r@XMM11() => Some(r)
      case r@XMM12() => Some(r)
      case r@XMM13() => Some(r)
      case r@XMM14() => Some(r)
      case r@XMM15() => Some(r)
      case _ => None
    }
  }

  object RegOrImm {
    def unapply(op: Operand): Option[Operand] = op match {
      case Reg(r) => Some(r)
      case RegF(r) => Some(r)
      case op@Immediate(_) => Some(op)
      case _ => None
    }
  }

  // We use R14..R15 and XMM6..XMM7 as our temporary registers.
  // We should not use the argument passing registers here.
  def regalloc(map: OffsetMap, insn: Insn): List[Insn] = insn match {
    case Push(RegOrImm(r)) => Push(r) :: Nil
    case Pop1(RegOrImm(dst)) => Pop1(dst) :: Nil
    case Add(RegOrImm(src), RegOrImm(dst)) => Add(src, dst) :: Nil
    case Sub(RegOrImm(src), RegOrImm(dst)) => Sub(src, dst) :: Nil
    case Mul(RegOrImm(src), RegOrImm(dst)) => Mul(src, dst) :: Nil
    case Div(RegOrImm(dst)) => Div(dst) :: Nil
    case Shl(RegOrImm(src), RegOrImm(dst)) => Shl(src, dst) :: Nil
    case Shr(RegOrImm(src), RegOrImm(dst)) => Shr(src, dst) :: Nil
    case And(RegOrImm(src), RegOrImm(dst)) => And(src, dst) :: Nil
    case Xor(RegOrImm(src), RegOrImm(dst)) => Xor(src, dst) :: Nil
    case Or(RegOrImm(src), RegOrImm(dst)) => Or(src, dst) :: Nil
    case Mov(RegOrImm(src), RegOrImm(dst)) => Mov(src, dst) :: Nil
    case Cmp(RegOrImm(r1), RegOrImm(r2)) => Cmp(r1, r2) :: Nil
    case Call(RegOrImm(fun)) => Call(fun) :: Nil

    case AddF(RegOrImm(src), RegOrImm(dst)) => AddF(src, dst) :: Nil
    case SubF(RegOrImm(src), RegOrImm(dst)) => SubF(src, dst) :: Nil
    case MulF(RegOrImm(src), RegOrImm(dst)) => MulF(src, dst) :: Nil
    case DivF(RegOrImm(src), RegOrImm(dst)) => DivF(src, dst) :: Nil
    case MovF(RegOrImm(src), RegOrImm(dst)) => MovF(src, dst) :: Nil
    case CmpF(RegOrImm(r1), RegOrImm(r2)) => CmpF(r1, r2) :: Nil
    case I2F(RegOrImm(src), RegOrImm(dst)) => I2F(src, dst) :: Nil

    case Push(src) => load(map, src, R14()) :+ Push(R14())
    case Pop1(dst) => Pop1(R14()) :: store(map, R14(), dst)
    case Add(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Add(R14(), R15()) :: store(map, R15(), dst))
    case Sub(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Sub(R14(), R15()) :: store(map, R15(), dst))
    case Mul(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Mul(R14(), R15()) :: store(map, R15(), dst))
    case Div(dst) => load(map, dst, R14()) ++ (Div(R14()) :: store(map, R14(), dst))
    case Shl(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Shl(R14(), R15()) :: store(map, R15(), dst))
    case Shr(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Shr(R14(), R15()) :: store(map, R15(), dst))
    case And(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (And(R14(), R15()) :: store(map, R15(), dst))
    case Xor(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Xor(R14(), R15()) :: store(map, R15(), dst))
    case Or(src, dst) => load(map, src, R14()) ++ load(map, dst, R15()) ++ (Or(R14(), R15()) :: store(map, R15(), dst))
    case Mov(src, dst) => load(map, src, R14()) ++ store(map, R14(), dst)
    case Cmp(r1, r2) => load(map, r1, R14()) ++ load(map, r2, R15()) :+ Cmp(R14(), R15())
    case Call(Name(n)) => Call(Name(n)) :: Nil
    case Call(fun) => load(map, fun, R14()) :+ Call(R14())

    case AddF(src, dst) => loadf(map, src, XMM7()) ++ loadf(map, dst, XMM6()) ++ (AddF(XMM7(), XMM6()) :: storef(map, XMM6(), dst))
    case SubF(src, dst) => loadf(map, src, XMM7()) ++ loadf(map, dst, XMM6()) ++ (SubF(XMM7(), XMM6()) :: storef(map, XMM6(), dst))
    case MulF(src, dst) => loadf(map, src, XMM7()) ++ loadf(map, dst, XMM6()) ++ (MulF(XMM7(), XMM6()) :: storef(map, XMM6(), dst))
    case DivF(src, dst) => loadf(map, src, XMM7()) ++ loadf(map, dst, XMM6()) ++ (DivF(XMM7(), XMM6()) :: storef(map, XMM6(), dst))
    case MovF(src, dst) => loadf(map, src, XMM7()) ++ storef(map, XMM7(), dst)
    case CmpF(r1, r2) => loadf(map, r1, XMM7()) ++ loadf(map, r2, XMM6()) :+ CmpF(XMM7(), XMM6())
    case I2F(src, dst) => load(map, src, R14()) ++ (I2F(R14(), XMM7()) :: storef(map, XMM7(), dst))

    // No other instruction uses registers.
    case insn => insn :: Nil
  }

  def rewrite(map: OffsetMap, op: Operand): Operand = op match {
    case Arg(i, f) =>
      argAddress(i, f)
    case Param(i, f) =>
      paramAddress(i, f)
    case Pseudo(n) =>
      lookup(n)(map)
    case op =>
      op
  }

  def isAddress(op: Operand) = op match {
    case Address(_, _) => true
    case _ => false
  }

  // Use R12 and R13 as a temporary registers. We can't use the same registers as in regalloc above.
  // dst must be a Reg
  def load(map: OffsetMap, src: Operand, dst: Operand): List[Insn] = {
    dst match {
      case Reg(r) =>
      case _ => Errors.fatalError(s"cannot load from $src into non-register $dst")
    }
    src match {
      case Address(base, Pseudo(n)) =>
        load(map, Pseudo(n), R13()) :+ Mov(Address(base, R13()), dst)
      case Address(base, Arg(i, f)) =>
        Errors.fatalError("cannot compute address from an argument pseudo-variable")
      case Address(base, Param(i, f)) =>
        Errors.fatalError("cannot compute address from a parameter pseudo-variable")
      case src =>
        val s = rewrite(map, src)
        Mov(s, dst) :: Nil
    }
  }

  def loadf(map: OffsetMap, src: Operand, dst: Operand): List[Insn] = {
    dst match {
      case RegF(r) =>
      case _ => Errors.fatalError(s"cannot load from $src into non-register $dst")
    }
    src match {
      case Address(base, Pseudo(n)) =>
        load(map, Pseudo(n), R13()) :+ MovF(Address(base, R13()), dst)
      case Address(base, Arg(i, f)) =>
        Errors.fatalError("cannot compute address from an argument pseudo-variable")
      case Address(base, Param(i, f)) =>
        Errors.fatalError("cannot compute address from a parameter pseudo-variable")
      case src =>
        val s = rewrite(map, src)
        MovF(s, dst) :: Nil
    }
  }

  // src must be a Reg
  def store(map: OffsetMap, src: Operand, dst: Operand): List[Insn] = {
    src match {
      case Reg(r) =>
      case _ => Errors.fatalError(s"cannot store from $src into non-register $dst")
    }
    dst match {
      case Address(base, Pseudo(n)) =>
        load(map, Pseudo(n), R13()) :+ Mov(src, Address(base, R13()))
      case Address(base, Arg(i, f)) =>
        Errors.fatalError("cannot compute address from an argument pseudo-variable")
      case Address(base, Param(i, f)) =>
        Errors.fatalError("cannot compute address from a parameter pseudo-variable")
      case dst =>
        val d = rewrite(map, dst)
        Mov(src, d) :: Nil
    }
  }

  // src must be a Reg
  def storef(map: OffsetMap, src: Operand, dst: Operand): List[Insn] = {
    src match {
      case RegF(r) =>
      case _ => Errors.fatalError(s"cannot store from $src into non-register $dst")
    }
    dst match {
      case Address(base, Pseudo(n)) =>
        load(map, Pseudo(n), R13()) :+ MovF(src, Address(base, R13()))
      case Address(base, Arg(i, f)) =>
        Errors.fatalError("cannot compute address from an argument pseudo-variable")
      case Address(base, Param(i, f)) =>
        Errors.fatalError("cannot compute address from a parameter pseudo-variable")
      case dst =>
        val d = rewrite(map, dst)
        MovF(src, d) :: Nil
    }
  }

  def lookup(t: TempName)(map: OffsetMap): Operand = {
    map.get(t) match {
      case Some(e) => e
      case None =>
        Errors.fatalError(s"could not find stack location of temporary $t")
    }
  }
}
