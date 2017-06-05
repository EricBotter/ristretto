package ristretto.drip

import ristretto.drip.DripSyntax._

// Generate Drip from Ristretto ASTs
object PercGen {

  import ristretto.perc.{PercSyntax => P}
  import ristretto.drip.{DripSyntax => D}
  import ristretto.main.{Compiler => Errors}

  type Label = String
  type Temp = String

  type TempName = String
  type Name = String

  def translate(t: D.Root): P.Root = t match {
    case D.Root(dprocs) =>
      val procs = dprocs map {
        case D.Proc(f, params, body) =>
          val t = newTemp()
          P.Proc(f, params.map {
            case x => x
          }, translate(body, t) :+ P.Ret(P.Temp(t)))
      }
      P.Root(procs)
  }

  def translate(s: D.Stm): List[P.Stm] = s match {
    case D.Nop() =>
      P.Nop() :: Nil

    case D.ErrorStm(n) =>
      P.ErrorStm(n) :: Nil

    case D.CJmp(e, tgt) =>
      val t = newTemp()
      translate(e, t) :+ P.CJmp(P.NE(), P.Temp(t), tgt)

    case D.Jmp(tgt) =>
      P.Jmp(tgt) :: Nil

    case D.Store(offset, address, value) =>
      val t1 = newTemp()
      val t2 = newTemp()
      translate(address, t1) ++ translate(value, t2) :+
        P.Store(P.Address(offset, P.Temp(t1)), P.Temp(t2))

    case D.StoreF(offset, address, value) =>
      val t1 = newTemp()
      val t2 = newTemp()
      translate(address, t1) ++ translate(value, t2) :+
        P.StoreF(P.Address(offset, P.Temp(t1)), P.Temp(t2))

    case D.Move(t, e) =>
      translate(e, t)

    case D.MoveF(t, e) =>
      translate(e, t) //FIXME

    case D.I2F(t, e) =>
      val t1 = newTemp()
      translate(e, t1) :+ P.I2F(t, P.Temp(t1))

    case D.LabelStm(l) =>
      P.LabelStm(l) :: Nil
  }

  // Translate the expression `e`, writing the result into temporary `t`
  def translate(e: D.Exp, t: TempName): List[P.Stm] = e match {
    case D.Begin(stms, e) =>
      val ps = stms flatMap { s => translate(s) }
      ps ++ translate(e, t)

    case D.Call(f, es) =>
      val temps = es.indices.map(i => newTemp())
      val stms = es.indices.map(i => translate(es(i), temps(i)))
      val regset = es.indices.map(i => P.SetArg(i, f.asInstanceOf[D.Global].label, P.Temp(temps(i))))
      stms.flatten.toList ++ regset :+
        P.Call(t, P.Global(f.asInstanceOf[D.Global].label))

    case D.Alloc(sz) =>
      val tsz = newTemp()
      translate(sz, tsz) :+
        P.SetArg(0, "ristretto_alloc", P.Temp(tsz)) :+
        P.Call(t, P.Global("ristretto_alloc"))

    case D.Load(offset, addr) =>
      val t1 = newTemp()
      translate(addr, t1) :+ P.Load(t, P.Address(offset, P.Temp(t1)))

    case D.LoadF(offset, addr) =>
      val t1 = newTemp()
      translate(addr, t1) :+ P.LoadF(t, P.Address(offset, P.Temp(t1)))

    case D.BinOp(op, e1, e2) =>
      val t1 = newTemp()
      val t2 = newTemp()
      val r1 = translate(e1, t1)
      val r2 = translate(e2, t2)
      val r3 = op match {
        case ADD() =>
          P.Bin(t, P.ADD(), P.Temp(t1), P.Temp(t2)) :: Nil
        case SUB() =>
          P.Bin(t, P.SUB(), P.Temp(t1), P.Temp(t2)) :: Nil
        case MUL() =>
          P.Bin(t, P.MUL(), P.Temp(t1), P.Temp(t2)) :: Nil
        case DIV() =>
          P.Bin(t, P.DIV(), P.Temp(t1), P.Temp(t2)) :: Nil
        case ADDF() =>
          P.Bin(t, P.ADDF(), P.Temp(t1), P.Temp(t2)) :: Nil
        case SUBF() =>
          P.Bin(t, P.SUBF(), P.Temp(t1), P.Temp(t2)) :: Nil
        case MULF() =>
          P.Bin(t, P.MULF(), P.Temp(t1), P.Temp(t2)) :: Nil
        case DIVF() =>
          P.Bin(t, P.DIVF(), P.Temp(t1), P.Temp(t2)) :: Nil
        case REM() =>
          P.Bin(t, P.REM(), P.Temp(t1), P.Temp(t2)) :: Nil
        case LT() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUB(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmp(P.LT(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case GT() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUB(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmp(P.GT(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case LE() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUB(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmp(P.LE(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case GE() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUB(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmp(P.GE(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case EQ() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUB(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmp(P.EQ(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case NE() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUB(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmp(P.NE(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case LTF() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUBF(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmpF(P.LTF(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case GTF() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUBF(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmpF(P.GTF(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case LEF() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUBF(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmpF(P.LEF(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case GEF() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUBF(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmpF(P.GEF(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case EQF() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUBF(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmpF(P.EQF(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
        case NEF() =>
          val tx = newTemp()
          val l1 = newLabel()
          List(
            P.Bin(tx, P.SUBF(), P.Temp(t1), P.Temp(t2)),
            P.Move(t, P.Lit(1)),
            P.CJmpF(P.NEF(), P.Temp(tx), l1),
            P.Move(t, P.Lit(0)),
            P.LabelStm(l1)
          )
      }
      r1 ++ r2 ++ r3

    case D.Temp(x) if x == t =>
      Nil

    case D.Temp(x) =>
      P.Move(t, P.Temp(x)) :: Nil

    case D.Lit(n) =>
      P.Move(t, P.Lit(n)) :: Nil

    case D.LitF(n) =>
      P.MoveF(t, P.LitF(n)) :: Nil

    case D.Global(x) =>
      P.Move(t, P.Global(x)) :: Nil
  }

  def newLabel(): Label = {
    ristretto.main.FreshId.freshId("Lperc")
  }

  def newTemp(): Temp = {
    ristretto.main.FreshId.freshId("tperc")
  }
}
