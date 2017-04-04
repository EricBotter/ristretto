package ristretto.frontend

// Generate Drip from Ristretto ASTs
// Drip generation is similar to the IR described in class except for how arrays
// are handled. Before each array we generate a two-word header containing
// the dimensionality of the array and the length of the outer dimension.
// Each subarray is one dimension less and has its own length.
// Code generation for arrays thus depends on the type of the array.
// In addition, boolean arrays are implemented as byte arrays.
object DripGen {
  import ristretto.drip.{DripSyntax => D}
  import ristretto.frontend.RistrettoSyntax._
  import ristretto.frontend.Trees._

  type Label = String
  type Temp = String

  type Name = String

  val WORDSIZE = 8

  def translate(t: Root): D.Root = t match {
    case Root(dfns) =>
      val procs = dfns collect {
        case p @ FunDef(tt, x, params, body) =>
          new ProcTranslator().translate(p)
      }
      D.Root(procs)
  }

  class ProcTranslator() {
    val returnValueTemp = newTemp()
    val returnLabel = newLabel()
    val arrayBoundsLabel = newLabel()
    val divByZeroLabel = newLabel()

    // Error codes. These should agree with the codes in the runtime.
    val ARRAY_BOUNDS_ERROR = 0
    val DIV_BY_0_ERROR = 1

    // boolean not -- assumes False = 0 and True = 1
    // this does not work if True is just non-zero
    // 1 - 0 = 1
    // 1 - 1 = 0
    def DNot(e: D.Exp) = D.BinOp(D.SUB(), D.Lit(1), e)

    val FALSE = D.Lit(0)
    val TRUE = D.Lit(1)

    def translate(p: FunDef): D.Proc = p match {
      case FunDef(tt, x, params, body) =>
        D.Proc(x,
               params.map { case Param(t, x) => x },
               D.Begin(translate(body) ++ {
                         D.Jmp(returnLabel) ::
                         D.LabelStm(arrayBoundsLabel) ::
                         D.ErrorStm(ARRAY_BOUNDS_ERROR) ::
                         D.LabelStm(divByZeroLabel) ::
                         D.ErrorStm(DIV_BY_0_ERROR) ::
                         D.LabelStm(returnLabel) ::
                         Nil
                       },
                       D.Temp(returnValueTemp)))
    }

    def translateBranch(e: Exp, ifTrue: Label, ifFalse: Label): List[D.Stm] = e match {
      case Not(e) =>
        translateBranch(e, ifFalse, ifTrue)
      case And(e1, e2) =>
        val l = newLabel()
        translateBranch(e1, l, ifFalse) ++ {
          D.LabelStm(l) :: translateBranch(e2, ifTrue, ifFalse)
        }
      case Or(e1, e2) =>
        val l = newLabel()
        translateBranch(e1, ifTrue, l) ++ {
          D.LabelStm(l) :: translateBranch(e2, ifTrue, ifFalse)
        }
      case True() =>
        D.Jmp(ifTrue) :: Nil
      case False() =>
        D.Jmp(ifFalse) :: Nil
      case e =>
        D.CJmp(translate(e), ifTrue) :: D.Jmp(ifFalse) :: Nil
    }

    def translate(s: Stm): List[D.Stm] = s match {
      case VarDefStm(t, x, e) =>
        D.Move(x, translate(e))::
        Nil

      case CallStm(e) =>
        val t0 = newTemp()
        D.Move(t0, translate(e))::
        Nil

      case Assign(x, e) =>
        D.Move(x, translate(e))::
        Nil

      case ArrayAssign(a, i, v) =>
        val ta = newTemp()
        val ti = newTemp()
        val Lok = newLabel()
        D.Move(ta, translate(a)) ::
        D.Move(ti, translate(i)) ::
        translateBranch(And(Le(IntLit(0), Var(ti)), Lt(Var(ti), ArrayLength(Var(ta)))), Lok, arrayBoundsLabel) ++ {
          D.LabelStm(Lok) ::
          arrayStore(D.Temp(ta), D.Temp(ti), translate(v)) ::
          Nil
        }

      case Return(None) =>
        D.Jmp(returnLabel)::
        Nil

      case Return(Some(e)) =>
        D.Move(returnValueTemp, translate(e))::
        D.Jmp(returnLabel)::
        Nil

      case IfElse(e0, s1, s2) =>
        val ljoin = newLabel()
        val ltrue = newLabel()
        val lfalse = newLabel()
        translateBranch(e0, ltrue, lfalse) ++ {
          D.LabelStm(ltrue) :: translate(s1) ++ {
            D.Jmp(ljoin) :: D.LabelStm(lfalse) :: translate(s2) ++ {
              D.LabelStm(ljoin) :: Nil
            }
          }
        }

      case IfThen(e0, s1) =>
        val ljoin = newLabel()
        val ltrue = newLabel()
        translateBranch(e0, ltrue, ljoin) ++ {
          D.LabelStm(ltrue) :: translate(s1) ++ {
            D.LabelStm(ljoin) :: Nil
          }
        }

      case While(e0, s1) =>
        val ltop = newLabel()
        val lbot = newLabel()
        val lend = newLabel()

        D.Jmp(lbot) ::
        D.LabelStm(ltop) ::
        translate(s1) ++ {
          D.LabelStm(lbot) :: translateBranch(e0, ltop, lend) ++ {
            D.LabelStm(lend) :: Nil
          }
        }

      case Block(Nil) =>
        D.Nop()::
        Nil

      case Block(ss) =>
        ss.flatMap { s => translate(s) }
    }

    // Array store without bounds check
    def arrayStore(a: D.Exp, i: D.Exp, v: D.Exp): D.Stm = {
      D.Store(WORDSIZE * 2, D.BinOp(D.ADD(), a, D.BinOp(D.MUL(), D.Lit(WORDSIZE), i)), v)
    }

    // Array load without bounds check
    def arrayLoad(a: D.Exp, i: D.Exp): D.Exp = {
      D.Load(WORDSIZE * 2, D.BinOp(D.ADD(), a, D.BinOp(D.MUL(), D.Lit(WORDSIZE), i)))
    }

    // translate from an expression to Drip
    def translate(e: Exp): D.Exp = {
      e match {
        case IntLit(v) => D.Lit(v)
        case False() => FALSE
        case True() => TRUE

        case e @ And(e1, e2) =>
          val t = newTemp()
          D.Begin(translate(Assign(t, False())) ++
                  translate(IfThen(e, Assign(t, True()))),
                  D.Temp(t))

        case e @ Or(e1, e2) =>
          val t = newTemp()
          D.Begin(translate(Assign(t, False())) ++
                translate(IfThen(e, Assign(t, True()))),
                D.Temp(t))

        case Add(e1, IntLit(0)) => translate(e1)
        case Sub(e1, IntLit(0)) => translate(e1)
        case Mul(e1, IntLit(1)) => translate(e1)
        case Add(IntLit(0), e1) => translate(e1)
        case Mul(IntLit(1), e1) => translate(e1)

        case Add(e1, Neg(e2)) => translate(Sub(e1, e2))
        case Sub(e1, Neg(e2)) => translate(Add(e1, e2))

        case Add(e1, e2) => D.BinOp(D.ADD(), translate(e1), translate(e2))
        case Sub(e1, e2) => D.BinOp(D.SUB(), translate(e1), translate(e2))
        case Mul(e1, e2) => D.BinOp(D.MUL(), translate(e1), translate(e2))

        case Div(e1, e2) =>
          val t1 = newTemp()
          val t2 = newTemp()
          val Lok = newLabel()
          D.Begin(D.Move(t1, translate(e1))::
                  D.Move(t2, translate(e2))::
                  D.CJmp(D.BinOp(D.EQ(), D.Temp(t2), D.Lit(0)), divByZeroLabel)::Nil,
                  D.BinOp(D.DIV(), D.Temp(t1), D.Temp(t2)))

        case Mod(e1, e2) =>
          val t1 = newTemp()
          val t2 = newTemp()
          val Lok = newLabel()
          D.Begin(D.Move(t1, translate(e1))::
                  D.Move(t2, translate(e2))::
                  D.CJmp(D.BinOp(D.EQ(), D.Temp(t2), D.Lit(0)), divByZeroLabel)::Nil,
                  D.BinOp(D.REM(), D.Temp(t1), D.Temp(t2)))

        case Eq(e1, e2) => D.BinOp(D.EQ(), translate(e1), translate(e2))
        case Ne(e1, e2) => D.BinOp(D.NE(), translate(e1), translate(e2))
        case Lt(e1, e2) => D.BinOp(D.LT(), translate(e1), translate(e2))
        case Le(e1, e2) => D.BinOp(D.LE(), translate(e1), translate(e2))
        case Ge(e1, e2) => D.BinOp(D.GE(), translate(e1), translate(e2))
        case Gt(e1, e2) => D.BinOp(D.GT(), translate(e1), translate(e2))

        case Not(Eq(e1, e2)) => translate(Ne(e1, e2))
        case Not(Ne(e1, e2)) => translate(Eq(e1, e2))
        case Not(Lt(e1, e2)) => translate(Ge(e1, e2))
        case Not(Gt(e1, e2)) => translate(Le(e1, e2))
        case Not(Le(e1, e2)) => translate(Gt(e1, e2))
        case Not(Ge(e1, e2)) => translate(Lt(e1, e2))

        case Not(e) => DNot(translate(e))
        case Neg(e) => translate(Sub(IntLit(0), e))

        case Var(x) =>
          D.Temp(x)

        case ArrayLength(a) =>
          val ta = newTemp()
          D.Load(0, translate(a))

        case ArrayGet(a, i) =>
          val ta = newTemp()
          val ti = newTemp()
          val t2 = newTemp()
          val Lok = newLabel()
          D.Begin(D.Move(ta, translate(a)) ::
                  D.Move(ti, translate(i)) ::
                  translateBranch(And(Le(IntLit(0), Var(ti)), Lt(Var(ti), ArrayLength(Var(ta)))), Lok, arrayBoundsLabel) ++ {
                    D.LabelStm(Lok) :: Nil
                  },
                  arrayLoad(D.Temp(ta), D.Temp(ti)))

        case Call(f, es) =>
          D.Call(D.Global(f), es.map { e => translate(e) })

        case StringLit(s) =>
          // String literals are a special case of array literals.
          // Just construct the array literal and translate that.
          val v = parseStringLiteral(s)
          // Array literals cannot be empty, but string literals can be.
          v match {
            case "" =>
              // new int[0]
              translate(NewMultiArray(IntTyTree(), IntLit(0)::Nil))
            case v =>
              // { 'h', 'e', 'l', 'l', 'o' }
              translate(ArrayLit(v.toList.map { ch => IntLit(ch) }))
          }

        case e @ ArrayLit(es) =>
          // The construction is similar to the multi-dimensional array case
          // except we just initialize the array directly.

          // Compute the dimensionality of the array
          def dimensions(e: Exp): Int = e match {
            case IntLit(_) => 0
            case BooleanLit(_) => 0
            case StringLit(_) => 1  // string literals are int[]
            case ArrayLit(e::es) => dimensions(e) + 1
            case NewMultiArray(_, ns) => ns.length
            case _ => -1
          }

          // Arrays have a 2-word header and one word per element.
          // We store the length in the first word and the dimensionality in the second.
          val length = es.length
          val dims = dimensions(e)
          assert(dims >= 1)

          val ta = newTemp()
          val ti = newTemp()
          D.Begin(D.Move(ta, D.Alloc(D.BinOp(D.ADD(), D.Lit(WORDSIZE*2), D.BinOp(D.MUL(), D.Lit(WORDSIZE), D.Lit(length))))) ::
                  D.Store(0, D.Temp(ta), D.Lit(length)) ::
                  D.Store(WORDSIZE, D.Temp(ta), D.Lit(dims)) ::
                  // To initialize the array, we just translate a bunch of
                  // array assignments.
                  es.zipWithIndex.map {
                    case (e, i) => arrayStore(D.Temp(ta), D.Lit(i), translate(e))
                  },
                  D.Temp(ta))

        case NewMultiArray(ty, n::ns) =>
          // Arrays have a 2-word header and one word per element.
          // We store the length in the first word and the dimensionality in the second.
          val dims = ns.length + 1
          val ta = newTemp()
          val tn = newTemp()
          D.Begin(D.Move(tn, translate(n)) ::
                  D.Move(ta, D.Alloc(D.BinOp(D.ADD(), D.Lit(WORDSIZE*2), D.BinOp(D.MUL(), D.Lit(WORDSIZE), D.Temp(tn))))) ::
                  D.Store(0, D.Temp(ta), D.Temp(tn)) ::
                  D.Store(WORDSIZE, D.Temp(ta), D.Lit(dims)) :: {
                    // To initialize the array, we use a loop allocating
                    // a subarray of one dimension less for each entry.
                    if (dims > 1) {
                      val ti = newTemp()
                      val bot = newLabel()
                      val top = newLabel()
                      // i = 0
                      D.Move(ti, D.Lit(0)) ::
                      // goto bot
                      // top:
                      D.Jmp(bot) ::
                      D.LabelStm(top) ::
                      // a[i] = new T[ns]
                      arrayStore(D.Temp(ta), D.Temp(ti), translate(NewMultiArray(ty, ns))) ::
                      // i = i + 1
                      D.Move(ti, D.BinOp(D.ADD(), D.Temp(ti), D.Lit(1))) ::
                      // bot:
                      // if (i < n) goto top
                      D.LabelStm(bot) ::
                      D.CJmp(D.BinOp(D.LT(), D.Temp(ti), D.Temp(tn)), top) ::
                      Nil
                    }
                    else {
                      // In other cases, the array is initialized to 0 or false.
                      Nil
                    }
                  },
                  D.Temp(ta))

      }
    }
  }

  def newLabel(): Label = {
    ristretto.main.FreshId.freshId("Ldrip")
  }

  def newTemp(): Temp = {
    ristretto.main.FreshId.freshId("tdrip")
  }
}
