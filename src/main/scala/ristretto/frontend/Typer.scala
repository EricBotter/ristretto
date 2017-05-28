package ristretto.frontend

// Type checker for Ristretto ASTs.
object Typer {
  import ristretto.frontend.RistrettoSyntax._
  import ristretto.frontend.Trees._
  import ristretto.main.{Compiler => Errors}

  sealed trait Type
  case class IntType() extends Type {
    override def toString = "int"
  }
  case class FloatType() extends Type {
    override def toString = "float"
  }
  case class BooleanType() extends Type {
    override def toString = "boolean"
  }
  case class VoidType() extends Type {
    override def toString = "void"
  }
  case class ArrayType(t: Type) extends Type {
    override def toString = t + "[]"
  }
  case class FunType(args: List[Type], ret: Type) extends Type {
    override def toString = args.mkString("(", ", ", ")") + " -> " + ret
  }
  case class UnknownType() extends Type {
    override def toString = "unknown"
  }

  def makeFunType(params: List[Param], ty: TyTree): Type = {
    FunType(params.map { case Param(tt, x) => convertTyTree(tt) }, convertTyTree(ty))
  }

  type Env = Map[String, Type]

  def makeEnv(dfns: List[Def]) = dfns.foldLeft(Map.empty: Env) {
    case (env, FunDef(ty, x, params, body)) =>
      env + (x -> makeFunType(params, ty))
    case (env, ExternDef(ty, x, params)) =>
      env + (x -> makeFunType(params, ty))
  }

  def typeCheck(r: Root): Unit = r match {
    case Root(dfns) =>
      val env = makeEnv(dfns)
      for (dfn <- dfns) {
        typeCheck(dfn)(env)
        checkReturns(dfn)
      }
  }

  def typeCheck(dfn: Def)(env: Env): Unit = dfn match {
    case FunDef(ty, x, params, body) =>
      typeCheck(body)(env + ("return" -> convertTyTree(ty)) ++ params.map {
        case Param(ty, x) => (x -> convertTyTree(ty))
      })
    case ExternDef(ty, x, params) =>
  }

  // Check if the definition definitely returns.
  def checkReturns(dfn: Def): Unit = dfn match {
    case FunDef(ty, x, params, body) =>
      if (! definitelyReturnsOnce(body)) {
        Errors.error(dfn, s"function $x does not definitely return exactly once")
      }
    case ExternDef(ty, x, params) =>
  }

  def definitelyReturnsOnce(s: Stm): Boolean = s match {
    case Return(_) => true
    case IfElse(_, s1, s2) => definitelyReturnsOnce(s1) && definitelyReturnsOnce(s2)
    case Block(s::Nil) => definitelyReturnsOnce(s)
    case Block(s::ss) => ! returns(s) && definitelyReturnsOnce(Block(ss))
    case IfThen(_, s) => ! returns(s)
    case While(_ ,s) => ! returns(s)
    case _ => false
  }

  def returns(s: Stm): Boolean = s match {
    case Return(_) => true
    case IfElse(_, s1, s2) => returns(s1) || returns(s2)
    case IfThen(_, s) => returns(s)
    case Block(s::ss) => returns(s) || returns(Block(ss))
    case While(_, s) => returns(s)
    case _ => false
  }

  def typeCheck(s: Stm)(env: Env): Unit = s match {
    case Block(Nil) => ()
    case Block(Return(_)::_::_) =>
      Errors.error(s, s"return statement cannot appear in the middle of a block")
    case Block(VarDefStm(_, _, _)::Nil) =>
      Errors.error(s, s"variable declaration cannot be last statement of block")
    case Block(s::Nil) =>
      typeCheck(s)(env)
    case Block((s @ VarDefStm(t, x, e))::ss) =>
      typeCheck(s)(env)
      typeCheck(Block(ss))(env + (x -> convertTyTree(t)))
    case Block(s::ss) =>
      typeCheck(s)(env)
      typeCheck(Block(ss))(env)
    case CallStm(e) =>
      typeCheck(e)(env) match {
        case VoidType() => ()
        case t =>
          Errors.error(s, s"call statement must be void")
      }
    case VarDefStm(t, x, e) =>
      val expected = convertTyTree(t)
      typeCheck(e)(env) match {
        case ty if ty != expected =>
          Errors.error(s, s"cannot initialize variable of type $expected with expression of type $ty")
        case _ =>
      }
    case Assign(x, e) =>
      env.get(x) match {
        case Some(ty) =>
          typeCheck(e)(env) match {
            case ty1 if ty != ty1 =>
              Errors.error(s, s"cannot assign ${ty1} to variable of type ${ty}")
            case _ =>
          }
        case None =>
          Errors.error(s, s"variable ${x.toString} not found")
      }
    case ArrayAssign(a, i, e) =>
      typeCheck(a)(env) match {
        case ArrayType(t1) =>
          typeCheck(i)(env) match {
            case IntType() =>
            case _ =>
              Errors.error(e, "array index expression must be an integer")
          }
          typeCheck(e)(env) match {
            case t2 if t1 != t2 =>
              Errors.error(s, s"cannot assign element of type $t2 into array of type $t1")
            case _ =>
          }
        case t =>
          Errors.error(a, "array expression must have array type")
      }
    case IfElse(cond, e1, e2) =>
      typeCheck(cond)(env) match {
        case BooleanType() =>
          typeCheck(e1)(env)
          typeCheck(e2)(env)
        case ty =>
          Errors.error(cond, s"condition of if must be boolean")
      }
    case IfThen(cond, e1) =>
      typeCheck(cond)(env) match {
        case BooleanType() =>
          typeCheck(e1)(env)
        case ty =>
          Errors.error(cond, s"condition of if must be boolean")
      }
    case While(cond, e) =>
      typeCheck(cond)(env) match {
        case BooleanType() =>
          typeCheck(e)(env)
        case ty =>
          Errors.error(cond, s"condition of while must be boolean")
      }
    case Return(None) =>
      env.get("return") match {
        case Some(VoidType()) =>
        case Some(t) => Errors.error(s, s"function must return a value of type $t, not void")
        case None => Errors.error(s, s"cannot return outside a function")
      }
    case Return(Some(e)) =>
      typeCheck(e)(env) match {
        case ty =>
          env.get("return") match {
            case Some(t) if ty == t => ()
            case Some(t) => Errors.error(s, s"function must return a value of type $t, got $ty")
            case None => Errors.error(s, s"cannot return outside a function")
          }
      }
  }

  def typeCheck(e: Exp)(env: Env): Type = e match {
    case IntLit(_) => IntType()
    case FloatLit(_) => FloatType()
    case BooleanLit(_) => BooleanType()
    case StringLit(_) => ArrayType(IntType())
    case Arith(e1, e2) =>
      (typeCheck(e1)(env), typeCheck(e2)(env)) match {
        case (IntType(), IntType()) => IntType()
        case (FloatType(), IntType()) => FloatType()
        case (IntType(), FloatType()) => FloatType()
        case (FloatType(), FloatType()) => FloatType()
        case _ =>
          Errors.error(e, "operands of arithmetic operator must be integers or floats")
          UnknownType()
      }
    case Mod(e1, e2) =>
      (typeCheck(e1)(env), typeCheck(e2)(env)) match {
        case (IntType(), IntType()) => IntType()
        case _ =>
          Errors.error(e, "operands of modulus operator must be integers")
          UnknownType()
      }
    case Equality(e1, e2) =>
      (typeCheck(e1)(env), typeCheck(e2)(env)) match {
        case (t1, t2) if t1 == t2 => BooleanType()
        case _ =>
          Errors.error(e, "operands of equality operator must match")
          UnknownType()
      }
    case Rel(e1, e2) =>
      (typeCheck(e1)(env), typeCheck(e2)(env)) match {
        case (IntType(), IntType()) => BooleanType()
        case (FloatType(), IntType()) => BooleanType()
        case (IntType(), FloatType()) => BooleanType()
        case (FloatType(), FloatType()) => BooleanType()
        case _ =>
          Errors.error(e, "operands of relational operators must be integers or floats")
          UnknownType()
      }
    case Bool(e1, e2) =>
      (typeCheck(e1)(env), typeCheck(e2)(env)) match {
        case (BooleanType(), BooleanType()) => BooleanType()
        case _ =>
          Errors.error(e, "operands of boolean operator must be booleans")
          UnknownType()
      }
    case Not(e) =>
      typeCheck(e)(env) match {
        case BooleanType() => BooleanType()
        case t =>
          Errors.error(e, "operand of not operator must be boolean")
          UnknownType()
      }
    case Neg(e) =>
      typeCheck(e)(env) match {
        case IntType() => IntType()
        case FloatType() => FloatType()
        case t =>
          Errors.error(e, "operand of negation operator must be integer or float")
          UnknownType()
      }
    case Var(x) => env.get(x) match {
      case Some(ty) => ty
      case None =>
        Errors.error(e, s"variable ${x.toString} not found")
        UnknownType()
    }
    case ArrayGet(a, i) =>
      typeCheck(a)(env) match {
        case ArrayType(t1) =>
          typeCheck(i)(env) match {
            case IntType() =>
            case _ =>
              Errors.error(e, "array index expression must be an integer")
          }
          t1
        case t =>
          Errors.error(e, "array expression must have array type")
          UnknownType()
      }
    case ArrayLength(e1) =>
      typeCheck(e1)(env) match {
        case ArrayType(t1) => IntType()
        case t =>
          Errors.error(e, "array expression must have array type")
          UnknownType()
      }
    case NewMultiArray(ty, es) =>
      // We don't allow new (int[])[10] because we don't have null for unintialized array elements.
      ty match {
        case ArrayTyTree(_) =>
          Errors.error(e, "must specify the sizes of all array dimensions. Cannot create a new array of arrays")
        case _ =>
      }
      for (e <- es) {
        typeCheck(e)(env) match {
          case IntType() =>
          case _ =>
            Errors.error(e, "array size expression must be an integer")
        }
      }
      es.foldLeft(convertTyTree(ty): Type) {
        case (ty, e) => ArrayType(ty)
      }
    case ArrayLit(Nil) =>
      Errors.error(e, "array literals must be non-empty")
      ArrayType(UnknownType())
    case ArrayLit(e::Nil) =>
      if (! isAllowedInArrayLiteral(e)) {
        Errors.error(e, "array literals may only contain literals or new array expressions")
      }
      typeCheck(e)(env) match {
        case t => ArrayType(t)
      }
    case ArrayLit(e::es) =>
      if (! isAllowedInArrayLiteral(e)) {
        Errors.error(e, "array literals may only contain literals or new array expressions")
      }
      typeCheck(e)(env) match {
        case t =>
          typeCheck(ArrayLit(es))(env) match {
            case ArrayType(ts) if t == ts => ArrayType(t)
            case ts =>
              Errors.error(e, "all array elements must be of the same type")
              UnknownType()
          }
      }
    case Call(f, es) =>
      env.get(f) match {
        case Some(FunType(formals, ret)) =>
          val actuals = for (e <- es) yield {
            typeCheck(e)(env)
          }
          if (actuals != formals) {
            Errors.error(e, s"cannot pass arguments of type ${actuals.mkString("(", ", ", ")")} to function expecting ${formals.mkString("(", ", ", ")")}")
          }
          ret
        case Some(ty) =>
          Errors.error(e, s"function ${f.toString} must have function type")
          UnknownType()
        case None =>
          Errors.error(e, s"function ${f.toString} not found")
          UnknownType()
      }
  }

  // Array literals are restricted to contain just literals and new array expressions
  // This ensures we can determine the dimensionality of the array without typing.
  def isAllowedInArrayLiteral(e: Exp): Boolean = e match {
    case StringLit(_) => true
    case IntLit(_) => true
    case FloatLit(_) => true
    case BooleanLit(_) => true
    case ArrayLit(es) => es.forall(isAllowedInArrayLiteral)
    case NewMultiArray(_, ns) => true
    case _ => false
  }

  def convertTyTree(ty: TyTree): Type = ty match {
    case IntTyTree() => IntType()
    case FloatTyTree() => FloatType()
    case BooleanTyTree() => BooleanType()
    case VoidTyTree() => VoidType()
    case ArrayTyTree(t) => ArrayType(convertTyTree(t))
  }
}
