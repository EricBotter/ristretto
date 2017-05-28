package ristretto.frontend

// Extractors for Ristretto ASTs.
object Trees {
  import ristretto.frontend.RistrettoSyntax._

  // Parse string literals.
  def parseStringLiteral(e: String): String = {
    // Some extractors to make parsing numbers easier.
    object Hex {
      def unapply(ch: Char) = ch match {
        case ch if '0' <= ch && ch <= '9' => Some(ch - '0')
        case ch if 'a' <= ch && ch <= 'f' => Some(ch - 'a' + 10)
        case ch if 'A' <= ch && ch <= 'F' => Some(ch - 'A' + 10)
        case _ => None
      }
    }
    object Oct {
      def unapply(ch: Char) = ch match {
        case ch if '0' <= ch && ch <= '7' => Some(ch - '0')
        case _ => None
      }
    }
    object Oct3 {
      def unapply(ch: Char) = ch match {
        case ch if '0' <= ch && ch <= '3' => Some(ch - '0')
        case _ => None
      }
    }

    e match {
      case s if s.startsWith("\"") =>
        def parse(cs: List[Char]): List[Char] = cs match {
          case '\\'::'b'::rest => '\b' :: parse(rest)
          case '\\'::'t'::rest => '\t' :: parse(rest)
          case '\\'::'f'::rest => '\f' :: parse(rest)
          case '\\'::'r'::rest => '\r' :: parse(rest)
          case '\\'::'n'::rest => '\n' :: parse(rest)
          case '\\'::'"'::rest => '\"' :: parse(rest)
          case '\\'::'\''::rest => '\'' :: parse(rest)
          case '\\'::'\\'::rest => '\\' :: parse(rest)
          case '\\'::'u'::Hex(a)::Hex(b)::Hex(c)::Hex(d)::rest =>
            (((((a * 16) + b) * 16) + c) * 16 + d).toChar :: parse(rest)
          case '\\'::Oct3(a)::Oct(b)::Oct(c)::rest =>
            ((((a * 8) + b) * 8) + c).toChar :: parse(rest)
          case '\\'::Oct(a)::Oct(b)::rest =>
            (((a * 8) + b) * 8).toChar :: parse(rest)
          case '\\'::Oct(a)::rest =>
            (a * 8).toChar :: parse(rest)
          case ch::rest =>
            ch :: parse(rest)
          case Nil => Nil
        }
        parse(s.tail.init.toList).mkString
      case s => s
    }
  }

  // View MultiArrayTyTrees as single-dimensional arrays.
  object ArrayTyTree {
    def unapply(ty: TyTree): Option[TyTree] = ty match {
      case MultiArrayTyTree(t, 1) => Some(t)
      case MultiArrayTyTree(t, n) => Some(MultiArrayTyTree(t, n-1))
      case _ => None
    }
    def apply(baseTy: TyTree) = baseTy match {
      case MultiArrayTyTree(t, n) => MultiArrayTyTree(t, n+1)
      case t => MultiArrayTyTree(t, 1)
    }
  }

  // View MultiArrayAssign as single-dimensional arrays.
  object ArrayAssign {
    def apply(a: Exp, i: Exp, v: Exp) = MultiArrayAssign(a, i::Nil, v)
    def unapply(e: Stm): Option[(Exp, Exp, Exp)] = e match {
      case MultiArrayAssign(a, i::Nil, v) => Some((a, i, v))
      case MultiArrayAssign(a, i::is, v) => unapply(MultiArrayAssign(ArrayGet(a, i), is, v))
      case _ => None
    }
  }

  // View MultiArrayGet as single-dimensional arrays.
  object ArrayGet {
    def apply(a: Exp, i: Exp) = MultiArrayGet(a, i::Nil)
    def unapply(e: Exp): Option[(Exp, Exp)] = e match {
      case MultiArrayGet(a, i::Nil) => Some((a, i))
      case MultiArrayGet(a, i::is) => unapply(MultiArrayGet(ArrayGet(a, i), is))
      case _ => None
    }
  }

  object Binary {
    def unapply(e: Exp): Option[(Exp, Exp)] = e match {
      case Add(e1, e2) => Some((e1, e2))
      case Sub(e1, e2) => Some((e1, e2))
      case Mul(e1, e2) => Some((e1, e2))
      case Div(e1, e2) => Some((e1, e2))
      case Mod(e1, e2) => Some((e1, e2))
      case Eq(e1, e2) => Some((e1, e2))
      case Ne(e1, e2) => Some((e1, e2))
      case Lt(e1, e2) => Some((e1, e2))
      case Gt(e1, e2) => Some((e1, e2))
      case Le(e1, e2) => Some((e1, e2))
      case Ge(e1, e2) => Some((e1, e2))
      case _ => None
    }
  }

  object Arith {
    def unapply(e: Exp): Option[(Exp, Exp)] = e match {
      case Add(e1, e2) => Some((e1, e2))
      case Sub(e1, e2) => Some((e1, e2))
      case Mul(e1, e2) => Some((e1, e2))
      case Div(e1, e2) => Some((e1, e2))
//      case Mod(e1, e2) => Some((e1, e2))
      case _ => None
    }
  }
  object Equality {
    def unapply(e: Exp): Option[(Exp, Exp)] = e match {
      case Eq(e1, e2) => Some((e1, e2))
      case Ne(e1, e2) => Some((e1, e2))
      case _ => None
    }
  }
  object Rel {
    def unapply(e: Exp): Option[(Exp, Exp)] = e match {
      case Lt(e1, e2) => Some((e1, e2))
      case Gt(e1, e2) => Some((e1, e2))
      case Le(e1, e2) => Some((e1, e2))
      case Ge(e1, e2) => Some((e1, e2))
      case _ => None
    }
  }
  object Bool {
    def unapply(e: Exp): Option[(Exp, Exp)] = e match {
      case And(e1, e2) => Some((e1, e2))
      case Or(e1, e2) => Some((e1, e2))
      case _ => None
    }
  }
  object BooleanLit {
    def unapply(e: Exp): Option[Boolean] = e match {
      case True() => Some(true)
      case False() => Some(false)
      case _ => None
    }
  }
}
