package scalaam.lattice

import scalaam.core._

object ConstantPropagation {
  sealed trait L[+A]
  case object Top              extends L[Nothing]
  case class Constant[A](x: A) extends L[A]
  case object Bottom           extends L[Nothing]

  abstract class BaseInstance[A](typeName: String) extends Lattice[L[A]] {
    def show(x: L[A]): String = x match {
      case Top         => typeName
      case Constant(x) => x.toString
      case Bottom      => s"$typeName.⊥"
    }
    val bottom: L[A] = Bottom
    val top: L[A]    = Top
    def join(x: L[A], y: => L[A]): L[A] = x match {
      case Top => Top
      case Constant(_) =>
        y match {
          case Top => Top
          case Constant(_) =>
            if (x == y) {
              x
            } else {
              Top
            }
          case Bottom => x
        }
      case Bottom => y
    }
    def meet(x: L[A], y: => L[A]): L[A] = x match {
      case Bottom => Bottom
      case Constant(_) =>
        y match {
          case Top => x
          case Constant(_) =>
            if (x == y) {
              x
            } else {
              Bottom
            }
          case Bottom => Bottom
        }
      case Top => y
    }
    def subsumes(x: L[A], y: => L[A]): Boolean = x match {
      case Top => true
      case Constant(_) =>
        y match {
          case Top         => false
          case Constant(_) => x == y
          case Bottom      => true
        }
      case Bottom =>
        y match {
          case Top         => false
          case Constant(_) => false
          case Bottom      => true
        }
    }
    def eql[B2: BoolLattice](n1: L[A], n2: L[A]): B2 = (n1, n2) match {
      case (Top, Top)                 => BoolLattice[B2].top
      case (Top, Constant(_))         => BoolLattice[B2].top
      case (Constant(_), Top)         => BoolLattice[B2].top
      case (Constant(x), Constant(y)) => BoolLattice[B2].inject(x == y)
      case (Bottom, _)                => BoolLattice[B2].bottom
      case (_, Bottom)                => BoolLattice[B2].bottom
    }
  }

  type B   = L[Boolean]
  type S   = L[String]
  type I   = L[Int]
  type R   = L[Double]
  type C   = L[Char]
  type Sym = L[String]

  object L {
    import scalaam.lattice._

    implicit val boolCP: BoolLattice[B] = new BaseInstance[Boolean]("Bool") with BoolLattice[B] {
      def inject(b: Boolean): B = Constant(b)
      def isTrue(b: B): Boolean = b match {
        case Top => true
        case Constant(x) => x
        case Bottom => false
      }
      def isFalse(b: B): Boolean = b match {
        case Top => true
        case Constant(x) => !x
        case Bottom => false
      }
      def not(b: B): B = b match {
        case Top => Top
        case Constant(x) => Constant(!x)
        case Bottom => Bottom
      }
    }

    implicit val stringCP: StringLattice[S] = new BaseInstance[String]("Str")
    with StringLattice[S] {
      def inject(x: String): S = Constant(x)
      def length[I2: IntLattice](s: S) = s match {
        case Top         => IntLattice[I2].top
        case Constant(s) => IntLattice[I2].inject(s.size)
        case Bottom      => IntLattice[I2].bottom
      }
      def append(s1: S, s2: S) = (s1, s2) match {
        case (Bottom, _) | (_, Bottom)  => Bottom
        case (Top, _) | (_, Top)        => Top
        case (Constant(x), Constant(y)) => Constant(x ++ y)
      }
      def ref[I2: IntLattice, C2: CharLattice](s: S, i: I2): C2 = s match {
        case Bottom => CharLattice[C2].bottom
        case Top    => CharLattice[C2].top
        case Constant(x) =>
          (0.to(x.size))
            .collect({
              case i2
                  if BoolLattice[Concrete.B]
                    .isTrue(IntLattice[I2].eql[Concrete.B](i, IntLattice[I2].inject(i2))) =>
                CharLattice[C2].inject(x.charAt(i2))
            })
            .foldLeft(CharLattice[C2].bottom)((c1, c2) => CharLattice[C2].join(c1, c2))
      }
      def lt[B2: BoolLattice](s1: S, s2: S) = (s1, s2) match {
        case (Bottom, _) | (_, Bottom)  => BoolLattice[B2].bottom
        case (Top, _) | (_, Top)        => BoolLattice[B2].top
        case (Constant(x), Constant(y)) => BoolLattice[B2].inject(x < y)
      }
      def toSymbol[Sym2: SymbolLattice](s: S) = s match {
        case Bottom      => SymbolLattice[Sym2].bottom
        case Top         => SymbolLattice[Sym2].top
        case Constant(x) => SymbolLattice[Sym2].inject(x)
      }
      def toNumber[I2: IntLattice](s: S) = s match {
        case Bottom         => MayFail.success(IntLattice[I2].bottom)
        case Constant(str)  => MayFail.fromOption(str.toIntOption.map(IntLattice[I2].inject))(NotANumberString)
        case Top            => MayFail.success(IntLattice[I2].top).addError(NotANumberString)
      }
    }
    implicit val intCP: IntLattice[I] = new BaseInstance[Int]("Int") with IntLattice[I] {
      def inject(x: Int): I = Constant(x)
      def toReal[R2: RealLattice](n: I): R2 = n match {
        case Top         => RealLattice[R2].top
        case Constant(x) => RealLattice[R2].inject(x.toDouble)
        case Bottom      => RealLattice[R2].bottom
      }
      def random(n: I): I = n match {
        case Bottom => Bottom
        case _      => Top
      }
      private def binop(op: (Int, Int) => Int, n1: I, n2: I) = (n1, n2) match {
        case (Top, Top)                 => Top
        case (Top, Constant(_))         => Top
        case (Constant(_), Top)         => Top
        case (Constant(x), Constant(y)) => Constant(op(x, y))
        case _                          => Bottom
      }
      def plus(n1: I, n2: I): I  = binop(_ + _, n1, n2)
      def minus(n1: I, n2: I): I = binop(_ - _, n1, n2)
      def times(n1: I, n2: I): I = binop(_ * _, n1, n2)
      def div[F: RealLattice](n1: I, n2: I): F = (n1, n2) match {
        case (Top, _) | (_, Top)        => RealLattice[F].top
        case (Constant(x), Constant(y)) => RealLattice[F].inject(x / y.toDouble)
        case _                          => RealLattice[F].bottom
      }
      def expt(n1: I, n2: I): I = binop((x, y) => Math.pow(x.toDouble,y.toDouble).toInt, n1, n2)
      def quotient(n1: I, n2: I): I  = binop(_ / _, n1, n2)
      def modulo(n1: I, n2: I): I    = (n1, n2) match {
        case (Top, Top) => Top
        case (Top, Constant(_)) => Top
        case (Constant(_), Top) => Top
        case (Constant(x), Constant(y)) if y != 0 => Constant(MathOps.modulo(x, y))
        case _ => Bottom
      }
      def remainder(n1: I, n2: I): I = binop(MathOps.remainder, n1, n2)
      def lt[B2: BoolLattice](n1: I, n2: I): B2 = (n1, n2) match {
        case (Top, Top)                 => BoolLattice[B2].top
        case (Top, Constant(_))         => BoolLattice[B2].top
        case (Constant(_), Top)         => BoolLattice[B2].top
        case (Constant(x), Constant(y)) => BoolLattice[B2].inject(x < y)
        case _                          => BoolLattice[B2].bottom
      }
      def valuesBetween(n1: I, n2: I): Set[I] = (n1, n2) match {
        case (Top, _)                   => Set(Top)
        case (_, Top)                   => Set(Top)
        case (Constant(x), Constant(y)) => x.to(y).map(i => Constant(i)).toSet
        case _                          => Set()
      }
      def toString[S2: StringLattice](n: I): S2 = n match {
        case Top         => StringLattice[S2].top
        case Constant(x) => StringLattice[S2].inject(x.toString)
        case Bottom      => StringLattice[S2].bottom
      }
      def toChar[C2: CharLattice](n: I): C2 = n match {
        case Top         => CharLattice[C2].top
        case Constant(x) => CharLattice[C2].inject(x.asInstanceOf[Char])
        case Bottom      => CharLattice[C2].bottom
      }
    }
    implicit val floatCP: RealLattice[R] = new BaseInstance[Double]("Real") with RealLattice[R] {
      def inject(x: Double) = Constant(x)
      def toInt[I2: IntLattice](n: R): I2 = n match {
        case Top         => IntLattice[I2].top
        case Constant(x) => IntLattice[I2].inject(x.toInt)
        case Bottom      => IntLattice[I2].bottom
      }
      def ceiling[I2: IntLattice](n: R): I2 = n match {
        case Constant(x) => IntLattice[I2].inject(x.ceil.toInt)
        case Top         => IntLattice[I2].top
        case Bottom      => IntLattice[I2].bottom
      }
      def floor[I2: IntLattice](n: R): I2 = n match {
        case Constant(x) => IntLattice[I2].inject(x.floor.toInt)
        case Top         => IntLattice[I2].top
        case Bottom      => IntLattice[I2].bottom
      }
      def round[I2: IntLattice](n: R): I2 = n match {
        case Constant(x) => IntLattice[I2].inject(MathOps.round(x).toInt)
        case Top         => IntLattice[I2].top
        case Bottom      => IntLattice[I2].bottom
      }
      def random(n: R): R = n match {
        case Constant(_) => Top
        case _           => n
      }
      def log(n: R): R = n match {
        case Constant(x) => Constant(scala.math.log(x))
        case _           => n
      }
      def sin(n: R): R = n match {
        case Constant(x) => Constant(scala.math.sin(x))
        case _           => n
      }
      def asin(n: R): R = n match {
        case Constant(x) => Constant(scala.math.asin(x))
        case _           => n
      }
      def cos(n: R): R = n match {
        case Constant(x) => Constant(scala.math.cos(x))
        case _           => n
      }
      def acos(n: R): R = n match {
        case Constant(x) => Constant(scala.math.acos(x))
        case _           => n
      }
      def tan(n: R): R = n match {
        case Constant(x) => Constant(scala.math.tan(x))
        case _           => n
      }
      def atan(n: R): R = n match {
        case Constant(x) => Constant(scala.math.atan(x))
        case _           => n
      }
      def sqrt(n: R): R = n match {
        case Constant(x) => Constant(scala.math.sqrt(x))
        case _           => n
      }
      private def binop(op: (Double, Double) => Double, n1: R, n2: R) = (n1, n2) match {
        case (Top, Top)                 => Top
        case (Top, Constant(_))         => Top
        case (Constant(_), Top)         => Top
        case (Constant(x), Constant(y)) => Constant(op(x, y))
        case _                          => Bottom
      }
      def plus(n1: R, n2: R): R  = binop(_ + _, n1, n2)
      def minus(n1: R, n2: R): R = binop(_ - _, n1, n2)
      def times(n1: R, n2: R): R = binop(_ * _, n1, n2)
      def div(n1: R, n2: R): R   = binop(_ / _, n1, n2)
      def expt(n1: R, n2: R): R = binop((x, y) => Math.pow(x,y), n1, n2)
      def lt[B2: BoolLattice](n1: R, n2: R): B2 = (n1, n2) match {
        case (Top, Top)                 => BoolLattice[B2].top
        case (Top, Constant(_))         => BoolLattice[B2].top
        case (Constant(_), Top)         => BoolLattice[B2].top
        case (Constant(x), Constant(y)) => BoolLattice[B2].inject(x < y)
        case _                          => BoolLattice[B2].bottom
      }
      def toString[S2: StringLattice](n: R): S2 = n match {
        case Top         => StringLattice[S2].top
        case Constant(x) => StringLattice[S2].inject(x.toString)
        case Bottom      => StringLattice[S2].bottom
      }
    }
    implicit val charCP: CharLattice[C] = new BaseInstance[Char]("Char") with CharLattice[C] {
      def inject(x: Char) = Constant(x)
      def downCase(c: C) = c match {
        case Constant(char) => Constant(char.toLower)
        case _ => c
      }
      def upCase(c: C): C = c match {
        case Constant(char) => Constant(char.toUpper)
        case _ => c
      }
      def toString[S2: StringLattice](c: C): S2 = c match {
        case Top            => StringLattice[S2].top
        case Constant(char) => StringLattice[S2].inject(char.toString)
        case Bottom         => StringLattice[S2].bottom
      }
      def toInt[I2: IntLattice](c: C): I2 = c match {
        case Bottom       => IntLattice[I2].bottom
        case Constant(c)  => IntLattice[I2].inject(c.toInt)
        case Top          => IntLattice[I2].top
      }
      def isLower[B2: BoolLattice](c: C): B2 = c match {
        case Bottom         => BoolLattice[B2].bottom
        case Constant(char) => BoolLattice[B2].inject(char.isLower)
        case Top            => BoolLattice[B2].top
      }
      def isUpper[B2: BoolLattice](c: C): B2 = c match {
        case Bottom         => BoolLattice[B2].bottom
        case Constant(char) => BoolLattice[B2].inject(char.isUpper)
        case Top            => BoolLattice[B2].top
      }
      override def charEq[B2: BoolLattice](c1: C, c2: C): B2 = (c1, c2) match {
        case (Bottom, _) | (_, Bottom)    => BoolLattice[B2].bottom
        case (Constant(c1), Constant(c2)) => BoolLattice[B2].inject(c1 == c2)
        case _                            => BoolLattice[B2].top
      }
      override def charLt[B2: BoolLattice](c1: C, c2: C): B2 = (c1, c2) match {
        case (Bottom, _) | (_, Bottom)    => BoolLattice[B2].bottom
        case (Constant(c1), Constant(c2)) => BoolLattice[B2].inject(c1 < c2)
        case _                            => BoolLattice[B2].top
      }
      override def charEqCI[B2: BoolLattice](c1: C, c2: C): B2 = (c1, c2) match {
        case (Bottom, _) | (_, Bottom)    => BoolLattice[B2].bottom
        case (Constant(c1), Constant(c2)) => BoolLattice[B2].inject(c1.toUpper == c2.toUpper) // TODO implement better (see note in concrete lattice)
        case _                            => BoolLattice[B2].top
      }
      override def charLtCI[B2: BoolLattice](c1: C, c2: C): B2 = (c1, c2) match {
        case (Bottom, _) | (_, Bottom)    => BoolLattice[B2].bottom
        case (Constant(c1), Constant(c2)) => BoolLattice[B2].inject(c1.toUpper < c2.toUpper) // TODO implement better (see note in concrete lattice)
        case _                            => BoolLattice[B2].top
      }
    }
    implicit val symCP: SymbolLattice[Sym] = new BaseInstance[String]("Symbol")
    with SymbolLattice[Sym] {
      def inject(x: String) = Constant(x)
      def toString[S2: StringLattice](s: Sym): S2 = s match {
        case Top         => StringLattice[S2].top
        case Constant(x) => StringLattice[S2].inject(x)
        case Bottom      => StringLattice[S2].bottom
      }
    }
  }
}
