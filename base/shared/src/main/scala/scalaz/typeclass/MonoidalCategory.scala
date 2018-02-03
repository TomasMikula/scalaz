package scalaz
package typeclass

trait MonoidalCategory[=>:[_,_], x[_,_], I] {
  def category: Category[=>:]
  def parallel[A, B, C, D](f: A =>: B, g: C =>: D): (A x C) =>: (B x D)
  def assocLR[A, B, C](abc: (A x B) x C): A x (B x C)
  def assocRL[A, B, C](abc: A x (B x C)): (A x B) x C
  def addUnitL[A](a: A): I x A
  def addUnitR[A](a: A): A x I
  def elimUnitL[A](ia: I x A): A
  def elimUnitR[A](ai: A x I): A
}

trait CartesianMonoidalCategory[=>:[_,_], x[_,_], I] {
  def prod[A, B, C](f: A =>: B, g: A =>: C): A =>: (B x C)
  def fst[A, B]: (A x B) =>: A
  def snd[A, B]: (A x B) =>: B
  def terminal[A]: A =>: I
}

trait ClosedMonoidalCategory[=>:[_,_], x[_,_], I, ->:[_,_]] {
  def monoidalCategory: MonoidalCategory[=>:, x, I]
  def curry[A, B, C](f: (A x B) =>: C): A =>: (B ->: C)
  def eval[A, B]: ((A ->: B) x A) =>: B

  def uncurry[A, B, C](f: A =>: (B ->: C)): (A x B) =>: C =
    monoidalCategory.category.compose.compose(eval[B, C], monoidalCategory.parallel(f, monoidalCategory.category.id[B]))
}

trait CartesianClosedCategory[=>:[_,_], x[_,_], I, ->:] {
}

sealed trait FreeCCC[=>:[_,_], x[_,_], I, ->:[_,_], A, B]
object FreeCCC {
  import data.AList1

  case class Wrap[=>:[_,_], x[_,_], I, ->:[_,_], A, B](f: A =>: B) extends FreeCCC[=>:, x, I, ->:, A, B]
  case class Sequence[=>:[_,_], x[_,_], I, ->:[_,_], A, B](fs: AList1[FreeCCC[=>:, x, I, ->:, ?, ?], A, B]) extends FreeCCC[=>:, x, I, ->:, A, B]
  case class Id[=>:[_,_], x[_,_], I, ->:[_,_], A]() extends FreeCCC[=>:, x, I, ->:, A, A]
  case class Fst[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, A x B, A]
  case class Snd[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, A x B, B]
  case class Prod[=>:[_,_], x[_,_], I, ->:[_,_], A, B, C](f: FreeCCC[=>:, x, I, ->:, A, B], g: FreeCCC[=>:, x, I, ->:, A, C]) extends FreeCCC[=>:, x, I, ->:, A, B x C]
  case class Const[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, A, B ->: A]
  case class Curry[=>:[_,_], x[_,_], I, ->:[_,_], A, B, C](f: FreeCCC[=>:, x, I, ->:, A x B, C]) extends FreeCCC[=>:, x, I, ->:, A, B ->: C]
  case class Eval[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, (A ->: B) x A, B]
}

sealed trait SuperFreeCCC[=>:[_,_], A, B] {
  def apply[x[_,_], I, ->:[_,_]]: FreeCCC[=>:, x, I, ->:, A, B]
}

trait FunModule {
  type Fun[A, B]
}

object FunImpl extends FunModule {
  type Fun[A, B] = FreeCCC[Function1, Tuple2, Unit, Function1, A, B]
}

sealed trait RecFun[A, B] {
  def apply(a: A): B = RecFun.eval(this, a)
}

object RecFun {
  import scalaz.data._

  type Fun[A, B] = FreeCCC[Function1, Tuple2, Unit, Function1, A, B]
  type =>:[A, B] = RecFun[A, B]

  case class WrapFun[A, B](f: Fun[A, B]) extends RecFun[A, B]
  case class Rec[A, B](f: A =>: (A =>: B) =>: B) extends RecFun[A, B]

  private[RecFun] def eval[A, B](f: A =>: B, a: A): B =
    evalStack(a, compile(f))

  private def compile[A, B](f: A =>: B): InstList[A, B] = f match {
    case WrapFun(g) => g match {
      case _ => ???
    }
    case Rec(g) => Put(f) :: Swap() ::: compile(g) :: Load(???) :: AList.empty
  }

  @annotation.tailrec
  private def evalStack[L, R](l: L, is: InstList[L, R]): R =
    is match {
      case ev @ ANil() => ev.leibniz(l)
      case ACons(i, is) => i(l) match {
        case \/-(r) => r
        case -\/(p) => evalStack(p._1, p._2 ::: is)
      }
        case TransformTop(f) => evalStack( (f(l._1), l._2)            , is )
        case Put(a)          => evalStack( (a, l)                     , is )
        case Merge()         => evalStack( ((l._1, l._2._1), l._2._2) , is )
        case Unmerge()       => evalStack( (l._1._1, (l._1._2, l._2)) , is )
        case Swap()          => evalStack( (l._2._1, (l._1, l._2._2)) , is )
        case Load(f)         =>
          val (x, js) = f(l) ;  evalStack( x, js ::: is )
      }
    }

  sealed trait Inst[L, R] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R
  }

  case class TransformTop[A, T, B, R](f: A => B) extends Inst[(A, T), (B, T)] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R = 
  }
  case class Put[A, T](a: A) extends Inst[T, (A, T)] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R
  }
  case class Merge[A, B, T]() extends Inst[(A, (B, T)), ((A, B), T)] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R
  }
  case class Unmerge[A, B, T]() extends Inst[((A, B), T), (A, (B, T))] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R
  }
  case class Swap[A, B, T]() extends Inst[(A, (B, T)), (B, (A, T))] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R
  }
  case class Load[A, B, R](load: A => (B, InstList[B, R])) extends Inst[A, R] {
    def apply(l: L) : APair[Id, InstList[?, R]] \/ R
  }

  type InstList[A, B] = AList[Inst, A, B]
}
