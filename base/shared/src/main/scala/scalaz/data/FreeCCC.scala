package scalaz
package data

sealed trait FreeCCC[=>:[_,_], x[_,_], I, ->:[_,_], A, B] {

  type Visitor[R] = FreeCCC.Visitor[=>:, x, I, ->:, A, B, R]

  def visit[R](v: Visitor[R]): R

  final def andThen[C](f: FreeCCC[=>:, x, I, ->:, B, C]): FreeCCC[=>:, x, I, ->:, A, C] =
    FreeCCC.Sequence(this :: AList1(f))

  final def compose[Z](f: FreeCCC[=>:, x, I, ->:, Z, A]): FreeCCC[=>:, x, I, ->:, Z, B] =
    FreeCCC.Sequence(f :: AList1(this))
}

object FreeCCC {

  case class Wrap[=>:[_,_], x[_,_], I, ->:[_,_], A, B](f: A =>: B) extends FreeCCC[=>:, x, I, ->:, A, B] {
    def visit[R](v: Visitor[R]): R = v.caseWrap(f)
  }
  case class Sequence[=>:[_,_], x[_,_], I, ->:[_,_], A, B](fs: AList1[FreeCCC[=>:, x, I, ->:, ?, ?], A, B]) extends FreeCCC[=>:, x, I, ->:, A, B] {
    private type ==>[X, Y] = FreeCCC[=>:, x, I, ->:, X, Y]
    private def id[X](): X ==> X = Id()

    def split: APair[A ==> ?, ? ==> B] = fs.tail match {
      case ev @ ANil() => APair.of[A ==> ?, ? ==> B](fs.head, ev.subst[fs.Pivot ==> ?](id[fs.Pivot]()))
      case ACons(h, t) => APair.of[A ==> ?, ? ==> B](fs.head, Sequence(ACons1(h, t)))
    }

    def visit[R](v: Visitor[R]): R = v.caseSequence(fs)
  }
  case class Id[=>:[_,_], x[_,_], I, ->:[_,_], A]() extends FreeCCC[=>:, x, I, ->:, A, A] {
    def visit[R](v: Visitor[R]): R = v.caseId()
  }
  case class Fst[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, A x B, A] {
    def visit[R](v: Visitor[R]): R = v.caseFst[B]()
  }
  case class Snd[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, A x B, B] {
    def visit[R](v: Visitor[R]): R = v.caseSnd[A]()
  }
  case class Prod[=>:[_,_], x[_,_], I, ->:[_,_], A, B, C](f: FreeCCC[=>:, x, I, ->:, A, B], g: FreeCCC[=>:, x, I, ->:, A, C]) extends FreeCCC[=>:, x, I, ->:, A, B x C] {
    def visit[R](v: Visitor[R]): R = v.caseProd(f, g)
  }
  case class Terminal[=>:[_,_], x[_,_], I, ->:[_,_], A]() extends FreeCCC[=>:, x, I, ->:, A, I] {
    def visit[R](v: Visitor[R]): R = v.caseTerminal()
  }
  case class Curry[=>:[_,_], x[_,_], I, ->:[_,_], A, B, C](f: FreeCCC[=>:, x, I, ->:, A x B, C]) extends FreeCCC[=>:, x, I, ->:, A, B ->: C] {
    def visit[R](v: Visitor[R]): R = v.caseCurry(f)
  }
  case class Eval[=>:[_,_], x[_,_], I, ->:[_,_], A, B]() extends FreeCCC[=>:, x, I, ->:, (A ->: B) x A, B] {
    def visit[R](v: Visitor[R]): R = v.caseEval[A]()
  }

  trait Visitor[=>:[_,_], x[_,_], I, ->:[_,_], A, B, R] {
    def caseWrap(f: A =>: B): R
    def caseSequence(fs: AList1[FreeCCC[=>:, x, I, ->:, ?, ?], A, B]): R
    def caseId()(implicit ev: A === B): R
    def caseFst[A2]()(implicit ev: A === (B x A2)): R
    def caseSnd[A1]()(implicit ev: A === (A1 x B)): R
    def caseProd[B1, B2](f: FreeCCC[=>:, x, I, ->:, A, B1], g: FreeCCC[=>:, x, I, ->:, A, B2])(implicit ev: (B1 x B2) === B): R
    def caseTerminal()(implicit ev: I === B): R
    def caseCurry[B1, B2](f: FreeCCC[=>:, x, I, ->:, A x B1, B2])(implicit ev: (B1 ->: B2) === B): R
    def caseEval[A0]()(implicit ev: A === ((A0 ->: B) x A0)): R
  }
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

trait RecFunModule {
  type RecFun[A, B]

  def eval[A, B](f: RecFun[A, B], a: A): B
}

private[data] object RecFunImpl extends RecFunModule {

  trait AFixModule {
    type AFix[F[_[_, _], _, _], A, B]

    def fix  [F[_[_, _], _, _], A, B](f: F[RecFunImpl.AFix[F, ?, ?], A, B]):          AFix[F, A, B]
    def unfix[F[_[_, _], _, _], A, B](f:          AFix[F, A, B]       ): F[RecFunImpl.AFix[F, ?, ?], A, B]
  }

  object AFixImpl extends AFixModule {
    type AFix[F[_[_, _], _, _], A, B] = F[RecFunImpl.AFix[F, ?, ?], A, B]

    def fix  [F[_[_, _], _, _], A, B](f: F[RecFunImpl.AFix[F, ?, ?], A, B]):          AFix[F, A, B]        = f
    def unfix[F[_[_, _], _, _], A, B](f:          AFix[F, A, B]       ): F[RecFunImpl.AFix[F, ?, ?], A, B] = f
  }

  val AFix: AFixModule = AFixImpl
  type AFix[F[_[_, _], _, _], A, B] = AFix.AFix[F, A, B]

  type Fun[A, B] = FreeCCC[Function1, Tuple2, Unit, Function1, A, B]

  type Rec[=>:[_,_], A, B] = A =>: (A =>: B) =>: B

  type RecFunF[F[_,_], α, β] = FreeCCC[λ[(a, b) => Function1[a, b] \/ Rec[F, a, b]], Tuple2, Unit, F, α, β]
  type RecFun[A, B] = AFix[RecFunF, A, B]
  type =>:[A, B] = RecFun[A, B]
  type ->[A, B] = Function1[A, B] \/ Rec[RecFun, A, B]
  type ==>:[A, B] = FreeCCC[->, Tuple2, Unit, RecFun, A, B]

  def fix[A, B](f: A ==>: B): A =>: B = AFix.fix[RecFunF, A, B](f)
  def unfix[A, B](f: A =>: B): A ==>: B = AFix.unfix[RecFunF, A, B](f)

  def eval[A, B](f: A =>: B, a: A): B =
    EvalApp(a, f, Done[B](_)).run

  private sealed trait Evaluator[R] {
    final def run: R = Evaluator.run(this)
  }

  private case class Done[R](r: R) extends Evaluator[R]
  private case class FlatMap[A, B](a: Evaluator[A], f: A => Evaluator[B]) extends Evaluator[B]
  private case class EvalApp[A, B, R](a: A, φ: A =>: B, f: B => Evaluator[R]) extends Evaluator[R] {
    def step: Evaluator[R] = {
      val φ1 = AFix.unfix(φ)
      φ1.visit(new φ1.Visitor[Evaluator[R]] {
        import FreeCCC._

        override def caseWrap(ψ: A -> B) = ψ match {
          case -\/(g) => f(g(a))
          case \/-(ξ) => EvalApp[A, (A =>: B) =>: B, R](a, ξ, γ => EvalApp(φ, γ, f))
        }
        override def caseId()(implicit ev: A === B) = f(ev(a))
        override def caseFst[A2]()(implicit ev: A === (B, A2)) = f(ev(a)._1)
        override def caseSnd[A1]()(implicit ev: A === (A1, B)) = f(ev(a)._2)
        override def caseTerminal()(implicit ev: Unit === B) = f(ev(()))
        override def caseProd[B1, B2](σ: A ==>: B1, τ: A ==>: B2)(implicit ev: (B1, B2) === B) =
          EvalApp[A, B1, R](a, fix(σ), b1 => EvalApp[A, B2, R](a, fix(τ), b2 => f(ev((b1, b2)))))
        override def caseCurry[B1, B2](ψ: (A, B1) ==>: B2)(implicit ev: (B1 =>: B2) === B) =
          f(ev(fix(ψ compose Wrap[->, Tuple2, Unit, RecFun, B1, (A, B1)](-\/(b1 => (a, b1))))))
        override def caseEval[A0]()(implicit ev: A === (A0 =>: B, A0)) = {
          val (g, a0) = ev(a)
          EvalApp(a0, g, f)
        }
        override def caseSequence(φs: AList1[==>:, A, B]) = φs.tail match {
          case ev @ ANil() => EvalApp(a, fix(ev.subst[A ==>: ?](φs.head)), f)
          case ACons(h, t) => EvalApp(a, fix(φs.head), (x: φs.Pivot) => EvalApp(x, fix(Sequence(ACons1(h, t))), f))
        }
      })
    }
  }

  private object Evaluator {
    @annotation.tailrec
    final def run[R](e: Evaluator[R]): R = e match {
      case Done(r) => r
      case FlatMap(a, f) => a match {
        case Done(a) => run(f(a))
        case FlatMap(a, g) => run(FlatMap(a, g andThen f))
        case EvalApp(a, φ, g) => run(EvalApp(a, φ, g andThen f))
      }
      case e @ EvalApp(_, _, _) => run(e.step)
    }
  }
}
