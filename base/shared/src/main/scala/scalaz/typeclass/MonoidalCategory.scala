package scalaz
package typeclass

trait MonoidalCategoryClass[=>:[_,_], x[_,_], I] extends CategoryClass[=>:] {
  def parallel[A, B, C, D](f: A =>: B, g: C =>: D): (A x C) =>: (B x D)
  def assocLR[A, B, C]: ((A x B) x C) =>: (A x (B x C))
  def assocRL[A, B, C]: (A x (B x C)) =>: ((A x B) x C)
  def addUnitL[A]: A =>: (I x A)
  def addUnitR[A]: A =>: (A x I)
  def elimUnitL[A]: (I x A) =>: A
  def elimUnitR[A]: (A x I) =>: A

  override def dual: MonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] =
    new MonoidalCategoryClass.Dual[=>:, x, I] {
      def primal = MonoidalCategoryClass.this
    }
}

object MonoidalCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I]
  extends CategoryClass.Dual[=>:]
  with MonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] {
    override def primal: MonoidalCategoryClass[=>:, x, I]
    override def dual = primal

    def addUnitL[A]: (I x A) =>: A = primal.elimUnitL
    def addUnitR[A]: (A x I) =>: A = primal.elimUnitR
    def assocLR[A, B, C]: (A x (B x C)) =>: ((A x B) x C) = primal.assocRL
    def assocRL[A, B, C]: ((A x B) x C) =>: (A x (B x C)) = primal.assocLR
    def elimUnitL[A]: A =>: (I x A) = primal.addUnitL
    def elimUnitR[A]: A =>: (A x I) = primal.addUnitR
    def parallel[A, B, C, D](f: B =>: A, g: D =>: C): (B x D) =>: (A x C) = primal.parallel(f, g)
  }
}

trait BraidedMonoidalCategoryClass[=>:[_,_], x[_,_], I] extends MonoidalCategoryClass[=>:, x, I] {
  def twist[A, B]: (A x B) =>: (B x A)
  def untwist[A, B]: (B x A) =>: (A x B)

  override def dual: BraidedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] =
    new BraidedMonoidalCategoryClass.Dual[=>:, x, I] {
      def primal = BraidedMonoidalCategoryClass.this
    }
}

object BraidedMonoidalCategoryClass {
  trait Dual[=>:[_,_], x[_,_], I]
  extends MonoidalCategoryClass.Dual[=>:, x, I]
  with BraidedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] {
    override def primal: BraidedMonoidalCategoryClass[=>:, x, I]
    override def dual = primal

    def twist[A, B]: (B x A) =>: (A x B) = primal.untwist
    def untwist[A, B]: (A x B) =>: (B x A) = primal.twist
  }
}

trait SymmetricMonoidalCategoryClass[=>:[_,_], x[_,_], I] extends BraidedMonoidalCategoryClass[=>:, x, I] {
  def flip[A, B]: (A x B) =>: (B x A)

  override def twist[A, B]: (A x B) =>: (B x A) = flip[A, B]
  override def untwist[A, B]: (B x A) =>: (A x B) = flip[B, A]

  override def dual: SymmetricMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] =
    new SymmetricMonoidalCategoryClass.Dual[=>:, x, I] {
      def primal = SymmetricMonoidalCategoryClass.this
    }
}

object SymmetricMonoidalCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I]
  extends BraidedMonoidalCategoryClass.Dual[=>:, x, I]
  with SymmetricMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] {
    override def primal: SymmetricMonoidalCategoryClass[=>:, x, I]
    override def dual = primal

    def flip[A, B]: (B x A) =>: (A x B) = primal.flip
  }
}

trait ClosedMonoidalCategoryClass[=>:[_,_], x[_,_], I, ->:[_,_]] extends MonoidalCategoryClass[=>:, x, I] {
  def curry[A, B, C](f: (A x B) =>: C): A =>: (B ->: C)
  def eval[A, B]: ((A ->: B) x A) =>: B

  def uncurry[A, B, C](f: A =>: (B ->: C)): (A x B) =>: C =
    compose(eval[B, C], parallel(f, id[B]))

  override def dual: CoclosedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I, ->:] =
    new ClosedMonoidalCategoryClass.Dual[=>:, x, I, ->:] {
      def primal = ClosedMonoidalCategoryClass.this
    }
}

object ClosedMonoidalCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, ->:[_,_]]
  extends MonoidalCategoryClass.Dual[=>:, x, I]
  with CoclosedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I, ->:] {
    override def primal: ClosedMonoidalCategoryClass[=>:, x, I, ->:]
    override def dual = primal

    def cocurry[A, B, C](f: (A x B) =>: C): A =>: B ->: C = primal.curry(f)
    def coeval[A, B]: ((A ->: B) x A) =>: B = primal.eval
  }
}

trait CoclosedMonoidalCategoryClass[=>:[_,_], v[_,_], O, <-:[_,_]] extends MonoidalCategoryClass[=>:, v, O] {
  def cocurry[A, B, C](f: C =>: (A v B)): (B <-: C) =>: A
  def coeval[A, B]: B =>: ((A <-: B) v A)

  def councurry[A, B, C](f: (B <-: C) =>: A): C =>: (A v B) =
    andThen(coeval[B, C], parallel(f, id[B]))

  override def dual: ClosedMonoidalCategoryClass[λ[(a, b) => b =>: a], v, O, <-:] =
    new CoclosedMonoidalCategoryClass.Dual[=>:, v, O, <-:] {
      def primal = CoclosedMonoidalCategoryClass.this
    }
}

object CoclosedMonoidalCategoryClass {

  trait Dual[=>:[_,_], v[_,_], O, <-:[_,_]]
  extends MonoidalCategoryClass.Dual[=>:, v, O]
  with ClosedMonoidalCategoryClass[λ[(a, b) => b =>: a], v, O, <-:] {
    override def primal: CoclosedMonoidalCategoryClass[=>:, v, O, <-:]
    override def dual = primal

    def curry[A, B, C](f: C =>: (A v B)): (B <-: C) =>: A = primal.cocurry(f)
    def eval[A, B]: B =>: ((A <-: B) v A) = primal.coeval
  }
}

trait TracedMonoidalCategoryClass[=>:[_,_], x[_,_], I] extends SymmetricMonoidalCategoryClass[=>:, x, I] {
  def tr[X, A, B](f: (A x X) =>: (B x X)): A =>: B

  override def dual: TracedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] =
    new TracedMonoidalCategoryClass.Dual[=>:, x, I] {
      def primal = TracedMonoidalCategoryClass.this
    }
}

object TracedMonoidalCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I]
  extends SymmetricMonoidalCategoryClass.Dual[=>:, x, I]
  with TracedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I] {
    override def primal: TracedMonoidalCategoryClass[=>:, x, I]
    override def dual = primal

    def tr[X, A, B](f: (B x X) =>: (A x X)): B =>: A = primal.tr(f)
  }
}

/** Category with looping only at types that satisfy the constraint `P`. */
trait ConstrTracedMonoidalCategoryClass[=>:[_,_], x[_,_], I, P[_]] extends SymmetricMonoidalCategoryClass[=>:, x, I] {
  def tr[X: P, A, B](f: (A x X) =>: (B x X)): A =>: B

  override def dual: ConstrTracedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I, P] =
    new ConstrTracedMonoidalCategoryClass.Dual[=>:, x, I, P] {
      def primal = ConstrTracedMonoidalCategoryClass.this
    }
}

object ConstrTracedMonoidalCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, P[_]]
  extends SymmetricMonoidalCategoryClass.Dual[=>:, x, I]
     with ConstrTracedMonoidalCategoryClass[λ[(a, b) => b =>: a], x, I, P] {

    override def primal: ConstrTracedMonoidalCategoryClass[=>:, x, I, P]
    override def dual = primal

    def tr[X: P, A, B](f: x[B,X] =>: x[A,X]): B =>: A = primal.tr(f)
  }
}

/** Category with finite products. */
trait CartesianCategoryClass[=>:[_,_], x[_,_], I] extends CategoryClass[=>:] {
  def prod[A, B, C](f: A =>: B, g: A =>: C): A =>: (B x C)
  def fst[A, B]: (A x B) =>: A
  def snd[A, B]: (A x B) =>: B
  def terminal[A]: A =>: I

  def times[A, B, C, D](f: A =>: B, g: C =>: D): (A x C) =>: (B x D) =
    prod(compose(f, fst), compose(g, snd))

  /** Returns the monoidal structure of categorical product.
    * This class does not extend [[SymmetricMonoidalCategoryClass]] directly,
    * because it is common for a subclass to have multiple monoidal structures.
    */
  def productMonoidalStructure: SymmetricMonoidalCategoryClass[=>:, x, I] =
    new MonoidalFromCartesian(this)

  override def dual: CocartesianCategoryClass[λ[(a, b) => b =>: a], x, I] =
    new CartesianCategoryClass.Dual[=>:, x, I] {
      def primal = CartesianCategoryClass.this
    }
}

object CartesianCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I]
  extends CategoryClass.Dual[=>:]
  with CocartesianCategoryClass[λ[(a, b) => b =>: a], x, I] {
    override def primal: CartesianCategoryClass[=>:, x, I]
    override def dual = primal

    def sum[A, B, C](f: C =>: A, g: C =>: B): C =>: (A x B) = primal.prod(f, g)
    def inl[A, B]: (A x B) =>: A = primal.fst
    def inr[A, B]: (A x B) =>: B = primal.snd
    def initial[A]: A =>: I = primal.terminal
  }
}

class MonoidalFromCartesian[=>:[_,_], x[_,_], I](C: CartesianCategoryClass[=>:, x, I])
extends SymmetricMonoidalCategoryClass[=>:, x, I] {
  override def compose[A, B, C](f: B =>: C, g: A =>: B): A =>: C = C.compose(f, g)

  override def id[A]: A =>: A = C.id[A]

  override def parallel[A, B, C, D](f: A =>: B, g: C =>: D): (A x C) =>: (B x D) = C.times(f, g)

  override def assocLR[A, B, C]: ((A x B) x C) =>: (A x (B x C)) =
    C.prod(compose(C.fst[A, B], C.fst), C.prod(compose(C.snd[A, B], C.fst), C.snd))

  override def assocRL[A, B, C]: (A x (B x C)) =>: ((A x B) x C) =
    C.prod(C.prod(C.fst, compose(C.fst[B, C], C.snd)), compose(C.snd[B, C], C.snd))

  override def addUnitL[A]: A =>: (I x A) = C.prod(C.terminal, id)

  override def addUnitR[A]: A =>: (A x I) = C.prod(id, C.terminal)

  override def elimUnitL[A]: (I x A) =>: A = C.snd

  override def elimUnitR[A]: (A x I) =>: A = C.fst

  override def flip[A, B]: (A x B) =>: (B x A) = C.prod(C.snd, C.fst)
}

/** Category with finite products and a parameterized fixed point operator. */
trait PFixCategoryClass[=>:[_,_], x[_,_], I] extends CartesianCategoryClass[=>:, x, I] {
  /** Parameterized fixed-point operator. */
  def pfix[A, X](f: (A x X) =>: X): A =>: X

  /** Parameterized fixed point operator in a cartesian monoidal category
    * is equivalent to a trace.
    */
  def pfixTr[X, A, B](f: (A x X) =>: (B x X)): A =>: B =
    andThen(andThen(prod(id[A], pfix[A, X](andThen(f, snd[B, X]))), f), fst[B, X])

  /** Traced structure given by the parameterized fixed point operator. */
  def pfixTrace: TracedMonoidalCategoryClass[=>:, x, I] =
    new TracedFromPFix(this)

  override def dual: WhileCategoryClass[λ[(a, b) => b =>: a], x, I] =
    new PFixCategoryClass.Dual[=>:, x, I] {
      def primal = PFixCategoryClass.this
    }
}

object PFixCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I]
  extends CartesianCategoryClass.Dual[=>:, x, I]
  with WhileCategoryClass[λ[(a, b) => b =>: a], x, I] {
    override def primal: PFixCategoryClass[=>:, x, I]
    override def dual = primal

    def doWhile[X, A](f: (A x X) =>: X): A =>: X = primal.pfix(f)
  }
}

class TracedFromPFix[=>:[_,_], x[_,_], I](C: PFixCategoryClass[=>:, x, I])
extends MonoidalFromCartesian[=>:, x, I](C) with TracedMonoidalCategoryClass[=>:, x, I] {
  def tr[X, A, B](f: (A x X) =>: (B x X)): A =>: B = C.pfixTr(f)
}

/** Category with parameterized fixed point only at types that satisfy the constraint `P`. */
trait ConstrPFixCategoryClass[=>:[_,_], x[_,_], I, P[_]] extends CartesianCategoryClass[=>:, x, I] {
  /** Parameterized fixed-point operator. */
  def pfix[A, X: P](f: (A x X) =>: X): A =>: X

  def pfixTr[X: P, A, B](f: (A x X) =>: (B x X)): A =>: B =
    andThen(andThen(prod(id[A], pfix[A, X](andThen(f, snd[B, X]))), f), fst[B, X])
}

/** Category with finite coproducts. */
trait CocartesianCategoryClass[=>:[_,_], v[_,_], O] extends CategoryClass[=>:] {
  def sum[A, B, C](f: A =>: C, g: B =>: C): (A v B) =>: C
  def inl[A, B]: A =>: (A v B)
  def inr[A, B]: B =>: (A v B)
  def initial[A]: O =>: A

  def plus[A, B, C, D](f: A =>: B, g: C =>: D): (A v C) =>: (B v D) =
    sum(compose(inl, f), compose(inr, g))

  /** Returns the monoidal structure of categorical coproduct.
    * This class does not extend [[SymmetricMonoidalCategoryClass]] directly,
    * because it is common for a subclass to have multiple monoidal structures.
    */
  def coproductMonoidalStructure: SymmetricMonoidalCategoryClass[=>:, v, O] =
    new MonoidalFromCocartesian(this)

  override def dual: CartesianCategoryClass[λ[(a, b) => b =>: a], v, O] =
    new CocartesianCategoryClass.Dual[=>:, v, O] {
      def primal = CocartesianCategoryClass.this
    }
}

object CocartesianCategoryClass {

  trait Dual[=>:[_,_], v[_,_], O]
  extends CategoryClass.Dual[=>:]
  with CartesianCategoryClass[λ[(a, b) => b =>: a], v, O] {
    override def primal: CocartesianCategoryClass[=>:, v, O]
    override def dual = primal

    def prod[A, B, C](f: B =>: A, g: C =>: A): (B v C) =>: A = primal.sum(f, g)
    def fst[A, B]: A =>: (A v B) = primal.inl
    def snd[A, B]: B =>: (A v B) = primal.inr
    def terminal[A]: O =>: A = primal.initial
  }
}

class MonoidalFromCocartesian[=>:[_,_], v[_,_], O](C: CocartesianCategoryClass[=>:, v, O])
extends SymmetricMonoidalCategoryClass[=>:, v, O] {
  override def compose[A, B, C](f: B =>: C, g: A =>: B): A =>: C = C.compose(f, g)

  override def id[A]: A =>: A = C.id[A]

  override def parallel[A, B, C, D](f: A =>: B, g: C =>: D): (A v C) =>: (B v D) = C.plus(f, g)

  override def assocLR[A, B, C]: ((A v B) v C) =>: (A v (B v C)) =
    C.sum(C.sum(C.inl, compose(C.inr, C.inl[B, C])), compose(C.inr, C.inr[B, C]))

  override def assocRL[A, B, C]: (A v (B v C)) =>: ((A v B) v C) =
    C.sum(compose(C.inl, C.inl[A, B]), C.sum(compose(C.inl, C.inr[A, B]), C.inr))

  override def addUnitL[A]: A =>: (O v A) = C.inr

  override def addUnitR[A]: A =>: (A v O) = C.inl

  override def elimUnitL[A]: (O v A) =>: A = C.sum(C.initial, id)

  override def elimUnitR[A]: (A v O) =>: A = C.sum(id, C.initial)

  override def flip[A, B]: (A v B) =>: (B v A) = C.sum(C.inr, C.inl)
}

/** Category with finite coproducts and a "do-while loop". */
trait WhileCategoryClass[=>:[_,_], v[_,_], O] extends CocartesianCategoryClass[=>:, v, O] {
  /** Returns a "function" that keeps applying `f` while the result is `X`
    * and stops when the result is `A`.
    */
  def doWhile[X, A](f: X =>: (A v X)): X =>: A

  /** do-while in a cocartesian monoidal category is equivalent to a trace.  */
  def whileTr[X, A, B](f: (A v X) =>: (B v X)): A =>: B =
    andThen(inl[A, X], doWhile[A v X, B](andThen(f, plus(id[B], inr[A, X]))))

  /** Traced structure given by the do-while loop. */
  def whileTrace: TracedMonoidalCategoryClass[=>:, v, O] =
    new TracedFromWhile(this)

  override def dual: PFixCategoryClass[λ[(a, b) => b =>: a], v, O] =
    new WhileCategoryClass.Dual[=>:, v, O] {
      def primal = WhileCategoryClass.this
    }
}

object WhileCategoryClass {

  trait Dual[=>:[_,_], v[_,_], O]
  extends CocartesianCategoryClass.Dual[=>:, v, O]
  with PFixCategoryClass[λ[(a, b) => b =>: a], v, O] {
    override def primal: WhileCategoryClass[=>:, v, O]
    override def dual = primal

    def pfix[A, X](f: X =>: (A v X)): X =>: A = primal.doWhile(f)
  }
}

class TracedFromWhile[=>:[_,_], v[_,_], O](C: WhileCategoryClass[=>:, v, O])
extends MonoidalFromCocartesian[=>:, v, O](C) with TracedMonoidalCategoryClass[=>:, v, O] {
  def tr[X, A, B](f: (A v X) =>: (B v X)): A =>: B = C.whileTr(f)
}

/** Category with finite products and finite coproducts. */
trait BiCartesianCategoryClass[=>:[_,_], x[_,_], I, v[_,_], O]
  extends CartesianCategoryClass[=>:, x, I]
     with CocartesianCategoryClass[=>:, v, O] {

  override def dual: BiCartesianCategoryClass[λ[(a, b) => b =>: a], v, O, x, I] =
    new BiCartesianCategoryClass.Dual[=>:, x, I, v, O] {
      def primal = BiCartesianCategoryClass.this
    }
}

object BiCartesianCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, v[_,_], O]
  extends CartesianCategoryClass.Dual[=>:, x, I]
     with CocartesianCategoryClass.Dual[=>:, v, O]
     with BiCartesianCategoryClass[λ[(a, b) => b =>: a], v, O, x, I] {
    override def primal: BiCartesianCategoryClass[=>:, x, I, v, O]
    override def dual = primal
  }
}

/** Category with finite products and exponentials ("higher-order functions"). */
trait CartesianClosedCategoryClass[=>:[_,_], x[_,_], I, ->:[_, _]]
  extends CartesianCategoryClass[=>:, x, I]
     with ClosedMonoidalCategoryClass[=>:, x, I, ->:]
     with SymmetricMonoidalCategoryClass[=>:, x, I] {

  override def productMonoidalStructure = this
  override def dual: CocartesianCoclosedCategoryClass[λ[(a, b) => b =>: a], x, I, ->:] =
    new CartesianClosedCategoryClass.Dual[=>:, x, I, ->:] {
      def primal = CartesianClosedCategoryClass.this
    }
}

object CartesianClosedCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, ->:[_, _]]
  extends CartesianCategoryClass.Dual[=>:, x, I]
     with ClosedMonoidalCategoryClass.Dual[=>:, x, I, ->:]
     with SymmetricMonoidalCategoryClass.Dual[=>:, x, I]
     with CocartesianCoclosedCategoryClass[λ[(a, b) => b =>: a], x, I, ->:] {
    override def primal: CartesianClosedCategoryClass[=>:, x, I, ->:]
    override def dual = primal
  }
}

/** Category with finite products, exponentials and a parameterized fixed point operator. */
trait PFixClosedCategoryClass[=>:[_,_], x[_,_], I, ->:[_,_]]
extends CartesianClosedCategoryClass[=>:, x, I, ->:]
   with TracedMonoidalCategoryClass[=>:, x, I]
   with PFixCategoryClass[=>:, x, I] {

  override def dual: WhileCoclosedCategoryClass[λ[(a, b) => b =>: a], x, I, ->:] =
    new PFixClosedCategoryClass.Dual[=>:, x, I, ->:] {
      def primal = PFixClosedCategoryClass.this
    }

  override def tr[X, A, B](f: (A x X) =>: (B x X)): (A =>: B) = pfixTr(f)
}

object PFixClosedCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, ->:[_,_]]
  extends CartesianClosedCategoryClass.Dual[=>:, x, I, ->:]
     with PFixCategoryClass.Dual[=>:, x, I]
     with WhileCoclosedCategoryClass[λ[(a, b) => b =>: a], x, I, ->:] {
    override def primal: PFixClosedCategoryClass[=>:, x, I, ->:]
    override def dual = primal
  }
}

trait CocartesianCoclosedCategoryClass[=>:[_,_], v[_,_], O, <-:[_, _]]
extends CocartesianCategoryClass[=>:, v, O]
   with CoclosedMonoidalCategoryClass[=>:, v, O, <-:]
   with SymmetricMonoidalCategoryClass[=>:, v, O] {

  override def coproductMonoidalStructure = this
  override def dual: CartesianClosedCategoryClass[λ[(a, b) => b =>: a], v, O, <-:] =
    new CocartesianCoclosedCategoryClass.Dual[=>:, v, O, <-:] {
      def primal = CocartesianCoclosedCategoryClass.this
    }
}

object CocartesianCoclosedCategoryClass {

  trait Dual[=>:[_,_], v[_,_], O, <-:[_, _]]
  extends CocartesianCategoryClass.Dual[=>:, v, O]
     with CoclosedMonoidalCategoryClass.Dual[=>:, v, O, <-:]
     with SymmetricMonoidalCategoryClass.Dual[=>:, v, O]
     with CartesianClosedCategoryClass[λ[(a, b) => b =>: a], v, O, <-:] {
    override def primal: CocartesianCoclosedCategoryClass[=>:, v, O, <-:]
    override def dual = primal
  }
}

trait WhileCoclosedCategoryClass[=>:[_,_], v[_,_], O, <-:[_,_]]
extends CocartesianCoclosedCategoryClass[=>:, v, O, <-:]
   with TracedMonoidalCategoryClass[=>:, v, O]
   with WhileCategoryClass[=>:, v, O] {

  override def dual: PFixClosedCategoryClass[λ[(a, b) => b =>: a], v, O, <-:] =
    new WhileCoclosedCategoryClass.Dual[=>:, v, O, <-:] {
      def primal = WhileCoclosedCategoryClass.this
    }

  override def tr[X, A, B](f: (A v X) =>: (B v X)): (A =>: B) = whileTr(f)
}

object WhileCoclosedCategoryClass {

  trait Dual[=>:[_,_], v[_,_], O, <-:[_,_]]
  extends CocartesianCoclosedCategoryClass.Dual[=>:, v, O, <-:]
     with WhileCategoryClass.Dual[=>:, v, O]
     with PFixClosedCategoryClass[λ[(a, b) => b =>: a], v, O, <-:] {

    override def primal: WhileCoclosedCategoryClass[=>:, v, O, <-:]
    override def dual = primal
  }
}

/** A category that is both cartesian closed and co-cartesian. */
trait BiCartesianClosedCategoryClass[=>:[_,_], x[_,_], I, v[_,_], O, ->:[_, _]]
  extends CartesianClosedCategoryClass[=>:, x, I, ->:]
     with BiCartesianCategoryClass[=>:, x, I, v, O] {

  override def dual: BiCartesianCoclosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, ->:] =
    new BiCartesianClosedCategoryClass.Dual[=>:, x, I, v, O, ->:] {
      def primal = BiCartesianClosedCategoryClass.this
    }
}

object BiCartesianClosedCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, v[_,_], O, ->:[_, _]]
  extends CartesianClosedCategoryClass.Dual[=>:, x, I, ->:]
     with BiCartesianCategoryClass.Dual[=>:, x, I, v, O]
     with BiCartesianCoclosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, ->:] {
    override def primal: BiCartesianClosedCategoryClass[=>:, x, I, v, O, ->:]
    override def dual = primal
  }
}

/** Category with finite products, finite coproducts, exponentials and a while loop. */
trait WhileCartesianClosedCategoryClass[=>:[_,_], x[_,_], I, v[_,_], O, ->:[_, _]]
extends BiCartesianClosedCategoryClass[=>:, x, I, v, O, ->:]
   with WhileCategoryClass[=>:, v, O] {

  override def dual: PFixCocartesianCoclosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, ->:] =
    new WhileCartesianClosedCategoryClass.Dual[=>:, x, I, v, O, ->:] {
      def primal = WhileCartesianClosedCategoryClass.this
    }
}

object WhileCartesianClosedCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, v[_,_], O, ->:[_, _]]
  extends BiCartesianClosedCategoryClass.Dual[=>:, x, I, v, O, ->:]
     with WhileCategoryClass.Dual[=>:, v, O]
     with PFixCocartesianCoclosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, ->:] {
    override def primal: WhileCartesianClosedCategoryClass[=>:, x, I, v, O, ->:]
    override def dual = primal
  }
}

/** A category that is both co-cartesian co-closed and cartesian. */
trait BiCartesianCoclosedCategoryClass[=>:[_,_], x[_,_], I, v[_,_], O, <-:[_, _]]
  extends CocartesianCoclosedCategoryClass[=>:, v, O, <-:]
     with BiCartesianCategoryClass[=>:, x, I, v, O] {

  override def dual: BiCartesianClosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, <-:] =
    new BiCartesianCoclosedCategoryClass.Dual[=>:, x, I, v, O, <-:] {
      def primal = BiCartesianCoclosedCategoryClass.this
    }
}

object BiCartesianCoclosedCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, v[_,_], O, <-:[_, _]]
  extends CocartesianCoclosedCategoryClass.Dual[=>:, v, O, <-:]
     with BiCartesianCategoryClass.Dual[=>:, x, I, v, O]
     with BiCartesianClosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, <-:] {
    override def primal: BiCartesianCoclosedCategoryClass[=>:, x, I, v, O, <-:]
    override def dual = primal
  }
}

trait PFixCocartesianCoclosedCategoryClass[=>:[_,_], x[_,_], I, v[_,_], O, <-:[_, _]]
extends BiCartesianCoclosedCategoryClass[=>:, x, I, v, O, <-:]
   with PFixCategoryClass[=>:, x, I] {

  override def dual: WhileCartesianClosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, <-:] =
    new PFixCocartesianCoclosedCategoryClass.Dual[=>:, x, I, v, O, <-:] {
      def primal = PFixCocartesianCoclosedCategoryClass.this
    }
}

object PFixCocartesianCoclosedCategoryClass {

  trait Dual[=>:[_,_], x[_,_], I, v[_,_], O, <-:[_, _]]
  extends BiCartesianCoclosedCategoryClass.Dual[=>:, x, I, v, O, <-:]
     with PFixCategoryClass.Dual[=>:, x, I]
     with WhileCartesianClosedCategoryClass[λ[(a, b) => b =>: a], v, O, x, I, <-:] {
    override def primal: PFixCocartesianCoclosedCategoryClass[=>:, x, I, v, O, <-:]
    override def dual = primal
  }
}
