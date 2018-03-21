package scalaz
package typeclass

trait CategoryClass[=>:[_, _]] extends ComposeClass[=>:] {
  def id[A]: A =>: A

  override def dual: CategoryClass[λ[(a, b) => b =>: a]] =
    new CategoryClass.Dual[=>:] {
      def primal = CategoryClass.this
    }
}

object CategoryClass {

  trait Dual[=>:[_,_]]
  extends ComposeClass.Dual[=>:]
  with CategoryClass[λ[(a, b) => b =>: a]] {
    override def primal: CategoryClass[=>:]
    override def dual = primal

    def id[A]: A =>: A = primal.id[A]
  }
}
