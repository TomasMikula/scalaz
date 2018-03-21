package scalaz
package typeclass

trait ComposeClass[=>:[_, _]] {
  def compose[A, B, C](f: B =>: C, g: A =>: B): (A =>: C)

  def andThen[A, B, C](f: A =>: B, g: B =>: C): (A =>: C) = compose(g, f)

  def dual: ComposeClass[λ[(a, b) => b =>: a]] =
    new ComposeClass.Dual[=>:] {
      def primal = ComposeClass.this
    }
}

object ComposeClass {
  trait Dual[=>:[_,_]] extends ComposeClass[λ[(a, b) => b =>: a]] {
    def primal: ComposeClass[=>:]
    override def dual = primal

    def compose[A, B, C](f: C =>: B, g: B =>: A): C =>: A = primal.compose(g, f)
  }
}
