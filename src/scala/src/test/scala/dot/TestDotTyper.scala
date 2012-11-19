package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotTyper extends Suite with DotTyper {
  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")
  val z = Name("z")
  val nodefs = Defs(List())

  def testTC1() = expect(Success(Top))(typecheck(New(Top,x\\(nodefs, Var(x)))))

  def testTC2() =
    expect {
      Success(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Bottom, Top))))))
    } {
      typecheck(New(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Bottom, Top))))), x\\(nodefs, Var(x))))
    }

  def testTC2BadBounds() =
    expect {
      Failure("Top is not a subtype of Bottom")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Top, Bottom))))), x\\(nodefs, Var(x))))
    }
}
