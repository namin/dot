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

  val decls1 = Decls(List(
    TypeDecl(AbstractTypeLabel("L1"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("U1")))),
    TypeDecl(AbstractTypeLabel("L"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("U1")))),
    TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1'")), Tsel(Var(x), AbstractTypeLabel("U1'"))))))
  val decls2 = Decls(List(
    TypeDecl(AbstractTypeLabel("L2"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2")), Tsel(Var(x), AbstractTypeLabel("U2")))),
    TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2'")), Tsel(Var(x), AbstractTypeLabel("U2'")))),
    TypeDecl(AbstractTypeLabel("L"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2")), Tsel(Var(x), AbstractTypeLabel("U2"))))))

  def testMeet1() =
    expect {
      Decls(List(
	TypeDecl(AbstractTypeLabel("L"), TypeBounds(Union(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("S2"))),
						    Intersect(Tsel(Var(x), AbstractTypeLabel("U1")), Tsel(Var(x), AbstractTypeLabel("U2"))))),
	TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Union(Tsel(Var(x), AbstractTypeLabel("S1'")), Tsel(Var(x), AbstractTypeLabel("S2'"))),
						     Intersect(Tsel(Var(x), AbstractTypeLabel("U1'")), Tsel(Var(x), AbstractTypeLabel("U2'"))))),
        TypeDecl(AbstractTypeLabel("L1"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("U1")))),
        TypeDecl(AbstractTypeLabel("L2"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2")), Tsel(Var(x), AbstractTypeLabel("U2"))))))
    } {
      meet(decls1, decls2)
    }

  def testJoin1() =
    expect {
      Decls(List(
	TypeDecl(AbstractTypeLabel("L"), TypeBounds(Intersect(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("S2"))),
						    Union(Tsel(Var(x), AbstractTypeLabel("U1")), Tsel(Var(x), AbstractTypeLabel("U2"))))),
	TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Intersect(Tsel(Var(x), AbstractTypeLabel("S1'")), Tsel(Var(x), AbstractTypeLabel("S2'"))),
						     Union(Tsel(Var(x), AbstractTypeLabel("U1'")), Tsel(Var(x), AbstractTypeLabel("U2'")))))))
    } {
      join(decls1, decls2)
    }
}
