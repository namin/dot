package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotSyntax extends Suite with DotNominalSyntax with DotSubstitution {
  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")
  val z = Name("z")

  def testAlphaEquivalence() = {
    expectResult(false)(Var(x) == Var(y))
    expectResult(true)(New(Top, x\\(Defs(List()), Var(x))) == New(Top, z\\(Defs(List()), Var(z))))
    expectResult(true)(Refine(Top, x\\(Decls(List()))) == Refine(Top, z\\Decls(List())))

    expectResult(true)(
      New(Top, x\\(Defs(List(MethodDef(MethodLabel("m"), Method(y\\Msel(Var(x), MethodLabel("m"), Var(y)))))), Var(z)))
      ==
      New(Top, y\\(Defs(List(MethodDef(MethodLabel("m"), Method(x\\Msel(Var(y), MethodLabel("m"), Var(x)))))), Var(z))))

    expectResult(false)(
      New(Top, x\\(Defs(List(MethodDef(MethodLabel("m"), Method(y\\Msel(Var(x), MethodLabel("m"), Var(y)))))), Var(z)))
      ==
      New(Top, z\\(Defs(List(MethodDef(MethodLabel("m"), Method(x\\Msel(Var(z), MethodLabel("m"), Var(x)))))), Var(z))))
  }

  def testSubstitution() = {
    expectResult(Var(x))(Var(y) subst(y, Var(x)))
    expectResult {
      New(Top, z\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(z), ValueLabel("l"))))
    } {
      New(Top, y\\(Defs(List(ValueDef(ValueLabel("l"), Var(z)))), Sel(Var(y), ValueLabel("l")))) subst(z, Var(x))
    }
  }
}
