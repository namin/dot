package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotSyntax extends Suite with DotNominalSyntax {
  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")
  val z = Name("z")

  def testAlphaEquivalence() = {
    expect(false)(Var(x) == Var(y))
    expect(true)(New(Top, x\\(Defs(List()), Var(x))) == New(Top, z\\(Defs(List()), Var(z))))
    expect(true)(Refine(Top, x\\(Decls(List()))) == Refine(Top, z\\Decls(List())))

    expect(true)(
      New(Top, x\\(Defs(List(MethodDef(MethodLabel("m"), Method(y\\Msel(Var(x), MethodLabel("m"), Var(y)))))), Var(z)))
      ==
      New(Top, y\\(Defs(List(MethodDef(MethodLabel("m"), Method(x\\Msel(Var(y), MethodLabel("m"), Var(x)))))), Var(z))))

    expect(false)(
      New(Top, x\\(Defs(List(MethodDef(MethodLabel("m"), Method(y\\Msel(Var(x), MethodLabel("m"), Var(y)))))), Var(z)))
      ==
      New(Top, z\\(Defs(List(MethodDef(MethodLabel("m"), Method(x\\Msel(Var(z), MethodLabel("m"), Var(x)))))), Var(z))))
  }
}
