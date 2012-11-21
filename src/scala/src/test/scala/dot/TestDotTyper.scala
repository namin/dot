package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotTyper extends Suite with DotTyper {
  def bad[A](r: Result[A]) {
    assert(r.isInstanceOf[TyperFailure[A]])
  }

  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")
  val z = Name("z")
  val nodefs = Defs(List())

  def testTC1() = expect(TyperSuccess(Top))(typecheck(New(Top,x\\(nodefs, Var(x)))))

  def testTC2() =
    expect {
      TyperSuccess(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Bottom, Top))))))
    } {
      typecheck(New(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Bottom, Top))))), x\\(nodefs, Var(x))))
    }

  def testTC2BadBounds() =
    expect {
      TyperFailure("⊤ is not a subtype of ⊥")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Top, Bottom))))), x\\(nodefs, Var(x))))
    }

  def testTC_Sel() =
    expect(TyperSuccess(Top))(typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Top)))), x\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(x), ValueLabel("l"))))))

  def testTC_Sel_Bad() =
    expect {
      TyperFailure("undeclared label ValueLabel(l')")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Top)))), x\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(x), ValueLabel("l'")))))
    }

  def testTC_Sel_BadInit() =
    expect {
      TyperFailure("uninitialized value for label ValueLabel(l)")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Top)))), x\\(nodefs, Sel(Var(x), ValueLabel("l")))))
    }

  def testTC_Sel_BadInitTC() =
    bad(typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Bottom)))), x\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(x), ValueLabel("l"))))))

  def testTc_Msel1() =
    expect(TyperSuccess(Top))(typecheck(New(Refine(Top, z\\Decls(List(MethodDecl(MethodLabel("m"), ArrowType(Top, Top))))),
                                            z\\(Defs(List(MethodDef(MethodLabel("m"),
                                                                    Method(x\\Var(x))))),
                                        Msel(Var(z), MethodLabel("m"), Var(z))))))

  def testTc_Msel2() =
    expect(TyperSuccess(Top))(typecheck(New(Refine(Top, z\\Decls(List(MethodDecl(MethodLabel("m"), ArrowType(Top, Top))))),
                                            z\\(Defs(List(MethodDef(MethodLabel("m"),
                                                                    Method(x\\Msel(Var(z), MethodLabel("m"), Var(x)))))),
                                        Msel(Var(z), MethodLabel("m"), Var(z))))))

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
        TypeDecl(AbstractTypeLabel("L"),  TypeBounds(Union(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("S2"))),
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
        TypeDecl(AbstractTypeLabel("L"),  TypeBounds(Intersect(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("S2"))),
                                                     Union(Tsel(Var(x), AbstractTypeLabel("U1")), Tsel(Var(x), AbstractTypeLabel("U2"))))),
        TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Intersect(Tsel(Var(x), AbstractTypeLabel("S1'")), Tsel(Var(x), AbstractTypeLabel("S2'"))),
                                                     Union(Tsel(Var(x), AbstractTypeLabel("U1'")), Tsel(Var(x), AbstractTypeLabel("U2'")))))))
    } {
      join(decls1, decls2)
    }
}
