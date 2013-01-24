package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLooseDotTyper extends TestDotTyper with LooseDotTyper {
}

@RunWith(classOf[JUnitRunner])
class TestDotTyper extends FunSuite with DotTyper {
  def bad[A](r: Result[A]) {
    assert(r.isInstanceOf[TyperFailure[_]])
  }

  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")
  val z = Name("z")
  val nodefs = Defs(List())

  test("TC1") { expectResult(TyperSuccess(Top))(typecheck(New(Top,x\\(nodefs, Var(x))))) }

  test("TC2") {
    expectResult {
      TyperSuccess(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Bottom, Top))))))
    } {
      typecheck(New(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Bottom, Top))))), x\\(nodefs, Var(x))))
    }
  }

  test("TC2BadBounds") {
    expectResult {
      TyperFailure("⊤ is not a subtype of ⊥")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(TypeDecl(AbstractTypeLabel("L"), TypeBounds(Top, Bottom))))), x\\(nodefs, Var(x))))
    }
  }

  test("TC_Sel") {
    expectResult(TyperSuccess(Top))(typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Top)))), x\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(x), ValueLabel("l"))))))
  }

  test("TC_Sel_Bad") {
    expectResult {
      TyperFailure("undeclared ValueLabel(l')")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Top)))), x\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(x), ValueLabel("l'")))))
    }
  }

  test("TC_Sel_BadInit") {
    expectResult {
      TyperFailure("uninitialized value for label l")
    } {
      typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Top)))), x\\(nodefs, Sel(Var(x), ValueLabel("l")))))
    }
  }

  test("TC_Sel_BadInitTC") {
    bad(typecheck(New(Refine(Top, z\\Decls(List(ValueDecl(ValueLabel("l"), Bottom)))), x\\(Defs(List(ValueDef(ValueLabel("l"), Var(x)))), Sel(Var(x), ValueLabel("l"))))))
  }

  test("Tc_Msel1") {
    expectResult(TyperSuccess(Top))(typecheck(New(Refine(Top, z\\Decls(List(MethodDecl(MethodLabel("m"), ArrowType(Top, Top))))),
                                            z\\(Defs(List(MethodDef(MethodLabel("m"),
                                                                    Method(x\\Var(x))))),
                                        Msel(Var(z), MethodLabel("m"), Var(z))))))
  }

  test("Tc_Msel2") {
    expectResult(TyperSuccess(Top))(typecheck(New(Refine(Top, z\\Decls(List(MethodDecl(MethodLabel("m"), ArrowType(Top, Top))))),
                                            z\\(Defs(List(MethodDef(MethodLabel("m"),
                                                                    Method(x\\Msel(Var(z), MethodLabel("m"), Var(x)))))),
                                        Msel(Var(z), MethodLabel("m"), Var(z))))))
  }

  val decls1 = Decls(List(
    TypeDecl(AbstractTypeLabel("L1"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("U1")))),
    TypeDecl(AbstractTypeLabel("L"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("U1")))),
    TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S1'")), Tsel(Var(x), AbstractTypeLabel("U1'"))))))
  val decls2 = Decls(List(
    TypeDecl(AbstractTypeLabel("L2"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2")), Tsel(Var(x), AbstractTypeLabel("U2")))),
    TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2'")), Tsel(Var(x), AbstractTypeLabel("U2'")))),
    TypeDecl(AbstractTypeLabel("L"), TypeBounds(Tsel(Var(x), AbstractTypeLabel("S2")), Tsel(Var(x), AbstractTypeLabel("U2"))))))

  test("Meet1") {
    expectResult {
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
  }

  test("Join1") {
    expectResult {
      Decls(List(
        TypeDecl(AbstractTypeLabel("L"),  TypeBounds(Intersect(Tsel(Var(x), AbstractTypeLabel("S1")), Tsel(Var(x), AbstractTypeLabel("S2"))),
                                                     Union(Tsel(Var(x), AbstractTypeLabel("U1")), Tsel(Var(x), AbstractTypeLabel("U2"))))),
        TypeDecl(AbstractTypeLabel("L'"), TypeBounds(Intersect(Tsel(Var(x), AbstractTypeLabel("S1'")), Tsel(Var(x), AbstractTypeLabel("S2'"))),
                                                     Union(Tsel(Var(x), AbstractTypeLabel("U1'")), Tsel(Var(x), AbstractTypeLabel("U2'")))))))
    } {
      join(decls1, decls2)
    }
  }
}
