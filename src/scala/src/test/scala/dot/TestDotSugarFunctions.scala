package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotSyntaxWithSugarFunctions extends TestDotSyntax with DotSugarFunctions {
  import Terms._
  import Types._
  import Members._

  val f = Name("f")

  test("App") { App(Var(f), Var(x)) match {
    case App(t1, t2) =>
      expectResult(Var(f))(t1)
      expectResult(Var(x))(t2)
  }}
  test("LambdaType") { LambdaType(Bottom, Top) match {
    case LambdaType(ty1, ty2) =>
      expectResult(Bottom)(ty1)
      expectResult(Top)(ty2)
  }}
  test("Cast") { Cast(Var(x), Top) match {
    case Cast(t, ty) =>
      expectResult(Var(x))(t)
      expectResult(Top)(ty)
  }}
}

@RunWith(classOf[JUnitRunner])
class TestDotParserWithSugarFunctions extends TestDotParser with DotSugarFunctions {
  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")

  test("Lambda1") {
    ok(Parser.term, Some(Lambda(Top, x\\Var(x))))("\\x:Top.x")
  }
  test("Lambda1a") {
    ok(Parser.term, Some(Lambda(Top, x\\Var(x))))("(\\x:Top.x)")
  }
  test("Lambda2") {
    ok(Parser.term, Some(Lambda(Top, x\\Var(x))))("λx:Top.x")
  }
  test("Lambda3") {
    ok(Parser.term, Some(Lambda(Top, x\\Lambda(Top, y\\Var(x)))))("λx:Top.λy:Top.x")
  }
  test("Cast1") {
    ok(Parser.term, Some(Cast(Lambda(Top, x\\Var(x)), Top)))("(\\x:Top.x):Top")
  }
  test("Cast2") {
    ok(Parser.term, Some(Cast(Cast(Lambda(Top, x\\Var(x)), Top), Top)))("(\\x:Top.x):Top:Top")
  }
  test("App1") {
    ok(Parser.term, Some(App(Lambda(Top, x\\Var(x)), Lambda(Top, x\\Var(x)))))("(\\x:Top.x) \\x:Top.x")
  }
  test("App2") {
    ok(Parser.term, Some(Lambda(Top, x\\App(Var(x), Lambda(Top, x\\Var(x))))))("\\x:Top.x \\x:Top.x")
  }
  test("App3") {
    ok(Parser.term, Some(App(App(Lambda(Top, x\\Var(x)), Lambda(Top, x\\Var(x))), Lambda(Top, x\\Var(x)))))("(\\x:Top.x) (\\x:Top.x) (\\x:Top.x)")
  }
  test("LambdaType1") {
    ok(Parser.typ, Some(LambdaType(Top, Top)))("Top => Top")
  }
  test("LambdaType2") {
    ok(Parser.typ, Some(LambdaType(Top, LambdaType(Top, Top))))("Top => Top => Top")
  }
}

@RunWith(classOf[JUnitRunner])
class TestDotPrettyPrinterWithSugarFunctions extends TestDotPrettyPrinter with DotSugarFunctions {
  test("Lambda1") {
    ok("λx:⊤.x")
  }
  test("App1") {
    ok("(λx:⊤.x) (λx:⊤.x)")
  }
  test("App2") {
    ok("(λx:⊤.x) (λx:⊤.x) (λx:⊤.x)")
  }
  test("App3") {
    ok("(λx:⊤.x) ((λx:⊤.x) (λx:⊤.x))")
  }
  test("Cast1") {
    ok("(λx:⊤.x):(⊤)")
  }
  test("LambdaType1") {
    ok("(λx:⊤.x):(⊤ ⇒ ⊤)")
  }
  test("LambdaType2") {
    ok("(λx:⊤.λx:⊤.x):(⊤ ⇒ ⊤ ⇒ ⊤)")
  }
  test("LambdaType3") {
    ok("(λx:⊤ ⇒ ⊤.x):((⊤ ⇒ ⊤) ⇒ ⊤)")
  }
  test("All1") {
    ok("(λf:⊤ ⇒ ⊤.λx:⊤.f x) (λx:⊤.x) (λx:⊤.x)")
  }
}

@RunWith(classOf[JUnitRunner])
class TestDotTyperWithSugarFunctions extends TestDotTyper with DotSugarFunctions {
}

@RunWith(classOf[JUnitRunner])
class TestDotWithSugarFunctions extends TestDot with DotSugarFunctions {
  import Types._

  test("Lambda1") { expectResult(LambdaType(Top, Top)){check("\\x:Top.x")} }
  test("Lambda2") { expectResult(LambdaType(LambdaType(Top,Top),Top)){check("\\f:Top=>Top.f f")} }
  test("Cast1") { expectResult(Top){check("(\\x:Top.x):Top")} }
}

@RunWith(classOf[JUnitRunner])
class TestDotShellWithSugar extends TestDotShell with DotShellWithSugar { sh =>
  test("Lambda1") { ok(List(
      ("λx:Top.x", "===> λx:⊤.x : ⊤ ⇒ ⊤"),
      ("(λx:Top.x) (λx:Top.x)", "===> (λx:⊤.x) (λx:⊤.x) : ⊤"),
      ("(λx:Top=>Top.x) (λx:Top.x)", "===> (λx:⊤ ⇒ ⊤.x) (λx:⊤.x) : ⊤ ⇒ ⊤"))) }
}