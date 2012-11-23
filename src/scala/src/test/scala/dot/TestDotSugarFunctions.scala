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

  def testApp() = App(Var(f), Var(x)) match {
    case App(t1, t2) =>
      expect(Var(f))(t1)
      expect(Var(x))(t2)
  }
  def testLambdaType() = LambdaType(Bottom, Top) match {
    case LambdaType(ty1, ty2) =>
      expect(Bottom)(ty1)
      expect(Top)(ty2)
  }
  def testCast() = Cast(Var(x), Top) match {
    case Cast(t, ty) =>
      expect(Var(x))(t)
      expect(Top)(ty)
  }
}

@RunWith(classOf[JUnitRunner])
class TestDotParserWithSugarFunctions extends TestDotParser with DotSugarFunctions {
  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val y = Name("y")

  def testLambda1() = {
    ok(Parser.term, Some(Lambda(Top, x\\Var(x))))("\\x:Top.x")
  }
  def testLambda1a() = {
    ok(Parser.term, Some(Lambda(Top, x\\Var(x))))("(\\x:Top.x)")
  }
  def testLambda2() = {
    ok(Parser.term, Some(Lambda(Top, x\\Var(x))))("λx:Top.x")
  }
  def testLambda3() {
    ok(Parser.term, Some(Lambda(Top, x\\Lambda(Top, y\\Var(x)))))("λx:Top.λy:Top.x")
  }
  def testCast1() = {
    ok(Parser.term, Some(Cast(Lambda(Top, x\\Var(x)), Top)))("(\\x:Top.x):Top")
  }
  def testCast2() = {
    ok(Parser.term, Some(Cast(Cast(Lambda(Top, x\\Var(x)), Top), Top)))("(\\x:Top.x):Top:Top")
  }
  def testApp1() = {
    ok(Parser.term, Some(App(Lambda(Top, x\\Var(x)), Lambda(Top, x\\Var(x)))))("(\\x:Top.x) \\x:Top.x")
  }
  def testApp2() = {
    ok(Parser.term, Some(Lambda(Top, x\\App(Var(x), Lambda(Top, x\\Var(x))))))("\\x:Top.x \\x:Top.x")
  }
  def testApp3() = {
    ok(Parser.term, Some(App(App(Lambda(Top, x\\Var(x)), Lambda(Top, x\\Var(x))), Lambda(Top, x\\Var(x)))))("(\\x:Top.x) (\\x:Top.x) (\\x:Top.x)")
  }
  def testLambdaType1() = {
    ok(Parser.typ, Some(LambdaType(Top, Top)))("Top => Top")
  }
  def testLambdaType2() = {
    ok(Parser.typ, Some(LambdaType(Top, LambdaType(Top, Top))))("Top => Top => Top")
  }
}

@RunWith(classOf[JUnitRunner])
class TestDotPrettyPrinterWithSugarFunctions extends TestDotPrettyPrinter with DotSugarFunctions {
  def testLambda1() = {
    ok("λx:⊤.x")
  }
  def testApp1() = {
    ok("(λx:⊤.x) (λx:⊤.x)")
  }
  def testApp2() = {
    ok("(λx:⊤.x) (λx:⊤.x) (λx:⊤.x)")
  }
  def testApp3() = {
    ok("(λx:⊤.x) ((λx:⊤.x) (λx:⊤.x))")
  }
  def testCast1() = {
    ok("(λx:⊤.x):(⊤)")
  }
  def testLambdaType1() = {
    ok("(λx:⊤.x):(⊤ ⇒ ⊤)")
  }
  def testLambdaType2() = {
    ok("(λx:⊤.λx:⊤.x):(⊤ ⇒ ⊤ ⇒ ⊤)")
  }
  def testLambdaType3() = {
    ok("(λx:⊤ ⇒ ⊤.x):((⊤ ⇒ ⊤) ⇒ ⊤)")
  }
  def testAll1() = {
    ok("(λf:⊤ ⇒ ⊤.λx:⊤.f x) (λx:⊤.x) (λx:⊤.x)")
  }
}

@RunWith(classOf[JUnitRunner])
class TestDotTyperWithSugarFunctions extends TestDotTyper with DotSugarFunctions {
}

@RunWith(classOf[JUnitRunner])
class TestDotWithSugarFunctions extends TestDot with DotSugarFunctions {
  import Types._

  def testLambda1() = expect(LambdaType(Top, Top)){check("\\x:Top.x")}
  def testLambda2() = expect(LambdaType(LambdaType(Top,Top),Top)){check("\\f:Top=>Top.f f")}
  def testCast1() = expect(Top){check("(\\x:Top.x):Top")}
}

@RunWith(classOf[JUnitRunner])
class TestDotShellWithSugar extends TestDotShell with DotShellWithSugar { sh =>
  def testLambda1() = ok(List(
      ("λx:Top.x", "===> λx:⊤.x : ⊤ ⇒ ⊤"),
      ("(λx:Top.x) (λx:Top.x)", "===> (λx:⊤.x) (λx:⊤.x) : ⊤"),
      ("(λx:Top=>Top.x) (λx:Top.x)", "===> (λx:⊤ ⇒ ⊤.x) (λx:⊤.x) : ⊤ ⇒ ⊤")))
}