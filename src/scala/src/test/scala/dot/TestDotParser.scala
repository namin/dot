package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotParser extends FunSuite with DotParsing {
  import Terms._
  import Types._
  import Members._
  
  def parse[T](p: Parser[T])(in: String) = phrase(p)(new lexical.Scanner(in))

  def ok[T](p: Parser[T], expected: Option[T] = None)(in: String) = parse(p)(in) match {
    case Success(actual, _) => expected.foreach(e => expectResult(e)(actual))
    case _@r => fail("expected success, got " + r)
  }
  def bad[T](p: Parser[T], expectedMsg: Option[String] = None)(in: String) = parse(p)(in) match {
    case Failure(msg, _) => expectedMsg.foreach(e => expectResult(e)(msg))
    case _@r => fail("expected failure, got " + r)
  }
    
  test("ValueLabel1") { ok(Parser.valueLabel, Some(ValueLabel("foo")))("foo") }
  test("ValueLabelBad1") { bad(Parser.valueLabel, Some("value label should start with a lower case, unlike Foo"))("Foo") }

  test("New1") { ok(Parser.term)("val x = new Top; x") }
  test("New2") { ok(Parser.term)("val x = new Top\nx") }
  test("New3") { ok(Parser.term)("val x = new Top(); x") }
  test("New4") { ok(Parser.term)("val x = new Top(l=x); x") }
  test("New5") { ok(Parser.term)("val x = new Top(l=x; m(x)=x); x") }
  test("New6") { ok(Parser.term)("val x = new Top(l=x; m(x)=(val y = new Top; x)); x") }
  test("NewBad1") { bad(Parser.term, Some("expected concrete type, unlike ⊥"))("val x = new Bot; x") }

  test("Sel1") { ok(Parser.term)("val x = new Top; x.l") }
  test("Sel2") { ok(Parser.term)("val x = new Top; x.a.b") }

  test("Msel1") { ok(Parser.term)("val x = new Top; x.m(x)") }
  test("Msel2") { ok(Parser.term)("val x = new Top; x.a.b(x.a)") }

  test("Intersection1") { ok(Parser.typ)("Top & Top") }
  test("Union1") { ok(Parser.typ)("Top | Top") }
  test("TypeGrouping1") { ok(Parser.typ, Some(Union(Intersect(Top, Top), Top)))("Top & Top | Top") }
  test("TypeGrouping2") { ok(Parser.typ, Some(Union(Top, Intersect(Top, Top))))("Top | Top & Top") }
  
  test("ConcreteType1") { ok(Parser.concrete_typ)("Top") }
  test("ConcreteType2") { ok(Parser.concrete_typ)("Top & Top") }
  test("ConcreteTypeBad1") { bad(Parser.concrete_typ, Some("expected concrete type, unlike ⊤ ∨ ⊤"))("Top | Top") }

  test("Refine1") { ok(Parser.typ)("Top { z => }") }
  test("Refine2") { ok(Parser.typ)(
      """
      Top { z =>
         L: Bottom..Top
        !L: Bottom..Top
         m: Top -> Top
         l: Top
      }
      """
  )}
  test("Refine3") { ok(Parser.typ)("Top { z => a: Top; b: Top { z => c: Top } }") }

  val tyr = Refine(Top, Name("z")\\(Decls(List())))
  test("TypeGrouping3") { ok(Parser.typ, Some(Union(Intersect(tyr,tyr),tyr)))("Top { z => } & Top { z => } | Top { z => }") }
  test("TypeGrouping4") { ok(Parser.typ, Some(Union(Intersect(tyr,Top),Top)))("Top { z => } & Top | Top") }

  test("UniqLabels1") { bad(Parser.term, Some("duplicate definition"))("val x = new Top(l=x;l=x); x") }
  test("UniqLabels2") { bad(Parser.typ, Some("duplicate declaration"))("Top { z => l: Top; l: Top }") }

  test("1") { ok(Parser.term)(
      """
      val x = new ⊤ { x ⇒
        !L : ⊥..⊤
         L : ⊥..⊤
      }
      val y = new x.!L
      val id = new ⊤ { id ⇒
        apply : ⊤→⊤
      }(apply(x)=x)
      id.apply(y)
      """)
  }
}
