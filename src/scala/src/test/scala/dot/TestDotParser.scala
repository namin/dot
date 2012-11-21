package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotParser extends Suite with DotParsing {
  import Terms._
  import Types._
  import Members._
  
  def parse[T](p: Parser[T])(in: String) = phrase(p)(new lexical.Scanner(in))

  def ok[T](p: Parser[T], expected: Option[T] = None)(in: String) = parse(p)(in) match {
    case Success(actual, _) => expected.foreach(e => expect(e)(actual))
    case _@r => fail("expected success, got " + r)
  }
  def bad[T](p: Parser[T], expectedMsg: Option[String] = None)(in: String) = parse(p)(in) match {
    case Failure(msg, _) => expectedMsg.foreach(e => expect(e)(msg))
    case _@r => fail("expected failure, got " + r)
  }
    
  def testValueLabel1() = ok(Parser.valueLabel, Some(ValueLabel("foo")))("foo")
  def testValueLabelBad1() = bad(Parser.valueLabel, Some("value label should start with a lower case, unlike Foo"))("Foo")

  def testNew1() = ok(Parser.term)("val x = new Top; x")
  def testNew2() = ok(Parser.term)("val x = new Top\nx")
  def testNew3() = ok(Parser.term)("val x = new Top(); x")
  def testNew4() = ok(Parser.term)("val x = new Top(l=x); x")
  def testNew5() = ok(Parser.term)("val x = new Top(l=x; m(x)=x); x")
  def testNew6() = ok(Parser.term)("val x = new Top(l=x; m(x)=(val y = new Top; x)); x")
  def testNewBad1() = bad(Parser.term, Some("expected concrete type, unlike ⊥"))("val x = new Bot; x")

  def testSel1() = ok(Parser.term)("val x = new Top; x.l")
  def testSel2() = ok(Parser.term)("val x = new Top; x.a.b")

  def testMsel1() = ok(Parser.term)("val x = new Top; x.m(x)")
  def testMsel2() = ok(Parser.term)("val x = new Top; x.a.b(x.a)")

  def testIntersection1() = ok(Parser.typ)("Top & Top")
  def testUnion1() = ok(Parser.typ)("Top | Top")
  def testTypeGrouping1() = ok(Parser.typ, Some(Union(Intersect(Top, Top), Top)))("Top & Top | Top")
  def testTypeGrouping2() = ok(Parser.typ, Some(Union(Top, Intersect(Top, Top))))("Top | Top & Top")
  
  def testConcreteType1() = ok(Parser.concrete_typ)("Top")
  def testConcreteType2() = ok(Parser.concrete_typ)("Top & Top")
  def testConcreteTypeBad1() = bad(Parser.concrete_typ, Some("expected concrete type, unlike ⊤ ∨ ⊤"))("Top | Top")

  def testRefine1() = ok(Parser.typ)("Top { z => }")
  def testRefine2() = ok(Parser.typ)(
      """
      Top { z =>
         L: Bottom..Top
        !L: Bottom..Top
         m: Top -> Top
         l: Top
      }
      """
  )
  def testRefine3() = ok(Parser.typ)("Top { z => a: Top; b: Top { z => c: Top } }")

  val tyr = Refine(Top, Name("z")\\(Decls(List())))
  def testTypeGrouping3() = ok(Parser.typ, Some(Union(Intersect(tyr,tyr),tyr)))("Top { z => } & Top { z => } | Top { z => }")
  def testTypeGrouping4() = ok(Parser.typ, Some(Union(Intersect(tyr,Top),Top)))("Top { z => } & Top | Top")

  def testUniqLabels1() = bad(Parser.term, Some("duplicate definition"))("val x = new Top(l=x;l=x); x")
  def testUniqLabels2() = bad(Parser.typ, Some("duplicate declaration"))("Top { z => l: Top; l: Top }")

  def test1() = ok(Parser.term)(
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
