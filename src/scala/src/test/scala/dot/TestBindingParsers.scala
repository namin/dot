package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._
import util.parsing.combinator.{PackratParsers, ImplicitConversions}

trait LambdaParsing extends StdTokenParsers with BindingParsers with PackratParsers with LambdaNominalSyntax with ImplicitConversions { theParser =>
  type Tokens = StdLexical; val lexical = new StdLexical
  lexical.delimiters ++= List("\\",".", "(", ")")

  type P[T] = PackratParser[T]

  def l[T](p: => Parser[T])(name: String): P[T] = Parser{ in =>
    val r = p(in)
    r
  }
  def BindingParser(env: Map[String, Name]): BindingParser = new BindingParser(env)
  class BindingParser(env: Map[String, Name]) extends BindingParserCore(env) {
    lazy val termSingle: P[Term] = (
      l(bound(ident) ^^ {case x => Var(x)}) ("var") |
      l("\\" ~> bind(ident) >> {x => "." ~> under(x)(_.term)} ^^ {case abs => Lam(abs)}) ("lam") |
      l("(" ~> term <~ ")") ("paren")
    )
    lazy val term = chainl1(termSingle, l(success(App(_, _))) ("app"))
  }
  object Parser extends BindingParser(HashMap.empty)
}

@RunWith(classOf[JUnitRunner])
class TestBindingParsers extends Suite with LambdaParsing {
  def parse(in: String) = phrase(Parser.term)(new lexical.Scanner(in))

  val x = Name("x")
  val y = Name("y")
  val z = Name("z")

  def ok(expected: Term)(in: String) = parse(in) match {
    case Success(actual, _) => expect(expected)(actual)
    case _@r => fail("expected success, got " + r)
  }

  def bad(expectedMsg: String)(in: String) = parse(in) match {
    case Failure(msg, _) => expect(expectedMsg)(msg)
    case _@r => fail("expected failure, got " + r)
  }

  def testOK1() = ok(Lam(x\\Var(x)))("\\x.x")
  def testOK2() = ok(Lam(x\\Lam(y\\Var(x))))("\\x.\\y.x")
  def testOK3() = ok(Lam(x\\Lam(y\\App(Var(x), Var(y)))))("\\x.\\y.(x y)")
  def testOK4() = ok(Lam(x\\Lam(y\\App(App(Var(x), Var(y)), Var(x)))))("\\x.\\y.(x y) x")
  def testOK3a() = ok(Lam(x\\Lam(y\\App(Var(x), Var(y)))))("\\x.\\y.x y")
  def testOK4a() = ok(Lam(x\\Lam(y\\App(App(Var(x), Var(y)), Var(x)))))("\\x.\\y.x y x")

  def testBad1() = bad("Unbound variable: x")("x")
  def testBad2() = bad("Unbound variable: x")("\\y.x")
  def testBad3() = bad("Unbound variable: x")("(\\y.x) (\\x.x)")
}
