package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotShell extends Suite with DotShell { sh =>
  def ok(cmds: List[(String, String)]): Unit = cmds match {
    case Nil => ()
    case (in,out)::rest =>
      expect(out)(sh.tc(in))
      ok(rest)
  }

  def test1() = ok(List(
      ("val x = new Top", "<=== x : ⊤"),
      ("x", "===> x : ⊤"),
      ("val y = new Top { y => l: Top } (l=x)", "<=== y : ⊤ { y ⇒ l: ⊤ }"),
      ("y", "===> y : ⊤ { y ⇒ l: ⊤ }"),
      ("y.l", "===> y.l : ⊤")))

  def test2() = ok(List(
      ("val x = 1", "parse error: [1.9] failure: ``new'' expected but 1 found\n\n" +
                    "val x = 1\n" +
                    "        ^")))
}
