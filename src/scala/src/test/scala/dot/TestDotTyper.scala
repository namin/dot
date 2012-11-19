package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotTyper extends Suite with DotTyper {
  import Terms._
  import Types._
  import Members._

  val x = Name("x")
  val nodefs = Defs(List())

  def testTC1() = {
    expect(Success(Top))(typecheck(New(Top,x\\(nodefs, Var(x)))))
  }
}
