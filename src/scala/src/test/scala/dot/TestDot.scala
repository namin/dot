package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDot extends Suite with DotParsing with DotTyper {
  def parse(in: String): Term = phrase(Parser.term)(new lexical.Scanner(in)).get
  def check(in: String): Type = typecheck(parse(in)) match {
    case TyperSuccess(ty) => ty
    case TyperFailure(msg) => sys.error(msg)
  }
  
  import Types._
 
  def test1() = expect(Top){check(
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
    """)}
}
