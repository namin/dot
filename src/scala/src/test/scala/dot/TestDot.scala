package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLooseDot extends TestDot with LooseDotTyper {
}

@RunWith(classOf[JUnitRunner])
class TestDot extends Suite with DotParsing with DotTyper {
  def parse(in: String): Term = phrase(Parser.term)(new lexical.Scanner(in)) match {
    case Success(tm, _) => tm
    case r@_ => sys.error(r.toString)
  }
  def check(in: String): Type = typecheck(parse(in)) match {
    case TyperSuccess(ty) => ty
    case TyperFailure(msg) => sys.error(msg)
  }
  def checkfail(in: String): String = typecheck(parse(in)) match {
    case TyperSuccess(ty) => sys.error("expected failure, got success: "+ty)
    case TyperFailure(msg) => msg
  }
  
  import Types._
 
  def test1() = expectResult(Top){check(
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
    """
  )}

  def testFBoundedAbstractionDeclared() = expectResult(Top){check(
    """
      val x = new ⊤ { x ⇒ A: ⊥..⊤; !L : ⊥..x.A { a ⇒ B : ⊥..x.!L } }
      val y = new Top
      y
    """
  )}

  def testFBoundedAbstractionUsed() = expectResult(Top){check(
    """
      val x = new ⊤ { x ⇒ A: ⊥..⊤; !L : ⊥..x.A { a ⇒ B : ⊥..x.!L } }
      val y = new x.!L
      val id = new ⊤ { id ⇒
        apply : ⊤→⊤
      }(apply(x)=x)
      id.apply(y)
    """
  )}

  def testUnit() = expectResult(Top){check(
    """
      val id = new ⊤ { id ⇒
        apply : ⊤→⊤
      }(apply(x)=x)
      val dummy = new ⊤
      val root = new ⊤ { root =>
        !Unit: ⊥..⊤
         unit: ⊤→root.!Unit
      }(unit(x)=(val u = new root.!Unit; u))
      id.apply(root.unit(dummy))
    """
  )}

  def testFunctions() = expectResult(Top){check(
    """
      val sugar = new ⊤ { s ⇒
        !Arrow: ⊥..⊤ { f ⇒
           apply: ⊥ → ⊤
        }
      }
      val id = new sugar.!Arrow { f => apply: ⊤ → ⊤ } (apply(x)=x)
      id.apply(id)
    """
  )}

  def testLabelMixupError1() = expectResult(
"""undeclared ClassLabel(L)
      val y = new x.!L

                    ^""")(checkfail(
    """
      val x = new ⊤
      val y = new x.!L
      x
    """
  ))

  def testLabelMixupError2() = expectResult(
"""undeclared ValueLabel(a)
      val y = new x.a.!L

                    ^""")(checkfail(
    """
      val x = new ⊤
      val y = new x.a.!L
      x
    """
  ))

  def testLabelMixupError3() = expectResult(
"""undeclared ValueLabel(a)
      x.a.b

        ^"""
)(checkfail(
    """
      val x = new ⊤
      x.a.b
    """
  ))

  def testBottom() = expectResult(Bottom)(check(
    """
      val root = new ⊤ { root => error:  ⊤ -> ⊥ } ( error(x) = root.error(x) )
      root.error(root)
    """
  ))

  def testBottomFun() = expectResult(Bottom)(check(
    """
      val sugar = new ⊤ { s ⇒
        !Arrow: ⊥ .. ⊤ { f ⇒
           apply: ⊥ → ⊤
        }
      }
      val error = new sugar.!Arrow { f => apply: ⊤ → ⊥ } (apply(x) = error.apply(x))
      error.apply(error)
    """
  ))

  def testPeano() = expectResult(Top){check(
    """
      val sugar = new ⊤ { s ⇒
        !Arrow: ⊥ .. ⊤ { f ⇒
           apply: ⊥ → ⊤
        }
        !Unit: ⊥ .. ⊤
      }
      val unit = new sugar.!Unit
      val id = new sugar.!Arrow { f => apply: ⊤ → ⊤ } (apply(x)=x)
      val error = new sugar.!Arrow { f => apply: ⊤ → ⊥ } (apply(x) = error.apply(x))

      val root = new ⊤ { r ⇒
        !Nat2Nat: sugar.!Arrow { f => apply: r.!Nat  → r.!Nat }
                  ..
                  sugar.!Arrow { f => apply: r.!Nat  → r.!Nat }
        !Boolean: ⊥..⊤ { b ⇒
          ifNat: r.!Nat → r.!Nat2Nat
        }
        !Nat: ⊥ .. ⊤ { n  ⇒
          isZero: sugar.!Unit → r.!Boolean
          pred: sugar.!Unit → r.!Nat
          succ: sugar.!Unit → r.!Nat
        }
        false: sugar.!Unit → r.!Boolean
        true: sugar.!Unit → r.!Boolean
        zero: sugar.!Unit → r.!Nat
        successor: r.!Nat → r.!Nat
      } (
        false(u) = val ff = new root.!Boolean (
          ifNat(a) = val f = new root.!Nat2Nat ( apply(b) = b ); f
        ); ff
        true(u)  = val tt = new root.!Boolean (
          ifNat(a) = val f = new root.!Nat2Nat ( apply(b) = a ); f
        ); tt
        zero(u)  = val zz = new root.!Nat (
          isZero(u) = root.true(u)
          succ(u)   = root.successor(zz)
          pred(u)   = error.apply(u)
        ); zz
        successor(n) = val ss = new root.!Nat (
          isZero(u) = root.false(u)
          succ(u)   = root.successor(ss)
          pred(u)   = n
       ); ss
      )
      id.apply(root.zero(unit).succ(unit).pred(unit).isZero(unit))
    """
  )}

  def testScopeFresh() = expectResult(
"""cannot have type (x.L) of new scope (x.l) path-dependent on x
    x.l

    ^"""){checkfail(
    """
    val x = new Top { x => L: Top..Top; l: x.L }(l=x);
    x.l
    """
  )}

  def testMemTermRestriction() = expectResult(
"""mem-term restriction fails for z in l: z.L
(val x = new Top { x => L: Top..Top; l: x.L }(l=x); x).l

                                                       ^"""){checkfail(
"""
(val x = new Top { x => L: Top..Top; l: x.L }(l=x); x).l
"""
  )}

  def testTooRecursive() = expectResult("stuck in infinite derivation"){checkfail(
      "val x = new Top {x => l: x.L; L: Bot .. x.l.L} (l=x); x")
  }
}
