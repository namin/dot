package dot

import scala.collection.immutable._

trait DotShell extends DotParsing with DotTyper with DotPrettyPrint { shell =>
  sealed class Line
  case class ValDef(x: String, tpe: Type, args: \\[Members.Defs]) extends Line
  case class LineTerm(tm: Term) extends Line
  
  var valDefs: List[ValDef] = List.empty
  var typerEnv: Env = initEnv
  var parsingEnv: Map[String, Name] = HashMap.empty
  
  override def BindingParser(env: Map[String, Name]): ShellParser = new ShellParser(env)
  class ShellParser(env: Map[String, Name]) extends BindingParser(env) {
    lazy val valdef: P[ValDef] = l(
      "val" ~> ident >> {xStr => bind(success(xStr)) >> {x => "=" ~> "new" ~> (concrete_typ ~
       under(x){p => p.defs <~ opt(";")}) ^^
       {case tyc~args => ValDef(xStr: String, tyc, args)}}}) ("val def")
    def line: P[Line] = term ^^ LineTerm | valdef
  }

  import Terms._
  import Types._
  import Members._
  lazy val vx = Name("x")
  lazy val vy = Name("y")
  lazy val vz = Name("z")
  lazy val funApply = MethodLabel("apply")
  def funType(s: Type, u: Type) = {
    assert(s.fresh(vz) && u.fresh(vz))
    Refine(Top, vz\\(Decls(List(MethodDecl(funApply, ArrowType(s, u))))))
  }
  def cast(tm: Term, tp: Type) = {
    assert(tm.fresh(vx) && tm.fresh(vy) && tm.fresh(vz) && tp.fresh(vx) && tp.fresh(vy) && tp.fresh(vz))
    New(
      funType(tp, tp),
      vy\\(Defs(List(MethodDef(funApply, Method(vx\\Var(vx))))),
           Msel(Var(vy), funApply, tm)))
  }
  def toTerm(line: Line): Term = line match {
    case ValDef(_, tpe, \\(x, args)) => New(tpe, x\\(args, cast(Var(x), Top)))
    case LineTerm(tm) => tm
  }

  def tc(in: String): String = {
    val line: Line = phrase(new ShellParser(parsingEnv).line)(new lexical.Scanner(in)) match {
      case Success(line, _) => line
      case r@_ => return "parse error: " + r
    }
    val r = typecheck(toTerm(line), Some(typerEnv))
    val msg = r match {
      case TyperSuccess(tp) => line match {
        case ValDef(xStr, tpe, \\(x, args)) =>
          parsingEnv = parsingEnv.updated(xStr, x)
          typerEnv = typerEnv.updated(x, tpe)
          "<<< " + xStr + " : " + tpe.pp
        case LineTerm(tm) =>
          ">>> " + tm.pp + " : " + tp.pp
      }
      case TyperFailure(msg) => "type error: " + msg
    }
    msg
  }
  
  def exec(in: String) {
    println(tc(in))
  }
}

// A minimal shell for DOT:
// $ sbt console
//
// ...
//
// scala> dot.sh.exec("val x = new Top")
// <<< x : ⊤
//
// scala> dot.sh.exec("x")
// >>> x : ⊤
// 
// scala> dot.sh.exec("val y = new Top { y => l: Top } (l=x)")
// <<< y : ⊤ { y ⇒ l: ⊤ }
// 
// scala> dot.sh.exec("y")
// >>> y : ⊤ { y ⇒ l: ⊤ }
// 
// scala> dot.sh.exec("y.l")
// >>> y.l : ⊤
object sh extends DotShell
