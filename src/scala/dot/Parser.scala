package scala.dot

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._

import scala.util.binding.frescala
import util.parsing.combinator.{PackratParsers, ImplicitConversions}

class Parsing extends StdTokenParsers with frescala.BindingParsers with PackratParsers with NominalBindingSyntax with ImplicitConversions {
  type Tokens = StdLexical; val lexical = new StdLexical
  lexical.delimiters ++= List("\\",".",":","=","{","}","(", ")","=>",";","&","|","..","()")
  lexical.reserved ++= List("val", "new", "type", "trait","Any","Nothing")

  type P[T] = PackratParser[T]
  
  def l[T](p: => P[T])(name: String): P[T] = Parser{ in =>
    println("trying "+ name +" at:\n"+ in.pos.longString)
    val r = p(in)
    println(name +" --> "+ r)
    r
  }

  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}

  def BindingParser(env: Map[String, Name]): BindingParser = new BindingParser(env)
  class BindingParser(env: Map[String, Name]) extends BindingParserCore(env) {
    lazy val value: P[Value] =
      ( bound(ident)                                                         ^^ {case x => Var(x)} 
      | "\\" ~> bind(ident) >> {x => (":" ~> tpe <~ ".") ~ under(x)(_.term)} ^^ {case tpe ~ body => Fun(tpe, body)  }
      | "()" ^^^ Terms.Unit
      )

    lazy val term: P[Term] =
      l( value
      | "val" ~> bind(ident) >> {x => ("=" ~> "new" ~> tpe) ~ under(x)(_.ctor)} ^? {case tpe ~ args_scope if {println("checking Tc"+ tpe); tpe.isConcrete} => New(tpe, args_scope)}
      | chainl1(term, success(App(_: Term, _: Term)))
      | chainl1(term, labelRef[Levels.Term], "." ^^^ (Sel(_, _)))
      )  ("term")
    
    lazy val path: P[Term] = term ^? {case p if p.isPath => p}

    lazy val ctor: P[(Members.Defs[Value], Term)] = l(("{" ~> valMems <~ "}") ~ (";" ~> term)  ^^ {case ms ~ sc => (ms, sc)})("ctor")

    lazy val labelV: P[Label[Levels.Term]] = "val" ~> labelRef[Levels.Term]
    def labelRef[L <: Level]: P[Label[L]] = ident ^^ Label[L]
    lazy val valMems: P[Members.Defs[Value]] = repsep[Members.Def[Value]]((labelV <~ "=") ~ value ^^ {case l ~ v => Members.Def[Terms.Value](l, v)}, ";")

    lazy val memDecl: P[Members.Decl[Entity]] =
      ( (("type" ~> labelRef[Levels.Type] <~ ":") ~ typeBounds) ^^ {case l ~ cls => Members.Decl[TypeBounds](l, cls)}
      | (("val" ~> labelRef[Levels.Term] <~ ":") ~ tpe) ^^ {case l ~ cls => Members.Decl[Type](l, cls)}
      )
    lazy val memDecls: P[Members.Decls] = repsep[Members.Decl[Entity]](memDecl, ";")

    lazy val refinement: P[\\[Members.Decls]] = l("{" ~> bind(ident) >> {x => "=>" ~> under[Members.Decls](x)(_.memDecls) <~ "}"})("refinement")

    lazy val tpe: P[Type] =
      l( (path <~ ".") ~ labelRef[Levels.Type] ^^ {case tgt ~ l => TSel(tgt, l)}
      | chainl1(tpe, refinement, success(Refine(_, _)))
      | chainl1(tpe, "=>" ^^^ (FunT(_, _)))
      | chainl1(tpe, "&" ^^^ (Intersect(_, _)))
      | chainl1(tpe, "|" ^^^ (Union(_, _)))
      | "Any" ^^^ Top
      | "Nothing" ^^^ Bottom
      ) ("type")

    lazy val typeBounds: P[TypeBounds] = (tpe <~ "..") ~ tpe ^^ {case lo ~ hi => TypeBounds(lo, hi)}
  }
  
  object Parser extends BindingParser(HashMap.empty)
}

object TestParser extends Parsing with Application  {
  def parse(in: String) = phrase(Parser.term)(new lexical.Scanner(in))
//  println(parse("val root = new Any { rootThis => type Unit: Any..Any } { }; ()"))

//	val stuff = Array(
//    "val x = new Any{};x",
//    "val root = new Any { rootThis => } {}; ()"
//		"val root = new Any { rootThis =>" +
//			"type Unit: Any..Any } { }; ()",
//		"val x = new Any { self => val bar: Any => Any; } { val bar = \\x: Any. x }; ()"
//	);

//  String toParse = 

}