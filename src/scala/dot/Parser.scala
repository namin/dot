package scala.dot

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.ImplicitConversions
import scala.collection.immutable._

import scala.util.binding.frescala

trait Parsing extends StdTokenParsers with frescala.BindingParsers with NominalBindingSyntax with ImplicitConversions {
  type Tokens = StdLexical; val lexical = new StdLexical
  lexical.delimiters ++= List("\\",".",":","=","{","}","(", ")","=>",";","&","|","..")
  lexical.reserved ++= List("val", "new", "type", "trait","Any","Nothing")
  
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
  
  case class BindingParser(env: Map[String, Name]) extends BindingParserCore(env) { 
    def value: Parser[Value] = 
      ( bound(ident)                                                         ^^ {case x => Var(x)} 
      | "\\" ~> bind(ident) >> {x => (":" ~> tpe <~ ".") ~ under(x)(_.term)} ^^ {case tpe ~ body => Fun(tpe, body)  }
      )

    def labelV: Parser[Label[Levels.Term]] = "val" ~> labelRef[Levels.Term]
    def labelRef[L <: Level]: Parser[Label[L]] = ident ^^ Label[L]
    def valMems: Parser[Members.Defs[Value]] = repsep((labelV <~ "=") ~ value ^^ {case l ~ v => Members.Def[Terms.Value](l, v)}, ";")
    def ctor: Parser[(Members.Defs[Value], Term)] = ("{" ~> valMems <~ "}") ~ (";" ~> term)  ^^ {case ms ~ sc => (ms, sc)}

    def term: Parser[Term] = 
      ( value
      | chainl1(term, success(App(_: Term, _: Term)))
      | "val" ~> bind(ident) >> {x => ("=" ~> "new" ~> tpe) ~ under(x)(_.ctor)} ^? {case tpe ~ args_scope if tpe.isConcrete => New(tpe, args_scope)} 
      | chainl1(term, labelRef[Levels.Term], "." ^^^ (Sel(_, _)))    
      )
    
    def path: Parser[Term] = term ^? {case p if p.isPath => p}

    def memDecl: Parser[Members.Decl[Entity]] =
      ( (("type" ~> labelRef[Levels.Type] <~ ":") ~ typeBounds) ^^ {case l ~ cls => Members.Decl[TypeBounds](l, cls)}
      | (("val" ~> labelRef[Levels.Term] <~ ":") ~ tpe) ^^ {case l ~ cls => Members.Decl[Type](l, cls)}
      )
    def memDecls: Parser[Members.Decls] = repsep(memDecl, ";")
    def refinement: Parser[\\[Members.Decls]] = "{" ~> bind(ident) >> {x => "=>" ~> under[Members.Decls](x)(_.memDecls) <~ "}"}
    def tpe: Parser[Type] = 
      ( (path <~ ".") ~ labelRef[Levels.Type] ^^ {case tgt ~ l => TSel(tgt, l)}
      | chainl1(tpe, refinement, success(Refine(_, _)))
      | chainl1(tpe, "=>" ^^^ (FunT(_, _)))    
      | chainl1(tpe, "&" ^^^ (Intersect(_, _)))    
      | chainl1(tpe, "|" ^^^ (Union(_, _)))    
      | "Any" ^^^ Top
      | "Nothing" ^^^ Bottom
      )

    def typeBounds: Parser[TypeBounds] = (tpe <~ "..") ~ tpe ^^ {case lo ~ hi => TypeBounds(lo, hi)}
  }
  
  object Parser extends BindingParser(HashMap.empty)
}
// 
// object TestParser extends Parsers with Syntax with Binding with Application  {
//  def parse(in: String) = phrase(term)(new lexical.Scanner(in))
//  println(parse("\\x. \\y.y"))
// }