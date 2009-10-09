package scala.dot

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._

import scala.util.binding.frescala
import util.parsing.combinator.{PackratParsers, ImplicitConversions}

class Parsing extends StdTokenParsers with frescala.BindingParsers with PackratParsers with NominalBindingSyntax with ImplicitConversions {
  type Tokens = StdLexical; val lexical = new StdLexical
  lexical.delimiters ++= List("\\",".",":","=","{","}","(", ")","=>",";","&","|","..")
  lexical.reserved ++= List("val", "new", "type", "trait","Any","Nothing")

  type P[T] = PackratParser[T]

  private var indent = ""
  def l[T](p: => P[T])(name: String): P[T] = Parser{ in =>
    println(indent +"trying "+ name +" at:\n"+ in.pos.longString)
    val old = indent; indent += "  "
    val r = p(in)
    indent = old
    println(indent+name +" --> "+ r)
    r
  }

  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}

  def BindingParser(env: Map[String, Name]): BindingParser = new BindingParser(env)
  class BindingParser(env: Map[String, Name]) extends BindingParserCore(env) {
    lazy val value: P[Value] =
      ( bound(ident)                                                         ^^ {case x => Var(x)} 
      | "\\" ~> bind(ident) >> {x => (":" ~> tpe <~ ".") ~ under(x)(_.term)} ^^ {case tpe ~ body => Fun(tpe, body)  }
      )

    lazy val term: P[Term] =
      l( value
      | "val" ~> bind(ident) >> {x => ("=" ~> "new" ~> tpe) ~ under(x)(_.ctor)} ^? {case tpe ~ args_scope if tpe.isConcrete => New(tpe, args_scope)}
      | chainl1(term, success(App(_: Term, _: Term)))
      | chainl1(term, labelRef[Levels.Term], "." ^^^ (Sel(_, _)))
      )  ("term")
    
    lazy val path: P[Term] = term ^? {case p if p.isPath => p}

    lazy val ctor: P[(Members.Defs[Value], Term)] = ("{" ~> valMems <~ "}") ~ (";" ~> term)  ^^ {case ms ~ sc => (ms, sc)}

    lazy val labelV: P[Label[Levels.Term]] = "val" ~> labelRef[Levels.Term]
    def labelRef[L <: Level]: P[Label[L]] = ident ^^ Label[L]
    lazy val valMems: P[Members.Defs[Value]] = repsep[Members.Def[Value]]((labelV <~ "=") ~ value ^^ {case l ~ v => Members.Def[Terms.Value](l, v)}, ";")

    lazy val memDecl: P[Members.Decl[Entity]] =
      l( (("type" ~> labelRef[Levels.Type] <~ ":") ~ typeBounds) ^^ {case l ~ cls => Members.Decl[TypeBounds](l, cls)}
      | (("val" ~> labelRef[Levels.Term] <~ ":") ~ tpe) ^^ {case l ~ cls => Members.Decl[Type](l, cls)}
      )("memDecl")
    lazy val memDecls: P[Members.Decls] = repsep[Members.Decl[Entity]](memDecl, ";")


    lazy val tpe0: P[Type] =
      l(tsel
      | top
      | bot
      ) ("tpe0")
    lazy val tsel = l((path <~ ".") ~ labelRef[Levels.Type] ^^ {case tgt ~ l => TSel(tgt, l)}       )("tsel")
    lazy val top = l("Any" ^^^ Top                                                                  )("top")
    lazy val bot = l("Nothing" ^^^ Bottom                                                           )("bot")

    lazy val tpe: P[Type] =
    l(trfn
    | tarr
    | tand
    | tor
    | tpe0
    ) ("tpe")

    lazy val trfn = l(chainl1(tpe0, refinement, success(Refine(_, _)))                                )("trfn")
    lazy val refinement: P[\\[Members.Decls]] = l("{" ~> bind(ident) >> {x => "=>" ~> under[Members.Decls](x)(_.memDecls) <~ "}"})("refineMent")    
    lazy val tarr = l(chainl1(tpe0, tpe, "=>" ^^^ (FunT(_, _)))                                            )("tarr")
    lazy val tand = l(chainl1(tpe0, tpe, "&" ^^^ (Intersect(_, _)))                                        )("tand")
    lazy val tor = l(chainl1(tpe0, tpe, "|" ^^^ (Union(_, _)))                                            )("tor")

    lazy val typeBounds: P[TypeBounds] = l((tpe <~ "..") ~ tpe ^^ {case lo ~ hi => TypeBounds(lo, hi)})("typeBounds")
  }
  
  object Parser extends BindingParser(HashMap.empty)
}

 object TestParser extends Parsing with Application  {
  def parse(in: String) = phrase(Parser.term)(new lexical.Scanner(in))
  println(parse("val x = new Any{ self => type foo : Any..Any }{};x")) //"val x = new Any{};x"
 }