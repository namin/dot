package scala.dot
 
import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._
 
import scala.util.binding.frescala
import util.parsing.combinator.{PackratParsers, ImplicitConversions}
 
class Parsing extends StdTokenParsers with frescala.BindingParsers with PackratParsers with NominalBindingSyntax with ImplicitConversions { 
	theParser =>
	
  type Tokens = StdLexical; val lexical = new StdLexical
  lexical.delimiters ++= List("\\",".",":","=","{","}","(", ")","=>",";","&","|","..","()")
  lexical.reserved ++= List("val", "new", "type", "trait", "Any", "Nothing", "extends")
 
  type P[T] = PackratParser[T]

  val logging = false;

  private var indent = ""
  def l[T](p: => Parser[T])(name: String): P[T] = Parser{ in =>
   	if (logging) println(indent +"trying "+ name) // +" at:\n"+ in.pos)
    val old = indent; indent += " "
    val r = p(in)
    indent = old

    if (logging) println(indent + name +" --> "+ r)
    r
  }

  def chainl2[T, U](first: => Parser[T], p: => Parser[U], q: => Parser[(T, U) => T]): Parser[T] 
    = first ~ rep1(q ~ p) ^^ {
        case x ~ xs => xs.foldLeft(x){(_, _) match {case (a, f ~ b) => f(a, b)}}
      }
 
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
 
  def BindingParser(env: Map[String, Name]): BindingParser = new BindingParser(env)
  class BindingParser(env: Map[String, Name]) extends BindingParserCore(env) {

    lazy val value: P[Value] =
      ( 
				l (bound(ident) ^^ {case x => Var(x)}) ("var")
      | l("\\" ~> "(" ~> bind(ident) >> {x => (":" ~> tpe <~ ")" <~ "=>") ~ under(x)(_.term)} ^^ {case tpe ~ body => Fun(tpe, body) }) ("fun")
      | l ("()" ^^^ Unit) ("unit")
      ) 

		//  
		//     lazy val term: P[Term] = (
		//       l( "(" ~> term <~")" ) ("paren")
		// 	 | l((term ~ term) ^^ { case a ~ b => App(a,b) } ) ("app")
		//        | l (chainl2(term0, termLabelRef, "." ^^^ (Sel(_, _)))) ("sel")
		//        | l (term0) ("term0")
		// )
		//  
		//     lazy val term0: P[Term] = (
		// 		l( value ) ("value")
		//       | l ("val" ~> bind(ident) >> {x => ("=" ~> "new" ~> tpe) ~! under[(Members.ValDefs, Term)](x)(_.ctor)} ^^ {case tpe ~ args_scope /*if tpe.isConcrete*/ => New(tpe, args_scope)}) ("new-expr" ) 
		// )

		// app MUST be pulled out as its own lazy val, due to the fact that "app" and "sel" both
		// have the same left recursive term
		lazy val app: P[Term] = (
			 l ((term ~ ("(" ~> term <~ ")")) ^^ { case a ~ b => App(a,b) } ) ("app")					
			 | (term <~ "()") ^^ (App(_, Terms.Unit))
		)
		
		// selection MUST be pulled out as its own lazy val, due to the fact that "app" and "sel" both
		// have the same left recursive term			
		lazy val selection: P[Term] = (
			l (chainl2(term, termLabelRef, "." ^^^ (Sel(_, _)))) ("sel")	       
		)
    		
		lazy val term: P[Term] = (
				"()" ^^^ Unit
  		 |  l( "(" ~> term <~")" ) ("paren")
			 | selection
//			 | l (chainl2(term, termLabelRef, "." ^^^ (Sel(_, _)))) ("sel")
			 | app
       | l ("val" ~> bind(ident) >> {x => ("=" ~> "new" ~> tpe) ~! under[(Members.ValDefs, Term)](x)(_.ctor)} ^^ {case tpe ~ args_scope /*if tpe.isConcrete*/ => New(tpe, args_scope)}) ("new-expr" ) 
			 | l (value) ("value")		
		)
 
    lazy val path: P[Term] = term //^? {case p if p.isPath => p}
 
    lazy val ctor: P[(Members.ValDefs, Term)] = ("{" ~> valMems <~ "}") ~ (";" ~> term) ^^ {case ms ~ sc => (ms, sc)}
 
    lazy val labelV: P[TermLabel] = "val" ~> termLabelRef
		def termLabelRef: P[TermLabel] = ident ^^ TermLabel
		def typeLabelRef: P[TypeLabel] = ident ^^ TypeLabel.concreteTypeLabel
		def abstractTypeLabelRef: P[TypeLabel] = ident ^^ TypeLabel.abstractTypeLabel	

    lazy val valMems: P[Members.ValDefs] = repsep[Members.ValueDef]((labelV <~ "=") ~ value ^^ {case l ~ v => Members.ValueDef(l, v)}, ";") ^^ {Members.ValDefs(_)} // <~ ";"
 
		// todo: de-sugaring is done here, ideally it would be done in a separate phase
		// currently done for "type L = T" and "trait L extends T" syntax 
    lazy val memDecl: P[Members.Dcl] =
			l((("type" ~> abstractTypeLabelRef <~ "=") ~! typeSugar) ^^ {case l ~ cls => Members.TypeBoundsDecl(l, cls)}
      | (("type" ~> abstractTypeLabelRef <~ ":") ~! typeBounds) ^^ {case l ~ cls => Members.TypeBoundsDecl(l, cls)}
			| (("trait" ~> typeLabelRef <~ "extends") ~! typeSugar) ^^ { case l ~ cls => Members.TypeBoundsDecl(l, cls) }
//			| (( "type" ~> labelRef[Levels.Type] <~ "=" ~ typeSugar) ^^ { case bound => Members.Decl[TypeBounds](bound, bound)})
      | (("val" ~> termLabelRef <~ ":") ~! tpe) ^^ {case l ~ cls => Members.TypeDecl(l, cls)}
      )("memDecl")

    lazy val memDecls: P[Members.Decls] = repsep[Members.Dcl](memDecl, ";") ^^ {Members.Decls(_)}
		

		// lazy val valDecls = repsep(valDecl, ";")		
		// lazy val typeDecls = repsep(typeDecl, ";")
 
    lazy val tpe: P[Type] =
    l( l(chainl2(tpe0, refinement, success(Refine(_, _))) )("trefine")
     | l(chainl2(tpe0, tpe, "=>" ^^^ (FunT(_, _))) )("tfun")
     | l(chainl2(tpe0, tpe, "&" ^^^ (Intersect(_, _))) )("tand")
     | l(chainl2(tpe0, tpe, "|" ^^^ (Union(_, _))) )("tor")
     | tpe0
     )("tpe")
 
    lazy val tpe0: P[Type] =
     l( l("(" ~> tpe <~")") ("tparen")
		 | l(path ^^ {case Terms.Sel(tgt, TermLabel(l)) => TSel(tgt, TypeLabel(l, true))} )("tsel")
//     l(l((path <~ ".") ~ typeLabelRef ^^ {case tgt ~ l => TSel(tgt, l)} )("tsel")
     | l("Any" ^^^ Top )("top")
     | l("Nothing" ^^^ Bottom )("bot")
     )("tpe0")
 
    lazy val refinement: P[\\[Members.Decls]] = 
			l("{" ~> bind(ident) >> {x => "=>" ~> under[Members.Decls](x)(_.memDecls) <~ "}"})("refinement") // (Parsing.this.listBinders(memDeclHasBinders))
 
    lazy val typeBounds: P[TypeBounds] = l((tpe <~ "..") ~ tpe ^^ {case lo ~ hi => TypeBounds(lo, hi)})("typeBounds")

		lazy val typeSugar: P[TypeBounds] = l((tpe ^^ {(x: Type) => TypeBounds(x, x)} ))("typeBoundsSugar")
  }
  
  object Parser extends BindingParser(HashMap.empty)
}


object TestParser extends Parsing with PrettyPrinting with Application with Evaluation {
	import scala.io.Source;

  def parse(in: String) = phrase(Parser.term)(new lexical.Scanner(in))

  val source = Source.fromFile("dot.txt")
  val lines = source.getLines().mkString
  println("parsing: " + lines)
  println("******************")
	val result = parse(lines).get;
	println(result);
  println(result.prettyPrint)

	println("-----\nEvaluation:")
	
	val evalResult = eval(result)
	println("------\n" + evalResult.prettyPrint)
}