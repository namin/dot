package dot

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._
import util.parsing.combinator.{PackratParsers, ImplicitConversions}
import scala.util.parsing.input.Positional

trait DotParsing extends StdTokenParsers with BindingParsers with PackratParsers with DotNominalSyntax with ImplicitConversions with Debug with DotPrettyPrint { theParser =>
  type Tokens = StdLexical; val lexical = new StdLexical {
    override def token: Parser[Token] = delim | super.token
  }

  lexical.delimiters ++= List("=", ";", ".", "(", ")", "{", "}", "=>", "⇒", ":", "..", "->", "→", "!", "&", "∧", "/\\", "|", "∨", "\\/", "⊥", "⊤")
  lexical.reserved ++= List("val", "new", "Top", "Bottom", "Bot")

  type P[T] = PackratParser[T]

  val debugParser: Boolean = false
  def debugParser(msg: String) { if (debugParser) super.debug(msg) }

  private var indent = ""
  def l[T <: Positional](p: => Parser[T])(name: String): P[T] = positioned(Parser{ in =>
    debugParser(indent + "trying " + name)
    val oldIndent = indent
    indent += " "
    val r = p(in)
    indent = oldIndent
    debugParser(indent + name + " --> " + r)
    r
  })

  import Terms._
  import Types._
  import Members._

  def BindingParser(envArg: Map[String, Name]): BindingParser = new BindingParser { val env = envArg }
  trait BindingParser extends BindingParserCore {
    def suggest[T](parser: Parser[T], pred: T => Boolean, err: T => String): Parser[T] = Parser{ in =>
     parser(in) filterWithError(pred, err, in)
    }
    def only[T](parser: Parser[T], pred: T => Boolean, err: T => String): Parser[T] =
      parser.flatMap{r => if (pred(r)) success(r) else failure(err(r))}
    def lowerident(kind: String): P[String] = suggest[String](
        ident.withFailureMessage(kind+" expected"),
        _.charAt(0).isLower,
        kind+" should start with a lower case, unlike "+_)
    def upperident(kind: String, caveat: String = ""): P[String] = suggest[String](
        ident.withFailureMessage(kind+ " expected"),
        _.charAt(0).isUpper,
        kind+" should start with an upper case"+caveat+", unlike "+_)
    lazy val variable: P[Var] = l(bound(ident.withFailureMessage("variable expected")) ^^ Var) ("var")
    lazy val valueLabel: P[ValueLabel] = l(lowerident("value label") ^^ ValueLabel) ("value label")
    lazy val methodLabel: P[MethodLabel] = l(ident.withFailureMessage("method label expected") ^^ MethodLabel) ("method label")
    lazy val value: P[Value] = variable
    lazy val defn: P[Defn] =
      l(methodLabel ~ ("(" ~> bind(ident) >> {x => ")" ~> "=" ~>
        under(x){_.term}}) ^^ {case l~b => MethodDef(l, Method(b))}) ("method initialization") |
      l(valueLabel ~ ("=" ~> value) ^^ {case l~v => ValueDef(l, v)}) ("field initialization")
    lazy val defs: P[Defs] = l(
      opt("(" ~> only[List[Defn]](repsep(defn, opt(";")), uniqLabels, _ => "duplicate definition") <~ ")") ^^ { x =>
      x.map(Defs).getOrElse(Defs(List())) }) ("initialization")
    lazy val newInstance: P[New] = l(
      "val" ~> bind(ident) >> {x => "=" ~> "new" ~> concrete_typ ~
       under(x){p => p.defs ~ (opt(";") ~> p.term <~ opt(";")) ^^ { case ds~t => (ds,t) }} ^^
       { case tyc~args_scope => New(tyc, args_scope) }}) ("new instance")
    lazy val term1: P[Term] =
      l(term1 ~ ("." ~> methodLabel) ~ ("(" ~> term <~ ")") ^^ {case o~m~a => Msel(o, m, a)}) ("method invocation") |
      l(term1 ~ ("." ~> valueLabel) ^^ {case t~l => Sel(t, l)}) ("field selection") |
      newInstance |
      value |
      l("(" ~> term <~ ")") ("parenthesized term")
    def term: P[Term] = term1

    lazy val abstractTypeLabel: P[AbstractTypeLabel] =
      l(upperident("abstract type label") ^^ AbstractTypeLabel) ("abstract type label")
    // TODO: check that class labels are only declared once
    lazy val classLabel: P[ClassLabel] =
      l("!" ~> upperident("class label", " after the question mark") ^^ ClassLabel) ("class label")
    lazy val typeLabel: P[TypeLabel] = classLabel | abstractTypeLabel
    lazy val top: P[Type] = l(("Top" | "⊤") ^^^ Top ) ("top type")
    lazy val bottom: P[Type] = l(("Bottom" | "Bot" | "⊥") ^^^ Bottom) ("bottom type")
    lazy val intersection: P[Type] = l((typ1 ~ (("&" | "/\\" | "∧") ~> typ2)) ^^ Intersect) ("intersection type")
    lazy val union: P[Type] = l((typ2 ~ (("|" | "\\/" | "∨") ~> typ3)) ^^ Union) ("union type")
    lazy val dcl: Parser[Dcl] =
      l(methodLabel ~ (":" ~> typ ~ (("->" | "→") ~> typ)) ^^ {case l~(s~u) => MethodDecl(l, ArrowType(s, u))}) ("method declaration") |
      l(typeLabel ~ (":" ~> typ ~ (".." ~> typ)) ^^ {case l~(s~u) => TypeDecl(l, TypeBounds(s, u))}) ("type declaration") |
      l(valueLabel ~ (":" ~> typ) ^^ {case l~u => ValueDecl(l, u)}) ("value declaration")
    def refinement(typ: => Parser[Type]) = l(
      typ ~ (("{" ~> bind(ident) <~ ("=>" | "⇒")) >> {z => under(z){p =>
        only[List[Dcl]](repsep(p.dcl, opt(";")), uniqLabels, _ => "duplicate declaration") ^^ Decls }} <~ "}") ^^
      { case ty~ds => Refine(ty, ds) }) ("refinement type")
    lazy val type_selection: Parser[Type] = l(
      only[Term](term, _.isPath, "expected path, not arbitrary term like "+_.pp) ~ ("." ~> typeLabel) ^^ Tsel
    ) ("type selection")
    lazy val typ1: P[Type] =
      refinement(typ1) |
      type_selection |
      top |
      bottom |
      l("(" ~> typ <~ ")") ("parenthesized type")
    lazy val typ2: P[Type] = intersection | typ1
    lazy val typ3: P[Type] = union | typ2
    lazy val typ4: P[Type] = refinement(typ) | typ3
    def typ: P[Type] = typ4
    lazy val concrete_typ: P[Type] = only[Type](typ, _.isConcrete, "expected concrete type, unlike "+_.pp)
  }
  def Parser = BindingParser(HashMap.empty)
}
