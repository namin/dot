package dot

import scala.collection.immutable._
import scala.text.Document
import scala.text.Document._

trait DotSugarFunctions extends DotParsing with DotTyper with DotPrettyPrint {
  import Terms._
  import Types._
  import Members._

  // Syntax

  case class Lambda(paramTp: Type, body: \\[Term]) extends Term

  // TODO: what about positions of synthetic parts?
  val lApply = MethodLabel("apply")
  object App {
    def apply(fun: Term, arg: Term): Term = Msel(fun, lApply, arg)
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case Msel(fun, `lApply`, arg) => Some((fun, arg))
      case _ => None
    }
  }
  object LambdaType {
    def apply(paramTp: Type, bodyTp: Type): Type = {
      val self = Name("self")
      Refine(Top, self\\Decls(List(MethodDecl(lApply, ArrowType(paramTp, bodyTp)))))
    }
    def unapply(tp: Type): Option[(Type, Type)] = tp match {
      case Refine(Top, \\(self, Decls(List(MethodDecl(`lApply`, ArrowType(paramTp, bodyTp)))))) if paramTp.fresh(self) && bodyTp.fresh(self) =>
        Some((paramTp, bodyTp))
      case _ => None
    }
  }
  object Cast {
    def apply(t: Term, tp: Type): Term = {
      val id = Name("id")
      val x = Name("x")
      App(New(LambdaType(tp, tp), id\\(Defs(List(MethodDef(lApply, Method(x\\Var(x))))), Var(id))), t)
    }
    def unapply(t: Term): Option[(Term, Type)] = t match {
      case App(New(LambdaType(tp, tp1), \\(id, (Defs(List(MethodDef(`lApply`, Method(\\(x, Var(x1)))))), Var(id1)))), t) if tp==tp1 && x==x1 && id==id1 =>
        Some((t, tp))
      case _ => None
    }
  }

  override implicit def termHasBinders: ContainsBinders[Term] = (tm: Term) => new Nominal[Term] {
    def swap(a: Name, b: Name): Term = tm match {
      case Lambda(tp, body) => Lambda(tp swap(a, b), body swap(a, b)).setPos(tm.pos)
      case _ => DotSugarFunctions.super.termHasBinders(tm) swap(a, b)
    }
    def fresh(a: Name): Boolean = tm match {
      case Lambda(tp, body) => tp.fresh(a) && body.fresh(a)
      case _ => DotSugarFunctions.super.termHasBinders(tm) fresh(a)
    }
  }

  override implicit def termIsSubstable(in: Term): Substable[Term, Term] = new Substable[Term, Term] {
    def subst(from: Name, to: Term): Term = in match {
      case Lambda(tp, body) => Lambda(tp subst(from, to), body subst(from, to)).setPos(in.pos)
      case _ => DotSugarFunctions.super.termIsSubstable(in) subst(from, to)
    }
  }

  // Parsing

  lexical.delimiters ++= List("\\", "λ")

  override def BindingParser(envArg: Map[String, Name]) = new DotSugarFunctionsBindingParser { val env = envArg }
  trait DotSugarFunctionsBindingParser extends BindingParser {
    lazy val term2: P[Term] =
      l(term2 ~ (":" ~> typ) ^^ {case t~tp => Cast(t, tp)}) ("cast sugar") |
      l(("\\" | "λ") ~> bind(ident) >> {x => (":" ~> typ <~ ".") ~ under(x){_.term} ^^
        {case tp~t => Lambda(tp, t)}}) ("lambda sugar") |
      term1
    override def term: P[Term] =
      l(chainl1(term2, success({(t1:Term,t2:Term) => App(t1, t2).setPos(t1.pos)}))) ("application sugar") |
      term2 |
      super.term
    override def typ: P[Type] =
      l(typ4 ~ (("=>" | "⇒") ~> typ) ^^ {case tp1~tp2 => LambdaType(tp1, tp2)}) ("lambda type sugar") |
      super.typ
  }

  // Pretty Printing
  override implicit def termIsPrettyPrintable(tm: Term): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = tm match {
      case Cast(t, tp) => "(" :: t.ppdoc :: "):(" :: tp.ppdoc :: text(")")
      case App(t1, t2) => (t1 match {
        case _:Var | App(_, _) => t1.ppdoc
        case _ => "(" :: t1.ppdoc :: text(")")
      }) :: " " :: (t2 match {
        case _:Var => t2.ppdoc
        case _ => "(" :: t2.ppdoc :: text(")")
      })
      case Lambda(tp, \\(x, t)) => "λ" :: x.pp :: ":" :: tp.ppdoc :: "." :: t.ppdoc
      case _ => DotSugarFunctions.super.termIsPrettyPrintable(tm).ppdoc
    }
  }
 override implicit def typeIsPrettyPrintable(tp: Type): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = tp match {
      case LambdaType(tp1, tp2) => (tp1 match {
        case LambdaType(_, _) => "(" :: tp1.ppdoc :: text(")")
        case _ => tp1.ppdoc
      }) :: " ⇒ " :: tp2.ppdoc
      case _ => DotSugarFunctions.super.typeIsPrettyPrintable(tp).ppdoc
    }
 }
 
 // Typer
 override def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] = {
   import TyperMonad._
   debug("-------------------------")
   debug("(sugar) type of " + tm.pp + ":" + pt)
   tm match {
     case Lambda(s, \\(x, body)) => for(
         _ <- wfe(s);
         eu <- Infer[Type]("lambdaBodyTp");
         _ <- assume(x, s)(ofT(body, eu));
         u <- !eu;
         _ <- pt := LambdaType(s, u)) yield ()
     case _ => super.ofT(tm, pt)
   }
 }
}