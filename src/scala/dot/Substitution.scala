package scala.dot

/**
 * Created by IntelliJ IDEA.
 * User: adriaan
 * Date: Nov 4, 2009
 * Time: 11:35:06 AM
 * To change this template use File | Settings | File Templates.
 */
//trait Logging {
//  def log[T](what: => T)(before: String, after: T => String = ((x: T) => "res= "+x), printer: String => Unit = printlnTab(_)): T = {
//    printer(before)
//    val res = what
//    printer(after(res))
//    res
//  }
//}

trait Substitution extends NominalBindingSyntax {
  import Terms._
  import Members._
  import Types.{Sel=>TSel, Fun=>FunT, _}

  // XXX TODO: can implicit resolution and type inference be improved so that we don't need this specialised version of scopedIsSubstable?
  implicit def s[T](in: \\[T])(implicit wSubs: T => Substable[Term, T], wNom: T => Nominal[T]): Substable[Term, \\[T]] = scopedIsSubstable[T, Term, T](in)
  implicit def termIsSubstable(in: Term): Substable[Term, Term] = new Substable[Term, Term] {
	  def subst(from: Name, to: Term): Term = /*log(*/in match {
			case Var(`from`) => to
      case Var(_) => in
			case Fun(tpe, b) => Fun(tpe subst(from, to), b subst(from, to))
			case Terms.Unit => Terms.Unit
			case App(fun, arg) => App(fun subst(from, to), arg subst(from, to))
			case New(tpe, args_scope) => New(tpe subst(from, to), args_scope subst(from, to))
      case Sel(tgt, label) => Sel(tgt subst(from, to), label)
		}//)("Substituting " + to.prettyPrint + " for " + from.prettyPrint + " in " + in.prettyPrint)
  }

  implicit def valueDefIsSubstable(in: ValueDef): Substable[Term, ValueDef] = new Substable[Term, ValueDef] {
	  def subst(from: Name, to: Term): ValueDef = in match {
      case ValueDef(l, rhs) => ValueDef(l, rhs) // TODO: can substitution ever change these?? subst(from, to))
    }
  }

  implicit def typeIsSubstable(in: Type): Substable[Term, Type] = new Substable[Term, Type] {
	  def subst(from: Name, to: Term): Type = in match {
			case TSel(tgt, label) => TSel(tgt subst(from, to), label)
			case Refine(parent, decls) => Refine(parent subst(from, to), decls subst(from, to))
			case FunT(a, r) => FunT(a subst(from, to), r subst(from, to))
			case Intersect(a, b) => Intersect(a subst(from, to), b subst(from, to))
			case Union(a, b) => Union(a subst(from, to), b subst(from, to))
      case Top => Top
      case Bottom => Bottom
		}
  }

  implicit def declIsSubstable(in: Decl[Level, Entity]): Substable[Term, Decl[Level, Entity]] = new Substable[Term, Decl[Level, Entity]] {
	  def subst(from: Name, to: Term): Decl[Level, Entity] = in match {
      case TypeBoundsDecl(label, bounds) => TypeBoundsDecl(label, bounds subst(from, to))
      case TypeDecl(label, tp) => TypeDecl(label, tp subst(from, to))
    }
  }

  implicit def typeBoundsIsSubstable(in: TypeBounds): Substable[Term, TypeBounds] = new Substable[Term, TypeBounds] {
	  def subst(from: Name, to: Term): TypeBounds = in match {
      case TypeBounds(lo, hi) => TypeBounds(lo subst(from, to), hi subst(from, to))
    }
  }
} 