package dot

import scala.text.Document
import scala.text.Document._

trait DotPrettyPrint { this: DotNominalSyntax =>

  trait PrettyPrintable {
    def ppdoc: Document
    def pp: String = {
      val sw = new java.io.StringWriter()
      ppdoc.format(50, sw)
      sw.toString
    }
  }

  import Terms._
  import Types._
  import Members._


  implicit def termIsPrettyPrintable(tm: Term): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = tm match {
      case Var(n) => text(n.pp)
      case Sel(obj, l) => obj.ppdoc :: "." :: text(l.name)
      case Msel(obj, m, arg) => obj.ppdoc :: "." :: m.name :: "(" :: arg.ppdoc :: text(")")
      case New(tpe, \\(z, (args, t))) =>
        val beg = "val " + z.pp + " = new "
        beg :: (tpe match {
          case _:Intersect | _:Union => group(nest(beg.length, tpe.ppdoc))
          case _ => tpe.ppdoc
        })  ::group(args.ppdoc) :: ";" :: (t match {
          case _:Var => " " :: t.ppdoc
          case _ => break :: t.ppdoc
        })
    }
  }

  implicit def typeLabelIsPrettyPrintable(l: TypeLabel): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = l match {
      case AbstractTypeLabel(name) => text(name)
      case ClassLabel(name) => "!" :: text(name)
    }
  }

  implicit def typeIsPrettyPrintable(tp: Type): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = tp match {
      case Tsel(obj, l) => obj.ppdoc :: "." :: l.ppdoc
      case Refine(parent, \\(z, decls)) =>
        parent.ppdoc :: " { " :: z.pp :: " ⇒" :: group(nest(3, decls.ppdoc) :: break) :: text("}") 
      case Intersect(a, b) =>
        def p(tp: Type) = tp match {
          case _:Union => "(" :: group(nest(3, tp.ppdoc)) :: text(")")
          case _ => tp.ppdoc
        }
        p(a) :: " ∧" :/: p(b)
      case Union(a, b) => a.ppdoc :: " ∨" :/: b.ppdoc
      case Top => text("⊤")
      case Bottom => text("⊥")
    }
  }

  implicit def listIsPrettyPrintable[T](lst: List[T])(implicit ev: T => PrettyPrintable): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = lst match {
      case Nil => text("")
      case x::Nil => break :: x.ppdoc
      case x::xs => break :: x.ppdoc :: ";" :: xs.ppdoc
    }
  }

  implicit def defIsPrettyPrintable(d: Defn): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = d match {
      case MethodDef(m, Method(\\(x,b))) => m.name :: "(" :: x.pp :: ") = " :: b.ppdoc
      case ValueDef(l, v) => l.name :: " = " :: v.ppdoc
    }
  }

  implicit def defsIsPrettyPrintable(ds: Defs): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = ds match {
      case Defs(List()) => text("")
      case Defs(ds) => group(" (" :: nest(3, ds.ppdoc) :/: text(")"))
    }
  }

  implicit def dclIsPrettyPrintable(d: Dcl): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = d match {
      case TypeDecl(l, TypeBounds(s, u)) =>
        val beg = l.pp + ": "
        beg :: ((s, u) match {
          case ((Top | Bottom), _) => s.ppdoc :: " .. " :: (u match {
            case _:Intersect | _:Union => group(nest(beg.length + 5, u.ppdoc))
            case _ => u.ppdoc
          })
          case (_, _) => nest(beg.length, s.ppdoc :: " .." :/: u.ppdoc)
        })
      case MethodDecl(m, ArrowType(s, u)) =>
        val beg = m.name + ": "
        beg :: nest(beg.length, s.ppdoc) :: " → " :: nest(3, u.ppdoc)
      case ValueDecl(l, u) => l.name :: ": " :: nest(3, u.ppdoc)
    }
  }

  implicit def declsIsPrettyPrintable(ds: Decls): PrettyPrintable = new PrettyPrintable {
    def ppdoc: Document = ds match {
      case Decls(List()) => text("")
      case Decls(ds) => ds.ppdoc
    }
  }
}