package scala.dot

trait PrettyPrinting 
{	
	this: Syntax =>
	
	trait PrettyPrintable {
		def prettyPrint: String
	}

	// implicit conversions
	implicit def prettyPrintEntity(e : Entity) = new PrettyPrintable {
		def prettyPrint = e match {
			case term: Term => term.prettyPrint
			case typ: Type => typ.prettyPrint
			case TypeBounds(lo, hi) => lo.prettyPrint + ".." + hi.prettyPrint
			case _ => e.toString
		}
	}

	implicit def prettyPrintName(name: Name) = new PrettyPrintable {	
		def prettyPrint = name.toString
	}
				
	// for context bound
	type PrettyPrintableFn[P] = P => PrettyPrintable
		
	implicit def prettyPrintBinder[P : PrettyPrintableFn](binder: \\[P]) = new PrettyPrintable {
		def prettyPrint = {
			val insides = binder.unabs
			insides._2.prettyPrint
		}		
	}
	
	def getBinderName[T](binder: \\[T]) = {
//		println("Binder is: " + binder)
		val n: Name = binder.unabs._1
		n.prettyPrint
	} 
	
	implicit def prettyPrintList[T : PrettyPrintableFn](list: List[T]) = new PrettyPrintable {
		def prettyPrint = {
			list.map(_.prettyPrint).mkString(";\n")
		}
	}
	
	// implicit def prettyPrintLabel(l: Label[Level]) = new PrettyPrintable {
	// 	def prettyPrint = l.name
	// }
	
	implicit def prettyPrintDecl[P <: Entity : PrettyPrintableFn](decl: Members.Decl[Level, P]): PrettyPrintable = new PrettyPrintable {
		def prettyPrint = {
			decl.l.name + " = " + decl.cls.prettyPrint
		}
	}	
	
	implicit def prettyPrintType(typ: Type): PrettyPrintable = new PrettyPrintable {
		import Types._
		def prettyPrint = typ match { 
			case Sel(tgt: Term, label: Label[Levels.Type]) => tgt.prettyPrint + "." + label.name
			case Refine(parent: Type, decls: \\[Members.Decls]) => 
				parent.prettyPrint + "{ " + getBinderName(decls) + " => \n" + decls.prettyPrint + "} " // (prettyPrintBinder(decls)(prettyPrintList))
			case Fun(from, to) => "(" + from.prettyPrint + " => " + to.prettyPrint + ")"
			case Intersect(a, b) => a.prettyPrint + " & " + b.prettyPrint
			case Union(a, b) => a.prettyPrint + " | " + b.prettyPrint
			case Top => "Any"
			case Bottom => "Nothing"
			case _ => typ.toString
		}
	}

//	implicit def prettyPrintValue(value: Terms.Value) = prettyPrintTerm(value)

	implicit def prettyPrintDefTermPair(pair: (Members.ValDefs, Term)) : PrettyPrintable = 
	 	new PrettyPrintable {
			def prettyPrint = {
//				defs.map((x : Terms.Value) => prettyPrintTerm(x).prettyPrint) + " - " + t.prettyPrint
				"{ " + prettyPrintList(pair._1)(prettyPrintDef).prettyPrint + " };\n" + pair._2.prettyPrint
			}
	}

	implicit def prettyPrintTerm(term: Term) : PrettyPrintable = new PrettyPrintable {
		def prettyPrint = term match { 
			case Terms.New(tpe, args_scope)	=> 
				"val " + getBinderName(args_scope) + " = new " + tpe.prettyPrint + "\n" + args_scope.prettyPrint
			case Terms.Var(n) => n.prettyPrint
			case Terms.App(fn, arg) => fn.prettyPrint + "(" + arg.prettyPrint + ")"
			case Terms.Unit => "()"
			case Terms.Fun(typ, body) => "(" + getBinderName(body) + ": " + typ.prettyPrint + ") => " + body.prettyPrint  //prettyPrintBinder(body)(prettyPrintTerm(_)).prettyPrint 
			case Terms.Sel(term, label) => "(" + term.prettyPrint + ")." + label.name 
		}
	}
		
	implicit def prettyPrintDef[P <: Entity : PrettyPrintableFn](defn: Members.Def[P]) = new PrettyPrintable {
		def prettyPrint = {
			"val " + defn.l.name + " = " + defn.rhs.prettyPrint
		}
	}
	
//	implicit def prettyPrintValDef(defn: Members.Def)
}