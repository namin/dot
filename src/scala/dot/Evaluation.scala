package scala.dot

trait Evaluation extends NominalBindingSyntax with PrettyPrinting with Substitution {

	import Terms._
	import Members._
  import Types.{Sel=>TSel, Fun=>FunT, _}
	import scala.collection.immutable.ListMap
	
	def eval(term: Term): Term = {
		val result = evalAll(term, new ListMap)	
		println("map: " + result._2)
		result._1
	}
	
	def evalAll(term: Term, store: Store): (Term, Store) = {			
		try {
			val (term2, store2) = eval1(term, store) 
			evalAll(term2, store2)
		} catch {
			case NoRuleApplies => (term, store)
			case NotFound => printlnTab("Not found"); (term, store)
		}
	}
	
	def termSubsTop(value: Value, binder: \\[Term]): Term = {
		val (fresh, term) = binder.unabs
		val result = term subst(fresh, value)
		result
	}


	class Constructor(val typ: Type, val defs: ValDefs) {
		 override def toString = typ.prettyPrint + " -- " + defs.prettyPrint
	}
	
	type Store = Map[Name, Constructor]
	
	case object NoRuleApplies extends Throwable
	case object NotFound extends Throwable
	
	var indent: String = "";

	def printlnTab(s: String) {
		println(indent + s)
	}
	
	def eval1(term: Term, store: Store): (Term, Store) = {	
		val old: String = indent
		indent += "  "

		println("--------")
		printlnTab(term.prettyPrint)
		println("--------")
		
		val result = term match {
			case App(fun, arg) => 
				fun match {
					case Fun(tpe, body) => arg match {
						case v: Value => 
							// printlnTab("app(fun, value)")
							(termSubsTop(v, body), store)
						case _ => 
							// printlnTab("app(fun, not value): " + arg.prettyPrint)
							val result = eval1(arg, store)
							(App(fun, result._1), result._2)
					}
					case _ => 
						// printlnTab("app(not fun, not value)")
						val result = eval1(fun, store)		
						(App(result._1, arg), result._2)
				}
							
			case New(tpe, args_scope) => 
				printlnTab("New")
			
				val \\(freshName, (defs, nestedTerm)) = args_scope
				val newStore = store + ((freshName, new Constructor(tpe, defs)))
				println("adding to store: " + freshName)
				(nestedTerm, newStore)
			
			case Sel(tgt, label) => 
				printlnTab(term.prettyPrint)
			
				tgt match {
					case Var(name) => (termSel(name, label, store), store)
					case _ => 
						val result = eval1(tgt, store)
						(Sel(result._1, label), result._2)
				}
				
			case _ => 
				printlnTab("no rule applies: " + term.prettyPrint)
				throw NoRuleApplies
		}
		indent = old
		result
	}
	
	def termSel(varName: Name, label: Label[Level], store: Store): Value = {
		store.get(varName) match {
			case Some(cons) => 
				cons.defs.find( (v: ValueDef) => v.l == label) match {
					case Some(value) => value.rhs
					case None => 
						printlnTab("Not found: " + label + " in: " + cons.defs)
						throw NotFound
				}
			case None => throw NotFound
		}
	}
	
}