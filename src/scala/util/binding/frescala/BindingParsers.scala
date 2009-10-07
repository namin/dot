package scala.util.binding.frescala

import scala.util.parsing.combinator.Parsers
import scala.collection.immutable.Map

trait BindingParsers extends Parsers with BindingSyntaxCore {
  type BindingParser <: BindingParserCore
  def BindingParser(env: Map[String, Name]): BindingParser
  
  class BindingParserCore(env: Map[String, Name]) {
    type BindResult = (BindingParser, Name)
    
    def bind(nameParser: Parser[String]): Parser[BindResult] = nameParser ^^ {name => val n=Name(name); (BindingParser(env(name)=n), n)}
    
    def bound(nameParser: Parser[String]): Parser[Name]  = nameParser ^? env
    
    def under[T : ContainsBinders](binder: BindResult)(p: BindingParser => Parser[T]): Parser[\\[T]] = {
      val (ctx, n) = binder
      p(ctx) ^^ (\\(n, _))
    }
  }
}