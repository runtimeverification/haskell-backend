package org.kframework.minikore.implementation

import org.kframework.minikore.interfaces.{build, pattern => p}

import scala.collection._

/** Algebraic data type of MiniKore. */ // TODO: should rename to "pattern"
object MiniKore {

  /** A collection of classes that serve as the default implementation of the [[org.kframework.minikore.interfaces.pattern]] **/

  // Pattern Implementations
  // =======================

  case class Variable(_1: p.Name, _2: p.Sort) extends p.Variable {
    def build(_1: p.Name, _2: p.Sort): Variable = Variable(_1, _2)
  }

  case class DomainValue(_1: p.Symbol, _2: p.Value) extends p.DomainValue {
    def build(_1: p.Symbol, _2: p.Value): DomainValue = DomainValue(_1, _2)
  }

  case class Application(_1: p.Symbol, args: Seq[p.Pattern]) extends p.Application {
    def build(_1: p.Symbol, args: Seq[p.Pattern]): Application = Application(_1, args)
  }

  case class Top() extends p.Top {
    def build(): Top = Top()
  }

  case class Bottom() extends p.Bottom {
    def build(): Bottom = Bottom()
  }

  case class And(_1: p.Pattern, _2: p.Pattern) extends p.And {
    def build(_1: p.Pattern, _2: p.Pattern): And = And(_1, _2)
  }

  case class Or(_1: p.Pattern, _2: p.Pattern) extends p.Or {
    def build(_1: p.Pattern, _2: p.Pattern): Or = Or(_1, _2)
  }

  case class Not(_1: p.Pattern) extends p.Not {
    def build(_1: p.Pattern): Not = Not(_1)
  }

  case class Implies(_1: p.Pattern, _2: p.Pattern) extends p.Implies {
    def build(_1: p.Pattern, _2: p.Pattern): Implies = Implies(_1, _2)
  }

  case class Exists(_1: p.Variable, _2: p.Pattern) extends p.Exists {
    def build(_1: p.Variable, _2: p.Pattern): Exists = Exists(_1, _2)
  }

  case class ForAll(_1: p.Variable, _2: p.Pattern) extends p.ForAll {
    def build(_1: p.Variable, _2: p.Pattern): ForAll = ForAll(_1, _2)
  }

  case class Next(_1: p.Pattern) extends p.Next {
    def build(_1: p.Pattern): Next = Next(_1)
  }

  case class Rewrite(_1: p.Pattern, _2: p.Pattern) extends p.Rewrite {
    def build(_1: p.Pattern, _2: p.Pattern): Rewrite = Rewrite(_1, _2)
  }

  case class Equals(_1: p.Pattern, _2: p.Pattern) extends p.Equals {
    def build(_1: p.Pattern, _2: p.Pattern): Equals = Equals(_1, _2)
  }

}


/** Helpers for building MiniKore definitions **/
object MiniKoreDSL {

  import MiniKore._

  import org.kframework.minikore.interfaces.outer.Sentence
  import org.kframework.minikore.implementation.outer._

  // Show Name and Value have wrappers? What exactly are their roles?
  implicit def asSort(s: String): p.Sort     = p.Sort(s)
  implicit def asSymbol(s: String): p.Symbol = p.Symbol(s)
  //implicit def asName(s: String): p.Name = p.Name(s)
  //implicit def asValue(s: String): p.Value = p.Value(s)

  case class definition(modules: Module*) {
    def att(atts: p.Pattern*): Definition = Definition(modules, atts)
  }
  implicit def asDefinition(d: definition): Definition = d.att()

  case class module(name: p.Name, sentences: Sentence*) {
    def att(atts: p.Pattern*): Module = Module(name, sentences, atts)
  }
  implicit def asModule(m: module): Module = m.att()

  case class imports(name: p.Name) {
    def att(atts: p.Pattern*): Import = Import(name, atts)
  }
  implicit def asImport(i: imports): Import = i.att()

  case class sort(sort: p.Sort) {
    def att(atts: p.Pattern*): SortDeclaration = SortDeclaration(sort, atts)
  }
  implicit def asSortDeclaration(s: sort): SortDeclaration = s.att()

  case class symbol(sort: p.Sort, symbol: p.Symbol, args: p.Sort*) {
    def att(atts: p.Pattern*): SymbolDeclaration = SymbolDeclaration(sort, symbol, args, atts)
  }
  implicit def asSymbolDeclaration(s: symbol): SymbolDeclaration = s.att()

  case class axiom(a: p.Pattern) {
    def att(atts: p.Pattern*): Axiom = Axiom(a, atts)
  }
  implicit def asAxiom(a: axiom): Axiom = a.att()

  // Why have both Rule and Axiom?
  case class rule(l: p.Pattern, r: p.Pattern) {
    def att(atts: p.Pattern*): Axiom = Axiom(Rewrite(l, r), atts)
  }
  implicit def asAxiom(r: rule): Axiom = r.att()

  // building terms
  def term(symbol: p.Symbol, args: p.Pattern*): Application = Application(symbol, args)
}


/** Implementation of the [[org.kframework.minikore.interfaces.build.Builders]] **/
object DefaultBuilders extends build.Builders {

  import org.kframework.minikore.implementation.{MiniKore => m}

  def Variable(_1: p.Name, _2: p.Sort): p.Variable = m.Variable(_1, _2)

  def DomainValue(_1: p.Symbol, _2: p.Value): p.DomainValue = m.DomainValue(_1, _2)

  def Top(): p.Top = m.Top()

  def Bottom(): p.Bottom = m.Bottom()

  def Not(_1: p.Pattern): p.Not = m.Not(_1)

  def Next(_1: p.Pattern): p.Next = m.Next(_1)

  def And(_1: p.Pattern, _2: p.Pattern): p.And = m.And(_1, _2)

  def Or(_1: p.Pattern, _2: p.Pattern): p.Or = m.Or(_1, _2)

  def Implies(_1: p.Pattern, _2: p.Pattern): p.Implies = m.Implies(_1, _2)

  def Equals(_1: p.Pattern, _2: p.Pattern): p.Equals = m.Equals(_1, _2)

  def Exists(_1: p.Variable, _2: p.Pattern): p.Exists = m.Exists(_1, _2)

  def ForAll(_1: p.Variable, _2: p.Pattern): p.ForAll = m.ForAll(_1, _2)

  def Rewrite(_1: p.Pattern, _2: p.Pattern): p.Rewrite = m.Rewrite(_1, _2)

  def Application(_1: p.Symbol, args: Seq[p.Pattern]): p.Application = m.Application(_1, args)
}


