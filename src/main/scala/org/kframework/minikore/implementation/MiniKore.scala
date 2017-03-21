package org.kframework.minikore.implementation

import org.kframework.minikore.interfaces.{build, pattern => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore {

  /** A collection of classes that serve as the default implementation of the [[org.kframework.minikore.interfaces.pattern]] **/

  type Attributes = Seq[i.Pattern]

  case class Definition(modules: Seq[Module], att: Attributes) {

    val sorts: Set[i.Sort] = modules flatMap (_.sorts) toSet

    val symbols: Set[i.Symbol] = modules flatMap (_.symbols) toSet
  }

  case class Module(name: i.Name, sentences: Seq[Sentence], att: Attributes) {

    val sorts: Set[i.Sort] = sentences collect {
      case SortDeclaration(sort, _)         => sort
      case SymbolDeclaration(sort, _, _, _) => sort
    } toSet

    val symbols: Set[i.Symbol] = sentences collect {
      case SymbolDeclaration(_, symbol, _, _) => symbol
    } toSet
  }

  sealed trait Sentence

  case class Import(name: i.Name, att: Attributes) extends Sentence

  case class SortDeclaration(sort: i.Sort, att: Attributes) extends Sentence

  case class SymbolDeclaration(sort: i.Sort, symbol: i.Symbol, args: Seq[i.Sort], att: Attributes) extends Sentence

  case class Rule(pattern: i.Pattern, att: Attributes) extends Sentence

  case class Axiom(pattern: i.Pattern, att: Attributes) extends Sentence

  case class Variable(_1: i.Name, _2: i.Sort) extends i.Variable {
    def build(_1: i.Name, _2: i.Sort): Variable = Variable(_1, _2)
  }

  case class DomainValue(_1: i.Symbol, _2: i.Value) extends i.DomainValue {
    def build(_1: i.Symbol, _2: i.Value): DomainValue = DomainValue(_1, _2)
  }

  case class Application(_1: i.Symbol, args: Seq[i.Pattern]) extends i.Application {
    def build(_1: i.Symbol, args: Seq[i.Pattern]): Application = Application(_1, args)
  }

  case class Top() extends i.Top {
    def build(): Top = Top()
  }

  case class Bottom() extends i.Bottom {
    def build(): Bottom = Bottom()
  }

  case class And(_1: i.Pattern, _2: i.Pattern) extends i.And {
    def build(_1: i.Pattern, _2: i.Pattern): And = And(_1, _2)
  }

  case class Or(_1: i.Pattern, _2: i.Pattern) extends i.Or {
    def build(_1: i.Pattern, _2: i.Pattern): Or = Or(_1, _2)
  }

  case class Not(_1: i.Pattern) extends i.Not {
    def build(_1: i.Pattern): Not = Not(_1)
  }

  case class Implies(_1: i.Pattern, _2: i.Pattern) extends i.Implies {
    def build(_1: i.Pattern, _2: i.Pattern): Implies = Implies(_1, _2)
  }

  case class Exists(_1: i.Variable, _2: i.Pattern) extends i.Exists {
    def build(_1: i.Variable, _2: i.Pattern): Exists = Exists(_1, _2)
  }

  case class ForAll(_1: i.Variable, _2: i.Pattern) extends i.ForAll {
    def build(_1: i.Variable, _2: i.Pattern): ForAll = ForAll(_1, _2)
  }

  case class Next(_1: i.Pattern) extends i.Next {
    def build(_1: i.Pattern): Next = Next(_1)
  }

  case class Rewrite(_1: i.Pattern, _2: i.Pattern) extends i.Rewrite {
    def build(_1: i.Pattern, _2: i.Pattern): Rewrite = Rewrite(_1, _2)
  }

  case class Equals(_1: i.Pattern, _2: i.Pattern) extends i.Equals {
    def build(_1: i.Pattern, _2: i.Pattern): Equals = Equals(_1, _2)
  }

}


/** Helpers for building MiniKore definitions **/
object MiniKoreDSL {

  import MiniKore._

  // Show Name and Value have wrappers? What exactly are their roles?
  implicit def asSort(s: String): i.Sort     = i.Sort(s)
  implicit def asSymbol(s: String): i.Symbol = i.Symbol(s)
  //implicit def asName(s: String): i.Name = i.Name(s)
  //implicit def asValue(s: String): i.Value = i.Value(s)

  case class definition(modules: Module*) {
    def att(atts: i.Pattern*): Definition = Definition(modules, atts)
  }
  implicit def asDefinition(d: definition): Definition = d.att()

  case class module(name: i.Name, sentences: Sentence*) {
    def att(atts: i.Pattern*): Module = Module(name, sentences, atts)
  }
  implicit def asModule(m: module): Module = m.att()

  case class imports(name: i.Name) {
    def att(atts: i.Pattern*): Import = Import(name, atts)
  }
  implicit def asImport(i: imports): Import = i.att()

  case class sort(sort: i.Sort) {
    def att(atts: i.Pattern*): SortDeclaration = SortDeclaration(sort, atts)
  }
  implicit def asSortDeclaration(s: sort): SortDeclaration = s.att()

  case class symbol(sort: i.Sort, symbol: i.Symbol, args: i.Sort*) {
    def att(atts: i.Pattern*): SymbolDeclaration = SymbolDeclaration(sort, symbol, args, atts)
  }
  implicit def asSymbolDeclaration(s: symbol): SymbolDeclaration = s.att()

  case class axiom(p: i.Pattern) {
    def att(atts: i.Pattern*): Axiom = Axiom(p, atts)
  }
  implicit def asAxiom(a: axiom): Axiom = a.att()

  // Why have both Rule and Axiom?
  case class rule(l: i.Pattern, r: i.Pattern) {
    def att(atts: i.Pattern*): Axiom = Axiom(Rewrite(l, r), atts)
  }
  implicit def asAxiom(r: rule): Axiom = r.att()

  // building terms
  def term(symbol: i.Symbol, args: i.Pattern*): Application = Application(symbol, args)
}


/** Implementation of the [[org.kframework.minikore.interfaces.build.Builders]] **/
object DefaultBuilders extends build.Builders {

  import org.kframework.minikore.implementation.{MiniKore => m}

  def Variable(_1: i.Name, _2: i.Sort): i.Variable = m.Variable(_1, _2)

  def DomainValue(_1: i.Symbol, _2: i.Value): i.DomainValue = m.DomainValue(_1, _2)

  def Top(): i.Top = m.Top()

  def Bottom(): i.Bottom = m.Bottom()

  def Not(_1: i.Pattern): i.Not = m.Not(_1)

  def Next(_1: i.Pattern): i.Next = m.Next(_1)

  def And(_1: i.Pattern, _2: i.Pattern): i.And = m.And(_1, _2)

  def Or(_1: i.Pattern, _2: i.Pattern): i.Or = m.Or(_1, _2)

  def Implies(_1: i.Pattern, _2: i.Pattern): i.Implies = m.Implies(_1, _2)

  def Equals(_1: i.Pattern, _2: i.Pattern): i.Equals = m.Equals(_1, _2)

  def Exists(_1: i.Variable, _2: i.Pattern): i.Exists = m.Exists(_1, _2)

  def ForAll(_1: i.Variable, _2: i.Pattern): i.ForAll = m.ForAll(_1, _2)

  def Rewrite(_1: i.Pattern, _2: i.Pattern): i.Rewrite = m.Rewrite(_1, _2)

  def Application(_1: i.Symbol, args: Seq[i.Pattern]): i.Application = m.Application(_1, args)
}


