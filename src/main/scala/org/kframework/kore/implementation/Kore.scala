package org.kframework.kore.implementation

import org.kframework.kore.interfaces.{outer => o}
import org.kframework.kore.interfaces.{pattern => p}
import org.kframework.kore.interfaces.builders.OuterBuilders
import org.kframework.kore.interfaces.builders.PatternBuilders

import scala.collection._

/** Algebraic data type of MiniKore. */ // TODO: should rename to "pattern"
object DefaultPattern {

  /** A collection of classes that serve as the default implementation of the [[org.kframework.kore.interfaces.pattern]] **/

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


object DefaultOuter {

  case class Definition(modules: Seq[o.Module], att: o.Attributes) extends o.Definition {
    override def onAttributes(f: p.Pattern => p.Pattern): Definition = Definition(modules.map(_.onAttributes(f)), att.map(f))
  }

  case class Module(name: p.Name, sentences: Seq[o.Sentence], att: o.Attributes) extends o.Module {
    override def onAttributes(f: p.Pattern => p.Pattern): Module = Module(name, sentences.map(_.onAttributes(f)), att.map(f))
  }

  case class Import(name: p.Name, att: o.Attributes) extends o.Import {
    override def onAttributes(f: p.Pattern => p.Pattern): Import = Import(name, att.map(f))
  }

  case class SortDeclaration(sort: p.Sort, att: o.Attributes) extends o.SortDeclaration {
    override def onAttributes(f: p.Pattern => p.Pattern): SortDeclaration = SortDeclaration(sort, att.map(f))
  }

  case class SymbolDeclaration(sort: p.Sort, symbol: p.Symbol, args: Seq[p.Sort], att: o.Attributes) extends o.SymbolDeclaration {
    override def onAttributes(f: p.Pattern => p.Pattern): SymbolDeclaration = SymbolDeclaration(sort, symbol, args, att.map(f))
  }

  case class Rule(pattern: p.Pattern, att: o.Attributes) extends o.Rule {
    override def onAttributes(f: p.Pattern => p.Pattern): Rule = Rule(pattern, att.map(f))
  }

  case class Axiom(pattern: p.Pattern, att: o.Attributes) extends o.Axiom {
    override def onAttributes(f: p.Pattern => p.Pattern): Axiom = Axiom(pattern, att.map(f))
  }
}

object builders {

  object DefaultOuterBuilders extends OuterBuilders {
    def Definition(modules: Seq[o.Module], att: o.Attributes): o.Definition = DefaultOuter.Definition(modules, att)
    def Module(name: p.Name, sentences: Seq[o.Sentence], att: o.Attributes): o.Module = DefaultOuter.Module(name, sentences, att)
    def Import(name: p.Name, att: o.Attributes): o.Import = DefaultOuter.Import(name, att)
    def SortDeclaration(sort: p.Sort, att: o.Attributes): o.SortDeclaration = DefaultOuter.SortDeclaration(sort, att)
    def SymbolDeclaration(sort: p.Sort, symbol: p.Symbol, args: Seq[p.Sort], att: o.Attributes): o.SymbolDeclaration = DefaultOuter.SymbolDeclaration(sort, symbol, args, att)
    def Rule(pattern: p.Pattern, att: o.Attributes): o.Rule = DefaultOuter.Rule(pattern, att)
    def Axiom(pattern: p.Pattern, att: o.Attributes): o.Axiom = DefaultOuter.Axiom(pattern, att)
  }

  /** Implementation of the [[org.kframework.kore.interfaces.builders.PatternBuilders]] **/
  object DefaultPatternBuilders extends PatternBuilders {
    def Variable(_1: p.Name, _2: p.Sort): p.Variable = DefaultPattern.Variable(_1, _2)
    def DomainValue(_1: p.Symbol, _2: p.Value): p.DomainValue = DefaultPattern.DomainValue(_1, _2)
    def Top(): p.Top = DefaultPattern.Top()
    def Bottom(): p.Bottom = DefaultPattern.Bottom()
    def Not(_1: p.Pattern): p.Not = DefaultPattern.Not(_1)
    def Next(_1: p.Pattern): p.Next = DefaultPattern.Next(_1)
    def And(_1: p.Pattern, _2: p.Pattern): p.And = DefaultPattern.And(_1, _2)
    def Or(_1: p.Pattern, _2: p.Pattern): p.Or = DefaultPattern.Or(_1, _2)
    def Implies(_1: p.Pattern, _2: p.Pattern): p.Implies = DefaultPattern.Implies(_1, _2)
    def Equals(_1: p.Pattern, _2: p.Pattern): p.Equals = DefaultPattern.Equals(_1, _2)
    def Exists(_1: p.Variable, _2: p.Pattern): p.Exists = DefaultPattern.Exists(_1, _2)
    def ForAll(_1: p.Variable, _2: p.Pattern): p.ForAll = DefaultPattern.ForAll(_1, _2)
    def Rewrite(_1: p.Pattern, _2: p.Pattern): p.Rewrite = DefaultPattern.Rewrite(_1, _2)
    def Application(_1: p.Symbol, args: Seq[p.Pattern]): p.Application = DefaultPattern.Application(_1, args)
  }

}

