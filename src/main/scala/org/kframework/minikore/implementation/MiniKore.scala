package org.kframework.minikore.implementation

import org.kframework.minikore.interfaces.{pattern => p}

import scala.collection._

/** Algebraic data type of MiniKore. */ // TODO: should rename to "pattern"
object pattern {

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

  /** Implementation of the [[org.kframework.minikore.interfaces.build.Builders]] **/
  object DefaultPatternBuilders extends p.PatternBuilders {
    def Variable(_1: p.Name, _2: p.Sort): p.Variable = Variable(_1, _2)

    def DomainValue(_1: p.Symbol, _2: p.Value): p.DomainValue = DomainValue(_1, _2)

    def Top(): p.Top = Top()

    def Bottom(): p.Bottom = Bottom()

    def Not(_1: p.Pattern): p.Not = Not(_1)

    def Next(_1: p.Pattern): p.Next = Next(_1)

    def And(_1: p.Pattern, _2: p.Pattern): p.And = And(_1, _2)

    def Or(_1: p.Pattern, _2: p.Pattern): p.Or = Or(_1, _2)

    def Implies(_1: p.Pattern, _2: p.Pattern): p.Implies = Implies(_1, _2)

    def Equals(_1: p.Pattern, _2: p.Pattern): p.Equals = Equals(_1, _2)

    def Exists(_1: p.Variable, _2: p.Pattern): p.Exists = Exists(_1, _2)

    def ForAll(_1: p.Variable, _2: p.Pattern): p.ForAll = ForAll(_1, _2)

    def Rewrite(_1: p.Pattern, _2: p.Pattern): p.Rewrite = Rewrite(_1, _2)

    def Application(_1: p.Symbol, args: Seq[p.Pattern]): p.Application = Application(_1, args)
  }
}
