package org.kframework.minikore.implementation


object outer {

  import org.kframework.minikore.interfaces.{pattern => p}
  import org.kframework.minikore.interfaces.{outer => o}

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

  object DefaultBuilders extends o.Builders {
    def Definition(modules: Seq[o.Module], att: o.Attributes): o.Definition = Definition(modules, att)

    def Module(name: p.Name, sentences: Seq[o.Sentence], att: o.Attributes): o.Module = Module(name, sentences, att)

    def Import(name: p.Name, att: o.Attributes): o.Import = Import(name, att)

    def SortDeclaration(sort: p.Sort, att: o.Attributes): o.SortDeclaration = SortDeclaration(sort, att)

    def SymbolDeclaration(sort: p.Sort, symbol: p.Symbol, args: Seq[p.Sort], att: o.Attributes): o.SymbolDeclaration = SymbolDeclaration(sort, symbol, args, att)

    def Rule(pattern: p.Pattern, att: o.Attributes): o.Rule = Rule(pattern, att)

    def Axiom(pattern: p.Pattern, att: o.Attributes): o.Axiom = Axiom(pattern, att)
  }
}
