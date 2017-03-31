package org.kframework.minikore.implementation

import org.kframework.minikore.interfaces.outer.OuterBuilders
import org.kframework.minikore.interfaces.pattern.PatternBuilders

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

  object DefaultOuterBuilders extends o.OuterBuilders {
    def Definition(modules: Seq[o.Module], att: o.Attributes): o.Definition = Definition(modules, att)

    def Module(name: p.Name, sentences: Seq[o.Sentence], att: o.Attributes): o.Module = Module(name, sentences, att)

    def Import(name: p.Name, att: o.Attributes): o.Import = Import(name, att)

    def SortDeclaration(sort: p.Sort, att: o.Attributes): o.SortDeclaration = SortDeclaration(sort, att)

    def SymbolDeclaration(sort: p.Sort, symbol: p.Symbol, args: Seq[p.Sort], att: o.Attributes): o.SymbolDeclaration = SymbolDeclaration(sort, symbol, args, att)

    def Rule(pattern: p.Pattern, att: o.Attributes): o.Rule = Rule(pattern, att)

    def Axiom(pattern: p.Pattern, att: o.Attributes): o.Axiom = Axiom(pattern, att)
  }
}

/** Helpers for building MiniKore definitions **/
case class MiniKoreDSL(ob: OuterBuilders, pb: PatternBuilders) {

  import org.kframework.minikore.interfaces.{outer => o}
  import org.kframework.minikore.interfaces.{pattern => p}

  // Show Name and Value have wrappers? What exactly are their roles?
  implicit def asSort(s: String): p.Sort     = p.Sort(s)
  implicit def asSymbol(s: String): p.Symbol = p.Symbol(s)
  //implicit def asName(s: String): p.Name = pb.Name(s)
  //implicit def asValue(s: String): p.Value = pb.Value(s)

  case class definition(modules: o.Module*) {
    def att(atts: p.Pattern*): o.Definition = ob.Definition(modules, atts)
  }
  implicit def asDefinition(d: definition): o.Definition = d.att()

  case class module(name: p.Name, sentences: o.Sentence*) {
    def att(atts: p.Pattern*): o.Module = ob.Module(name, sentences, atts)
  }
  implicit def asModule(m: module): o.Module = m.att()

  case class imports(name: p.Name) {
    def att(atts: p.Pattern*): o.Import = ob.Import(name, atts)
  }
  implicit def asImport(i: imports): o.Import = i.att()

  case class sort(sort: p.Sort) {
    def att(atts: p.Pattern*): o.SortDeclaration = ob.SortDeclaration(sort, atts)
  }
  implicit def asSortDeclaration(s: sort): o.SortDeclaration = s.att()

  case class symbol(sort: p.Sort, symbol: p.Symbol, args: p.Sort*) {
    def att(atts: p.Pattern*): o.SymbolDeclaration = ob.SymbolDeclaration(sort, symbol, args, atts)
  }
  implicit def asSymbolDeclaration(s: symbol): o.SymbolDeclaration = s.att()

  case class axiom(a: p.Pattern) {
    def att(atts: p.Pattern*): o.Axiom = ob.Axiom(a, atts)
  }
  implicit def asAxiom(a: axiom): o.Axiom = a.att()

  // Why have both Rule and Axiom?
  case class rule(l: p.Pattern, r: p.Pattern) {
    def att(atts: p.Pattern*): o.Axiom = ob.Axiom(pb.Rewrite(l, r), atts)
  }
  implicit def asAxiom(r: rule): o.Axiom = r.att()

  // building terms
  def term(symbol: p.Symbol, args: p.Pattern*): p.Application = pb.Application(symbol, args)
}
