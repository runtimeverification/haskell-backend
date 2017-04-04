package org.kframework.kore

import org.kframework.kore.interfaces.builders.OuterBuilders
import org.kframework.kore.interfaces.builders.PatternBuilders
import org.kframework.kore.interfaces.{pattern => p}
import org.kframework.kore.interfaces.{outer => o}

/**
  * Created by lpena on 4/4/17.
  */
/** Helpers for building MiniKore definitions **/
case class KoreDSL(ob: OuterBuilders, pb: PatternBuilders) {

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
