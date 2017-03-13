package org.kframework.minikore

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders


case class MiniKoreMeta(b: Builders) {

  import b._
  import org.kframework.minikore.implementation.MiniKore.{Definition, Module, Sentence, Import, SortDeclaration, SymbolDeclaration, Attributes, Rule, Axiom}
  val patternUtils = MiniKorePatternUtils(b)
  import patternUtils._

  // Meta KLabels
  // ============

  val KSymbol = Symbol("KSymbol")

  val KMLVariable    = Symbol("KMLVariable")
  val KMLDomainValue = Symbol("KMLDomainValue")

  val KMLApplication = Symbol("KMLApplication")
  val KMLTop         = Symbol("KMLTop")
  val KMLBottom      = Symbol("KMLBottom")
  val KMLAnd         = Symbol("KMLAnd")
  val KMLOr          = Symbol("KMLOr")
  val KMLNot         = Symbol("KMLNot")
  val KMLImplies     = Symbol("KMLImplies")
  val KMLExists      = Symbol("KMLExists")
  val KMLForAll      = Symbol("KMLForAll")
  val KMLNext        = Symbol("KMLNext")
  val KMLRewrite     = Symbol("KMLRewrite")
  val KMLEquals      = Symbol("KMLEquals")

  val KMLPatternList   = Symbol("KMLPatternList")
  val KMLPatternListMt = Symbol(".KMLPatternList")

  val KSort              = Symbol("KSort")
  val KSortList          = Symbol("KSortList")
  val KSortListMt        = Symbol(".KSortList")

  val KImport            = Symbol("KImport")
  val KSortDeclaration   = Symbol("KSortDeclaration")
  val KSymbolDeclaration = Symbol("KSymbolDeclaration")
  val KRule              = Symbol("KRule")
  val KAxiom             = Symbol("KAxiom")

  val KAttributes     = Symbol("KAttributes")
  val KAttributesMt   = Symbol(".KAttributes")
  val KSentenceList   = Symbol("KSentenceList")
  val KSentenceListMt = Symbol(".KSentenceList")

  val KModule       = Symbol("KModule")
  val KModuleList   = Symbol("KModuleList")
  val KModuleListMt = Symbol(".KModuleList")
  val KDefinition   = Symbol("KDefinition")

  // Leaf Data
  // =========

  val upDomainValue: DomainValue => Application = { case DomainValue(Symbol(name), value) => Application(KMLDomainValue, Seq(upName(name), upValue(value))) }
  val downDomainValue: Pattern => DomainValue   = { case Application(`KMLDomainValue`, name :: value :: Nil) => DomainValue(Symbol(downName(name)), downValue(value)) }

  val upVariable: Variable => Application = { case Variable(name, sort) => Application(KMLVariable, Seq(upName(name), upSort(sort))) }
  val downVariable: Pattern => Variable   = { case Application(KMLVariable, name :: sort :: Nil) => Variable(downName(name), downSort(sort)) }

  // specific uppers/downer helpers for various pieces of data

  val upSymbol: Symbol => Application = { case Symbol(value) => upDomainValue(DomainValue(KSymbol, value)) }
  val downSymbol: Pattern => Symbol   = downDomainValue andThen { case DomainValue(`KSymbol`, value) => Symbol(value) }

  val upSort: Sort => Application = { case Sort(value) => upDomainValue(DomainValue(KSort, value)) }
  val downSort: Pattern => Sort   = downDomainValue andThen { case DomainValue(`KSort`, value) => Sort(value) }

  val upName: Name => Application = (name: Name) => Application(Symbol(name), Seq.empty)
  val downName: Pattern => Name   = { case Application(Symbol(name), Nil) => name }

  val upValue: Value => Application = (value: Value) => Application(Symbol(value), Seq.empty)
  val downValue: Pattern => Value   = { case Application(Symbol(value), Nil) => value }

  def upSortList(concrete: Seq[Sort]): Application = consListLeft(KSortList, KSortListMt)(concrete map upSort)
  def downSortList(parsed: Pattern): Seq[Sort]     = flattenBySymbols(KSortList, KSortListMt)(parsed) map downSort

  // Pattern Structure
  // =================

  val upPattern: Pattern => Application = {
    case Application(label, Nil)  => Application(KMLApplication, Seq(upSymbol(label)))
    case Application(label, args) => Application(KMLApplication, Seq(upSymbol(label), upPatternList(args)))
    case Top()                    => Application(KMLTop, Seq.empty)
    case Bottom()                 => Application(KMLBottom, Seq.empty)
    case And(p, q)                => Application(KMLAnd, Seq(upPattern(p), upPattern(q)))
    case Or(p, q)                 => Application(KMLOr,  Seq(upPattern(p), upPattern(q)))
    case Not(p)                   => Application(KMLNot,  Seq(upPattern(p)))
    case Implies(p, q)            => Application(KMLImplies,  Seq(upPattern(p), upPattern(q)))
    case Exists(v, p)             => Application(KMLExists,  Seq(upPattern(p)))
    case ForAll(v, p)             => Application(KMLForAll,  Seq(upPattern(p)))
    case Next(p)                  => Application(KMLNext,  Seq(upPattern(p)))
    case Rewrite(p, q)            => Application(KMLRewrite,  Seq(upPattern(p), upPattern(q)))
    case Equals(p, q)             => Application(KMLEquals,  Seq(upPattern(p), upPattern(q)))
    case vb@Variable(_, _)        => upVariable(vb)
    case dv@DomainValue(_, _)     => upDomainValue(dv)
  }
  val downPattern: Pattern => Pattern = {
    case Application(`KMLApplication`, label :: Nil)          => Application(downSymbol(label), Seq.empty)
    case Application(`KMLApplication`, label :: pList :: Nil) => Application(downSymbol(label), downPatternList(pList))
    case Application(`KMLTop`, Nil)                           => Top()
    case Application(`KMLBottom`, Nil)                        => Bottom()
    case Application(`KMLAnd`, p1 :: p2 :: Nil)               => And(downPattern(p1), downPattern(p2))
    case Application(`KMLOr`, p1 :: p2 :: Nil)                => Or(downPattern(p1), downPattern(p2))
    case Application(`KMLNot`, p :: Nil)                      => Not(downPattern(p))
    case Application(`KMLImplies`, p1 :: p2 :: Nil)           => Implies(downPattern(p1), downPattern(p2))
    case Application(`KMLExists`, v :: p :: Nil)              => Exists(downVariable(v), downPattern(p))
    case Application(`KMLForAll`, v :: p :: Nil)              => ForAll(downVariable(v), downPattern(p))
    case Application(`KMLNext`, p :: Nil)                     => Next(downPattern(p))
    case Application(`KMLRewrite`, p1 :: p2 :: Nil)           => Rewrite(downPattern(p1), downPattern(p2))
    case Application(`KMLEquals`, p1 :: p2 :: Nil)            => Equals(downPattern(p1), downPattern(p2))
    case vb@Application(`KMLVariable`, _)                     => downVariable(vb)
    case dv@Application(`KMLDomainValue`, _)                  => downDomainValue(dv)
  }

  def upPatternList(concretes: Seq[Pattern]): Pattern = consListLeft(KMLPatternList, KMLPatternListMt)(concretes map upPattern)
  def downPatternList(parsed: Pattern): Seq[Pattern]  = flattenBySymbols(KMLPatternList, KMLPatternListMt)(parsed) map downPattern

  // Sentences
  // =========

  val upAttributes: Attributes => Pattern = {
    case Nil          => Application(KAttributesMt, Seq.empty)
    case concreteAtts => Application(KAttributes, Seq(upPatternList(concreteAtts)))
  }
  def downAttributes(parsed: Pattern): Attributes = flattenBySymbols(KAttributes, KAttributesMt)(parsed) flatMap downPatternList

  val upSentence: Sentence => Pattern = {
    case Import(name, atts)                         => Application(KImport, Seq(upName(name), upAttributes(atts)))
    case SortDeclaration(sort, atts)                => Application(KSortDeclaration, Seq(upSort(sort), upAttributes(atts)))
    case SymbolDeclaration(sort, label, args, atts) => Application(KSymbolDeclaration, Seq(upSort(sort), upSymbol(label), upSortList(args), upAttributes(atts)))
    case Rule(pattern, atts)                        => Application(KRule, Seq(upPattern(pattern), upAttributes(atts)))
    case Axiom(pattern, atts)                       => Application(KAxiom, Seq(upPattern(pattern), upAttributes(atts)))
  }
  val downSentence: Pattern => Sentence = {
    case Application(`KImport`, name :: atts :: Nil)                             => Import(downName(name), downAttributes(atts))
    case Application(`KSortDeclaration`, sort :: atts :: Nil)                    => SortDeclaration(downSort(sort), downAttributes(atts))
    case Application(`KSymbolDeclaration`, sort :: label :: args :: atts :: Nil) => SymbolDeclaration(downSort(sort), downSymbol(label), downSortList(args), downAttributes(atts))
    case Application(`KRule`, rule :: atts :: Nil)                               => Rule(downPattern(rule), downAttributes(atts))
    case Application(`KAxiom`, rule :: atts :: Nil)                              => Axiom(downPattern(rule), downAttributes(atts))
  }

  // Definitions
  // ===========

  val upModule: Module => Pattern = {
    case Module(name: Name, sentences: Seq[Sentence], atts: Attributes) => Application(KModule, Seq(upName(name), consListLeft(KSentenceList, KSentenceListMt)(sentences map upSentence), upAttributes(atts)))
  }
  val downModule: Pattern => Module = {
    case Application(`KModule`, name :: sentences :: atts :: Nil) => Module(downName(name), flattenBySymbols(KSentenceList, KSentenceListMt)(sentences) map downSentence, downAttributes(atts))
  }

  val upDefinition: Definition => Pattern = {
     case Definition(modules: Seq[Module], atts: Attributes) => Application(KDefinition, Seq(upAttributes(atts), consListLeft(KModuleList, KModuleListMt)(modules map upModule)))
  }
  val downDefinition: Pattern => Definition = {
     case Application(`KDefinition`, atts :: modules :: Nil) => Definition(flattenBySymbols(KModuleList, KModuleListMt)(modules) map downModule, downAttributes(atts))
  }
}
