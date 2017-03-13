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

  val KSymbol = Symbol("#Symbol")
  val KSort   = Symbol("#Sort")
  val KName   = Symbol("#Name")
  val KValue  = Symbol("#Value")

  val KSortList   = Symbol("#SortList")
  val KSortListMt = Symbol("#.SortList")

  val KVariable    = Symbol("#Variable")
  val KDomainValue = Symbol("#DomainValue")

  val KApplication = Symbol("#Application")
  val KTop         = Symbol("#Top")
  val KBottom      = Symbol("#Bottom")
  val KAnd         = Symbol("#And")
  val KOr          = Symbol("#Or")
  val KNot         = Symbol("#Not")
  val KImplies     = Symbol("#Implies")
  val KExists      = Symbol("#Exists")
  val KForAll      = Symbol("#ForAll")
  val KNext        = Symbol("#Next")
  val KRewrite     = Symbol("#Rewrite")
  val KEquals      = Symbol("#Equals")

  val KPatternList   = Symbol("#PatternList")
  val KPatternListMt = Symbol("#.PatternList")

  val KImport            = Symbol("#Import")
  val KSortDeclaration   = Symbol("#SortDeclaration")
  val KSymbolDeclaration = Symbol("#SymbolDeclaration")
  val KRule              = Symbol("#Rule")
  val KAxiom             = Symbol("#Axiom")

  val KAttributes     = Symbol("#Attributes")
  val KAttributesMt   = Symbol("#.Attributes")
  val KSentenceList   = Symbol("#SentenceList")
  val KSentenceListMt = Symbol("#.SentenceList")

  val KModule       = Symbol("#Module")
  val KModuleList   = Symbol("#ModuleList")
  val KModuleListMt = Symbol("#.ModuleList")
  val KDefinition   = Symbol("#Definition")

  // Leaf Data
  // =========

  val upDomainValue: DomainValue => Application = { case DomainValue(symbol, value) => Application(KDomainValue, Seq(upSymbol(symbol), upValue(value))) }
  val downDomainValue: Pattern => DomainValue   = { case Application(`KDomainValue`, symbol :: value :: Nil) => DomainValue(downSymbol(symbol), downValue(value)) }

  val upVariable: Variable => Application = { case Variable(name, sort) => Application(KVariable, Seq(upName(name), upSort(sort))) }
  val downVariable: Pattern => Variable   = { case Application(KVariable, name :: sort :: Nil) => Variable(downName(name), downSort(sort)) }

  // specific uppers/downer helpers for various pieces of data

  val upSymbol: Symbol => DomainValue = { case Symbol(symbol) => DomainValue(KSymbol, symbol) }
  val downSymbol: Pattern => Symbol   = { case DomainValue(`KSymbol`, symbol) => Symbol(symbol) }

  val upSort: Sort => DomainValue = { case Sort(sort) => DomainValue(KSort, sort) }
  val downSort: Pattern => Sort   = { case DomainValue(`KSort`, sort) => Sort(sort) }

  val upName: Name => DomainValue = { case name => DomainValue(KName, name) }
  val downName: Pattern => Name   = { case DomainValue(`KName`, name) => name }

  val upValue: Value => DomainValue = { case value => DomainValue(KValue, value) }
  val downValue: Pattern => Value   = { case DomainValue(`KValue`, value) => value }

  def upSortList(concrete: Seq[Sort]): Application = consListLeft(KSortList, KSortListMt)(concrete map upSort)
  def downSortList(parsed: Pattern): Seq[Sort]     = flattenBySymbols(KSortList, KSortListMt)(parsed) map downSort

  // Pattern Structure
  // =================

  val upPattern: Pattern => Application = {
    case Application(label, Nil)  => Application(KApplication, Seq(upSymbol(label)))
    case Application(label, args) => Application(KApplication, Seq(upSymbol(label), upPatternList(args)))
    case Top()                    => Application(KTop, Seq.empty)
    case Bottom()                 => Application(KBottom, Seq.empty)
    case And(p, q)                => Application(KAnd, Seq(upPattern(p), upPattern(q)))
    case Or(p, q)                 => Application(KOr, Seq(upPattern(p), upPattern(q)))
    case Not(p)                   => Application(KNot, Seq(upPattern(p)))
    case Implies(p, q)            => Application(KImplies, Seq(upPattern(p), upPattern(q)))
    case Exists(v, p)             => Application(KExists, Seq(upVariable(v), upPattern(p)))
    case ForAll(v, p)             => Application(KForAll, Seq(upVariable(v), upPattern(p)))
    case Next(p)                  => Application(KNext, Seq(upPattern(p)))
    case Rewrite(p, q)            => Application(KRewrite, Seq(upPattern(p), upPattern(q)))
    case Equals(p, q)             => Application(KEquals, Seq(upPattern(p), upPattern(q)))
    case vb@Variable(_, _)        => upVariable(vb)
    case dv@DomainValue(_, _)     => upDomainValue(dv)
  }
  val downPattern: Pattern => Pattern = {
    case Application(`KApplication`, label :: Nil)          => Application(downSymbol(label), Seq.empty)
    case Application(`KApplication`, label :: pList :: Nil) => Application(downSymbol(label), downPatternList(pList))
    case Application(`KTop`, Nil)                           => Top()
    case Application(`KBottom`, Nil)                        => Bottom()
    case Application(`KAnd`, p1 :: p2 :: Nil)               => And(downPattern(p1), downPattern(p2))
    case Application(`KOr`, p1 :: p2 :: Nil)                => Or(downPattern(p1), downPattern(p2))
    case Application(`KNot`, p :: Nil)                      => Not(downPattern(p))
    case Application(`KImplies`, p1 :: p2 :: Nil)           => Implies(downPattern(p1), downPattern(p2))
    case Application(`KExists`, v :: p :: Nil)              => Exists(downVariable(v), downPattern(p))
    case Application(`KForAll`, v :: p :: Nil)              => ForAll(downVariable(v), downPattern(p))
    case Application(`KNext`, p :: Nil)                     => Next(downPattern(p))
    case Application(`KRewrite`, p1 :: p2 :: Nil)           => Rewrite(downPattern(p1), downPattern(p2))
    case Application(`KEquals`, p1 :: p2 :: Nil)            => Equals(downPattern(p1), downPattern(p2))
    case vb@Application(`KVariable`, _)                     => downVariable(vb)
    case dv@Application(`KDomainValue`, _)                  => downDomainValue(dv)
  }

  def upPatternList(concretes: Seq[Pattern]): Pattern = consListLeft(KPatternList, KPatternListMt)(concretes map upPattern)
  def downPatternList(parsed: Pattern): Seq[Pattern]  = flattenBySymbols(KPatternList, KPatternListMt)(parsed) map downPattern

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
