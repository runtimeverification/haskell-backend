package org.kframework.minikore

import org.kframework.minikore.MiniKore._


object MiniKoreMeta {
  import MiniKorePatternUtils._

  // TODO: I would like to make the downers take things of type Application (instead of Pattern), but that
  // means that all of the recursively downed parts of the matched patterns have to be type annotated, which
  // is quite verbose and ugly. Should we make a new subsort of just Application in a trait called "MetaPattern"
  // or something like that?

  // Patterns
  // ========

  val upDomainValue: DomainValue => Application = { case DomainValue(name, value) => Application("KMLDomainValue", Seq(Application(name, Nil), Application(value, Nil))) }
  val downDomainValue: Pattern => DomainValue   = { case Application("KMLDomainValue", Application(name, Nil) :: Application(value, Nil) :: Nil) => DomainValue(name, value) }

  val upSymbol: String => Application = (value => DomainValue("KSymbol@KTOKENS", value)) andThen upDomainValue
  val downSymbol: Pattern => String   = downDomainValue andThen { case DomainValue("KSymbol@KTOKENS", value) => value }

  def upSymbolList(concrete: Seq[String]): Pattern = consListLeft("KSymbolList", ".KSymbolList")(concrete map upSymbol)
  def downSymbolList(parsed: Pattern): Seq[String] = flattenByLabels("KSymbolList", ".KSymbolList")(parsed) map downSymbol

  val upVariable: Variable => Application = { case Variable(name, sort) => Application("KMLVariable", Seq(Application(name), Application(sort))) }
  val downVariable: Pattern => Variable   = { case Application("KMLVariable", Application(name, Nil) :: Application(sort, Nil) :: Nil) => Variable(name, sort) }

  val upPattern: Pattern => Application = {
    case Application(label, Nil)  => Application("KMLApplication", Seq(Application(label, Seq.empty)))
    case Application(label, args) => Application("KMLApplication", Seq(upSymbol(label), upPatternList(args)))
    case And(p, q)                => Application("KMLAnd", Seq(upPattern(p), upPattern(q)))
    case Or(p, q)                 => Application("KMLOr",  Seq(upPattern(p), upPattern(q)))
    case Not(p)                   => Application("KMLNot",  Seq(upPattern(p)))
    case Implies(p, q)            => Application("KMLImplies",  Seq(upPattern(p), upPattern(q)))
    case Exists(v, p)             => Application("KMLExists",  Seq(upPattern(p)))
    case ForAll(v, p)             => Application("KMLForAll",  Seq(upPattern(p)))
    case Next(p)                  => Application("KMLNext",  Seq(upPattern(p)))
    case Rewrite(p, q)            => Application("KMLRewrite",  Seq(upPattern(p), upPattern(q)))
    case Equal(p, q)              => Application("KMLEqual",  Seq(upPattern(p), upPattern(q)))
    case vb@Variable(_, _)        => upVariable(vb)
    case dv@DomainValue(_, _)     => upDomainValue(dv)
  }
  val downPattern: Pattern => Pattern = {
    case Application("KMLApplication", Application(label, Nil) :: Nil) => Application(label, Seq.empty)
    case Application("KMLApplication", label :: pList :: Nil)          => Application(downSymbol(label), downPatternList(pList))
    case Application("KMLTrue", Nil)                                   => True()
    case Application("KMLFalse", Nil)                                  => False()
    case Application("KMLAnd", p1 :: p2 :: Nil)                        => And(downPattern(p1), downPattern(p2))
    case Application("KMLOr", p1 :: p2 :: Nil)                         => Or(downPattern(p1), downPattern(p2))
    case Application("KMLNot", p :: Nil)                               => Not(downPattern(p))
    case Application("KMLImplies", p1 :: p2 :: Nil)                    => Implies(downPattern(p1), downPattern(p2))
    case Application("KMLExists", v :: p :: Nil)                       => Exists(downVariable(v), downPattern(p))
    case Application("KMLForall", v :: p :: Nil)                       => ForAll(downVariable(v), downPattern(p))
    case Application("KMLNext", p :: Nil)                              => Next(downPattern(p))
    case Application("KMLRewrite", p1 :: p2 :: Nil)                    => Rewrite(downPattern(p1), downPattern(p2))
    case Application("KMLEqual", p1 :: p2 :: Nil)                      => Equal(downPattern(p1), downPattern(p2))
    case vb@Application("KMLVariable", _)                              => downVariable(vb)
    case dv@Application("KMLDomainValue", _)                           => downDomainValue(dv)
  }

  def upPatternList(concretes: Seq[Pattern]): Pattern = consListLeft("KMLPatternList", ".KMLPatternList")(concretes map upPattern)
  def downPatternList(parsed: Pattern): Seq[Pattern] = flattenByLabels("KMLPatternList", ".KMLPatternList")(parsed) map downPattern

  // Sentences
  // =========

  val upAttributes: Attributes => Pattern = {
    case Nil          => Application(".KAttributes", Seq.empty)
    case concreteAtts => Application("KAttributes", Seq(upPatternList(concreteAtts)))
  }
  def downAttributes(parsed: Pattern): Attributes = flattenByLabels("KAttributes", ".KAttributes")(parsed) flatMap downPatternList

  val upSentence: Sentence => Pattern = {
    case Import(name, atts)                         => Application("KImport", Seq(upSymbol(name), upAttributes(atts)))
    case SortDeclaration(sort, atts)                => Application("KSortDeclaration", Seq(upSymbol(sort), upAttributes(atts)))
    case SymbolDeclaration(sort, label, args, atts) => Application("KSymbolDeclaration", Seq(upSymbol(sort), upSymbol(label), upSymbolList(args), upAttributes(atts)))
    case Rule(pattern, atts)                        => Application("KRule", Seq(upPattern(pattern), upAttributes(atts)))
    case Axiom(pattern, atts)                       => Application("KAxiom", Seq(upPattern(pattern), upAttributes(atts)))
  }
  val downSentence: Pattern => Sentence = {
    case Application("KImport", importName :: atts :: Nil)                       => Import(downSymbol(importName), downAttributes(atts))
    case Application("KSortDeclaration", sort :: atts :: Nil)                    => SortDeclaration(downSymbol(sort), downAttributes(atts))
    case Application("KSymbolDeclaration", sort :: label :: args :: atts :: Nil) => SymbolDeclaration(downSymbol(sort), downSymbol(label), downSymbolList(args), downAttributes(atts))
    case Application("KRule", rule :: atts :: Nil)                               => Rule(downPattern(rule), downAttributes(atts))
    case Application("KAxiom", rule :: atts :: Nil)                              => Axiom(downPattern(rule), downAttributes(atts))
  }

  // Definitions
  // ===========

  val upModule: Module => Pattern = {
    case Module(name: String, sentences: Seq[Sentence], atts: Attributes) => Application("KModule", Seq(upSymbol(name), consListLeft("KSentenceList", ".KSentenceList")(sentences map upSentence), upAttributes(atts)))
  }
  val downModule: Pattern => Module = {
    case Application("KModule", name :: sentences :: atts :: Nil) => Module(downSymbol(name), flattenByLabels("KSentenceList", ".KSentenceList")(sentences) map downSentence, downAttributes(atts))
  }

  val upDefinition: Definition => Pattern = {
     case Definition(modules: Seq[Module], atts: Attributes) => Application("KDefinition", Seq(upAttributes(atts), consListLeft("KModuleList", ".KModuleList")(modules map upModule)))
  }
  val downDefinition: Pattern => Definition = {
     case Application("KDefinition", atts :: modules :: Nil) => Definition(flattenByLabels("KModuleList", ".KModuleList")(modules) map downModule, downAttributes(atts))
  }
}
