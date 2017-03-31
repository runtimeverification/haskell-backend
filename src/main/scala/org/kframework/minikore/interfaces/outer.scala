package org.kframework.minikore.interfaces

/**
  * Created by lpena on 3/23/17.
  */
object outer {

  import org.kframework.minikore.interfaces.{pattern => p}

  type Attributes = Seq[p.Pattern]

  trait HasAttributes {
    val att: Attributes

    def onAttributes(f: p.Pattern => p.Pattern): HasAttributes

    // Derived operations
    // TODO: Do we want `collect` written with dotless notation as well?
    def getBySymbol(key: p.Symbol): Seq[Seq[p.Pattern]] = att collect { case p.Application(`key`, args) => args }

    def onAttributeBySymbol(key: p.Symbol)(f: p.Pattern => p.Pattern): HasAttributes = onAttributes {
      case app@p.Application(`key`, _) => f(app)
      case pattern                     => pattern
    }

    def updateAttribute(key: p.Symbol, value: p.Pattern*): HasAttributes = onAttributeBySymbol(key) {
      case a@p.Application(`key`, _) => a.build(key, value)
    }
  }

  trait Definition extends HasAttributes {
    val modules: Seq[Module]

    // Derived operations
    lazy val sorts: Set[p.Sort] = modules.flatMap(_.sorts).toSet
    lazy val symbols: Set[p.Symbol] = modules.flatMap(_.symbols).toSet
    lazy val sentences: Seq[Sentence] = modules.flatMap(_.sentences)

    override def onAttributes(f: p.Pattern => p.Pattern): Definition
  }
  object Definition {
    def unapply(arg: Definition): Option[(Seq[Module], Attributes)] = Some(arg.modules, arg.att)
  }

  trait Module extends HasAttributes {
    val name: p.Name
    val sentences: Seq[Sentence]

    // Derived operations
    lazy val sorts: Set[p.Sort] = sentences.flatMap(_.sorts).toSet
    lazy val symbols: Set[p.Symbol] = sentences.flatMap(_.symbols).toSet

    override def onAttributes(f: p.Pattern => p.Pattern): Module
  }
  object Module {
    def unapply(arg: Module): Option[(p.Name, Seq[Sentence], Attributes)] = Some(arg.name, arg.sentences, arg.att)
  }

  trait Sentence extends HasAttributes {
    lazy val sorts: Set[p.Sort] = Set.empty
    lazy val symbols: Set[p.Symbol] = Set.empty

    override def onAttributes(f: p.Pattern => p.Pattern): Sentence
  }

  trait Import extends Sentence {
    val name: p.Name

    override def onAttributes(f: p.Pattern => p.Pattern): Import
  }
  object Import {
    def unapply(arg: Import): Option[(p.Name, Attributes)] = Some(arg.name, arg.att)
  }

  trait SortDeclaration extends Sentence {
    val sort: p.Sort

    override lazy val sorts = Set(sort)

    override def onAttributes(f: p.Pattern => p.Pattern): SortDeclaration
  }
  object SortDeclaration {
    def unapply(arg: SortDeclaration): Option[(p.Sort, Attributes)] = Some(arg.sort, arg.att)
  }

  trait SymbolDeclaration extends Sentence {
    val sort: p.Sort
    val symbol: p.Symbol
    val args: Seq[p.Sort]

    // TODO: Should `sorts` include the `args` here as well?
    override lazy val sorts = Set(sort)
    override lazy val symbols = Set(symbol)

    override def onAttributes(f: p.Pattern => p.Pattern): SymbolDeclaration
  }
  object SymbolDeclaration {
    def unapply(arg: SymbolDeclaration): Option[(p.Sort, p.Symbol, Seq[p.Sort], Attributes)] = Some(arg.sort, arg.symbol, arg.args, arg.att)
  }

  trait Rule extends Sentence {
    val pattern: p.Pattern

    override def onAttributes(f: p.Pattern => p.Pattern): Rule
  }
  object Rule {
    def unapply(arg: Rule): Option[(p.Pattern, Attributes)] = Some(arg.pattern, arg.att)
  }

  trait Axiom extends Sentence {
    val pattern: p.Pattern

    override def onAttributes(f: p.Pattern => p.Pattern): Axiom
  }
  object Axiom {
    def unapply(arg: Axiom): Option[(p.Pattern, Attributes)] = Some(arg.pattern, arg.att)
  }

  // TODO: Is there a reason that Builders is outside the `pattern` object in the pattern interface?
  trait Builders {
    def Definition(modules: Seq[Module], att: Attributes): Definition

    def Module(name: p.Name, sentences: Seq[Sentence], att: Attributes): Module

    def Import(name: p.Name, att: Attributes): Import

    def SortDeclaration(sort: p.Sort, att: Attributes): SortDeclaration

    def SymbolDeclaration(sort: p.Sort, symbol: p.Symbol, args: Seq[p.Sort], att: Attributes): SymbolDeclaration

    def Rule(pattern: p.Pattern, att: Attributes): Rule

    def Axiom(pattern: p.Pattern, att: Attributes): Axiom
  }

}
