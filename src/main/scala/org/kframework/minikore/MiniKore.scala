package org.kframework.minikore

import org.kframework.minikore.MiniKore._


// The main Kore Interface.
object MiniKore {

  trait AST

  trait Node[T] extends AST {
    val label: T
    val children: Seq[AST]
  }

  object Node {
    def unapply(arg: Node[_]): Option[(_, Seq[AST])] = Some((arg.label, arg.children))
  }

  trait Leaf[T] extends AST {
    val content: T
  }

  object Leaf {
    def unapply(arg: Leaf[_]): Option[_] = Some(arg.content)
  }

  type Attributes = Seq[Pattern]

  trait Definition {
    val modules: Seq[Module]
    val att: Attributes
  }

  object Definition {
    def unapply(arg: Definition): Option[(Seq[Module], Attributes)] = Some((arg.modules, arg.att))
  }

  trait Module {
    val name: String
    val sentences: Seq[Sentence]
    val att: Attributes
  }

  object Module {
    def unapply(arg: Module): Option[(String, Seq[Sentence], Attributes)] = Some((arg.name, arg.sentences, arg.att))
  }

  trait Sentence

  trait Import extends Sentence {
    val name: String
    val att: Attributes
  }

  object Import {
    def unapply(arg: Import): Option[(String, Attributes)] = Some((arg.name, arg.att))
  }

  trait SortDeclaration extends Sentence {
    val sort: String
    val att: Attributes
  }

  object SortDeclaration {
    def unapply(arg: SortDeclaration): Option[(String, Attributes)] = Some((arg.sort, arg.att))
  }

  trait SymbolDeclaration extends Sentence {
    val sort: String
    val label: String
    val args: Seq[String]
    val att: Attributes
  }

  object SymbolDeclaration {
    def unapply(arg: SymbolDeclaration): Option[(String, String, Seq[String], Attributes)] = Some((arg.sort, arg.label, arg.args, arg.att))
  }

  trait Rule extends Sentence {
    val p: Pattern
    val att: Attributes
  }

  object Rule {
    def unapply(arg: Rule): Option[(Pattern, Attributes)] = Some((arg.p, arg.att))
  }


  trait Axiom extends Sentence {
    val p: Pattern
    val att: Attributes
  }

  object Axiom {
    def unapply(arg: Axiom): Option[(Pattern, Attributes)] = Some((arg.p, arg.att))
  }


  // Pattern trait + traits
  trait Pattern extends AST

  trait Variable extends Pattern with Leaf[(String, String)]{
    val name: String
    val sort: String
  }

  object Variable {
    def unapply(arg: Variable): Option[(String, String)] = Some((arg.name, arg.sort))
  }

  trait Application extends Pattern with Node[String] {
    val label: String
    val args: Seq[Pattern]
  }

  object Application extends Pattern {
    def unapply(arg: Application): Option[(String, Seq[Pattern])] = Some((arg.label, arg.args))
  }

  trait DomainValue extends Pattern with Leaf[(String, String)] {
    val label: String
    val value: String
  }

  object DomainValue extends Pattern {
    def unapply(arg: DomainValue): Option[(String, String)] = Some((arg.label, arg.value))
  }

  //
  trait True extends Pattern with Leaf[Boolean]

  object True {
    def unapply(arg: True): Boolean = true
  }

  trait False extends Pattern with Leaf[Boolean]

  object False {
    def unapply(arg: False): Boolean = true
  }


  //
  trait And extends Pattern with Node[String] {
    val p: Pattern
    val q: Pattern
  }

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  trait Or extends Pattern with Node[String] {
    val p: Pattern
    val q: Pattern
  }

  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  trait Not extends Pattern with Node[String] {
    val p: Pattern
  }

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }

  trait Implies extends Pattern with Node[String] {
    val p: Pattern
    val q: Pattern
  }

  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  trait Exists extends Pattern with Node[String]{
    val v: Variable
    val p: Pattern
  }

  object Exists {
    def unapply(arg: Exists): Option[(Pattern, Pattern)] = Some((arg.v, arg.p))
  }

  trait ForAll extends Pattern with Node[String] {
    val v: Variable
    val p: Pattern
  }

  object ForAll {
    def unapply(arg: ForAll): Option[(Pattern, Pattern)] = Some((arg.v, arg.p))
  }

  //
  trait Next extends Pattern with Node[String] {
    val p: Pattern
  }

  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg.p)
  }

  trait Rewrite extends Pattern with Node[String] {
    val p: Pattern
    val q: Pattern
  }

  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  trait Equals extends Pattern with Node[String] {
    val p: Pattern
    val q: Pattern
  }

  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

}


// Provided Implementation for the Kore Interface
object DefaultImplementation {

  case class ConcreteDefinition(modules: Seq[Module], att: Attributes) extends Definition

  case class ConcreteModule(name: String, sentences: Seq[Sentence], att: Attributes) extends Module

  case class ConcreteImport(name: String, att: Attributes) extends Import

  case class ConcreteSortDeclaration(sort: String, att: Attributes) extends SortDeclaration

  case class ConcreteSymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends SymbolDeclaration

  case class ConcreteRule(p: Pattern, att: Attributes) extends Rule

  case class ConcreteAxiom(p: Pattern, att: Attributes) extends Axiom

  case class ConcreteVariable(name: String, sort: String) extends Variable {
    override val content: (String, String) = (name, sort)
  }

  case class ConcreteApplication(label: String, args: Attributes) extends Application {
    override val children: Seq[AST] = args
  }

  case class ConcreteDomainValue(label: String, value: String) extends DomainValue {
    override val content = (label, value)
  }

  case class ConcreteTrue() extends True {
    override val content: Boolean = true
  }

  case class ConcreteFalse() extends False {
    override val content: Boolean = false
  }

  case class ConcreteAnd(p: Pattern, q: Pattern) extends And {
    override val label: String = "\\and"
    override val children: Seq[AST] = Seq(p, q)
  }

  case class ConcreteOr(p: Pattern, q: Pattern) extends Or {
    override val label: String = "\\or"
    override val children: Seq[AST] = Seq(p, q)
  }

  case class ConcreteNot(p: Pattern) extends Not {
    override val label: String = "\\not"
    override val children: Seq[AST] = Seq(p)
  }

  case class ConcreteExists(v: Variable, p: Pattern) extends Exists {
    override val label: String = "\\exists"
    override val children: Seq[AST] = Seq(v, p)
  }

  case class ConcreteForAll(v: Variable, p: Pattern) extends ForAll {
    override val label: String = "\\forAll"
    override val children: Seq[AST] = Seq(v, p)
  }

  case class ConcreteNext(p: Pattern) extends Next {
    override val label: String = "\\next"
    override val children: Seq[AST] = Seq(p)
  }

  case class ConcreteRewrite(p: Pattern, q: Pattern) extends Rewrite {
    override val label: String = "\\rewrite"
    override val children: Seq[AST] = Seq(p, q)
  }

  case class ConcreteEquals(p: Pattern, q: Pattern) extends Equals {
    override val label: String = "\\equals"
    override val children: Seq[AST] = Seq(p, q)
  }

  case class ConcreteImplies(p: Pattern, q: Pattern) extends Implies {
    override val label: String = "\\implies"
    override val children: Seq[AST] = Seq(p, q)
  }

}
