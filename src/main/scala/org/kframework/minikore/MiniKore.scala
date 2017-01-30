package org.kframework.minikore

import org.kframework.minikore.MiniKore._


object MiniKore{

  type Attributes = Seq[Pattern]

  abstract class Definition {
    val modules: Seq[Module]
    val att: Attributes
  }

  object Definition {
    def unapply(arg: Definition): Option[(Seq[Module], Attributes)] = Some((arg.modules, arg.att))
  }

  abstract class Module {
    val name: String
    val sentences: Seq[Sentence]
    val att: Attributes
  }

  object Module {
    def unapply(arg: Module): Option[(String, Seq[Sentence], Attributes)] = Some((arg.name, arg.sentences, arg.att))
  }

  trait Sentence

  abstract class Import extends Sentence {
    val name: String
    val att: Attributes
  }

  object Import {
    def unapply(arg: Import): Option[(String, Attributes)] = Some((arg.name, arg.att))
  }

  abstract class SortDeclaration extends Sentence {
    val sort: String
    val att: Attributes
  }

  object SortDeclaration {
    def unapply(arg: SortDeclaration): Option[(String, Attributes)] = Some((arg.sort, arg.att))
  }

  abstract class SymbolDeclaration extends Sentence {
    val sort: String
    val label: String
    val args: Seq[String]
    val att: Attributes
  }

  object SymbolDeclaration {
    def unapply(arg: SymbolDeclaration): Option[(String, String, Seq[String], Attributes)] = Some((arg.sort, arg.label, arg.args, arg.att))
  }

  abstract class Rule extends Sentence {
    val p: Pattern
    val att: Attributes
  }

  object Rule {
    def unapply(arg: Rule): Option[(Pattern, Attributes)] = Some((arg.p, arg.att))
  }


  abstract class Axiom extends Sentence {
    val p: Pattern
    val att: Attributes
  }

  object Axiom {
    def unapply(arg: Axiom): Option[(Pattern, Attributes)] = Some((arg.p, arg.att))
  }


  // Pattern trait + abstract classes
  trait Pattern

  abstract class Variable extends Pattern {
    val name: String
    val sort: String
  }

  object Variable {
    def unapply(arg: Variable): Option[(String, String)] = Some((arg.name, arg.sort))
  }

  abstract class Application extends Pattern {
    val label: String
    val args: Seq[Pattern]
  }

  object Application extends Pattern {
    def unapply(arg: Application): Option[(String, Seq[Pattern])] = Some((arg.label, arg.args))
  }

  abstract class DomainValue extends Pattern {
    val label: String
    val value: String
  }

  object DomainValue extends Pattern {
    def unapply(arg: DomainValue): Option[(String, String)] = Some((arg.label, arg.value))
  }

  //
  abstract class True extends Pattern

  object True {
    def unapply(arg: True): Boolean = true
  }

  abstract class False extends Pattern

  object False {
    def unapply(arg: False): Boolean = true
  }


  //
  abstract class And extends Pattern {
    val p: Pattern
    val q: Pattern
  }

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  abstract class Or extends Pattern {
    val p: Pattern
    val q: Pattern
  }

  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  abstract class Not extends Pattern {
    val p: Pattern
  }

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }

  abstract class Implies extends Pattern {
    val p: Pattern
    val q: Pattern
  }

  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  abstract class Exists extends Pattern {
    val v: Variable
    val p: Pattern
  }

  object Exists {
    def unapply(arg: Exists): Option[(Pattern, Pattern)] = Some((arg.v, arg.p))
  }

  abstract class ForAll extends Pattern {
    val v: Variable
    val p: Pattern
  }

  object ForAll {
    def unapply(arg: ForAll): Option[(Pattern, Pattern)] = Some((arg.v, arg.p))
  }

  //
  abstract class Next extends Pattern {
    val p: Pattern
  }

  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg.p)
  }

  abstract class Rewrite extends Pattern {
    val p: Pattern
    val q: Pattern
  }

  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

  abstract class Equals extends Pattern {
    val p: Pattern
    val q: Pattern
  }

  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some((arg.p, arg.q))
  }

}

object DefaultImplementation {

  case class ConcreteDefinition(modules: Seq[Module], att: Attributes) extends Definition

  case class ConcreteModule(name: String, sentences: Seq[Sentence], att: Attributes) extends Module

  case class ConcreteImport(name: String, att: Attributes) extends Import

  case class ConcreteSortDeclaration(sort: String, att: Attributes) extends SortDeclaration

  case class ConcreteSymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends SymbolDeclaration

  case class ConcreteRule(p: Pattern, att: Attributes) extends Rule

  case class ConcreteAxiom(p: Pattern, att: Attributes) extends Axiom

  case class ConcreteVariable(name: String, sort: String) extends Variable

  case class ConcreteApplication(label: String, args: Attributes) extends Application

  case class ConcreteDomainValue(label: String, value: String) extends DomainValue

  case class ConcreteTrue() extends True

  case class ConcreteFalse() extends False

  case class ConcreteAnd(p: Pattern, q: Pattern) extends And

  case class ConcreteOr(p: Pattern, q: Pattern) extends Or

  case class ConcreteNot(p: Pattern) extends Not

  case class ConcreteExists(v: Variable, p: Pattern) extends Exists

  case class ConcreteForAll(v: Variable, p: Pattern) extends ForAll

  case class ConcreteNext(p: Pattern) extends Next

  case class ConcreteRewrite(p: Pattern, q: Pattern) extends Rewrite

  case class ConcreteEquals(p: Pattern, q: Pattern) extends Equals

  case class ConcreteImplies(p: Pattern, q: Pattern) extends Implies

}
