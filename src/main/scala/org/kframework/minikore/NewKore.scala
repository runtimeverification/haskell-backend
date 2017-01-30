package org.kframework.minikore

import org.kframework.minikore.NewKore._


object NewKore {

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

  case class SortDeclaration(sort: String, att: Attributes) extends Sentence

  case class SymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends Sentence

  case class Rule(pattern: Pattern, att: Attributes) extends Sentence

  case class Axiom(pattern: Pattern, att: Attributes) extends Sentence


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
    val sort: String
  }

  object DomainValue extends Pattern {
    def unapply(arg: DomainValue): Option[(String, String)] = Some((arg.label, arg.sort))
  }

  //
  abstract class True extends Pattern

  object True {
    def unapply(arg: True): Option[()] = Some()
  }

  abstract class False extends Pattern

  object False {
    def unapply(arg: True): Option[()] = Some()
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

  case class ConcreteVariable(name: String, sort: String) extends Variable

  case class ConcreteApplication(label: String, args: Attributes) extends Application

  case class ConcreteDomainValue(label: String, sort: String) extends DomainValue

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
