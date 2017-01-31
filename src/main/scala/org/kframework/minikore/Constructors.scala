package org.kframework.minikore

import org.kframework.minikore.MiniKore._


// Constructor Factory.
abstract class Constructors {

  def variable(name: String, sort: String): Variable

  def application(label: String, args: Seq[Pattern]): Application

  def domainValue(label: String, value: String): DomainValue

  def mlTrue(): True

  def mlFalse(): False

  def and(p: Pattern, q: Pattern): And

  def or(p: Pattern, q: Pattern): Or

  def not(p: Pattern): Not

  def exists(v: Variable, p: Pattern): Exists

  def forAll(v: Variable, p: Pattern): ForAll

  def implies(p: Pattern, q: Pattern): Implies

  def next(p: Pattern): Next

  def rewrite(p: Pattern, q: Pattern): Rewrite

  def equals(p: Pattern, q: Pattern): Equals

  def definition(modules: Seq[Module], att: Attributes): Definition

  def defImport(name: String, att: Attributes): Import

  def module(name: String, args: Seq[Sentence], att: Attributes): Module

  def sortDeclaration(sort: String, att: Attributes): SortDeclaration

  def symbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes): SymbolDeclaration

  def rule(p: Pattern, att: Attributes): Rule

  def axiom(p: Pattern, att: Attributes): Axiom

}

// Provided Constructors over default objects.

object KoreConstructor extends Constructors {
  override def variable(name: String, sort: String): Variable = DefaultImplementation.ConcreteVariable(name, sort)

  override def application(label: String, args: Seq[Pattern]): Application = DefaultImplementation.ConcreteApplication(label, args)

  override def domainValue(label: String, value: String): DomainValue = DefaultImplementation.ConcreteDomainValue(label, value)

  override def mlTrue(): True = DefaultImplementation.ConcreteTrue()

  override def mlFalse(): False = DefaultImplementation.ConcreteFalse()

  override def and(p: Pattern, q: Pattern): And = DefaultImplementation.ConcreteAnd(p, q)

  override def or(p: Pattern, q: Pattern): Or = DefaultImplementation.ConcreteOr(p, q)

  override def not(p: Pattern): Not = DefaultImplementation.ConcreteNot(p)

  override def exists(v: Variable, p: Pattern): Exists = DefaultImplementation.ConcreteExists(v, p)

  override def forAll(v: Variable, p: Pattern): ForAll = DefaultImplementation.ConcreteForAll(v, p)

  override def implies(p: Pattern, q: Pattern): Implies = DefaultImplementation.ConcreteImplies(p, q)

  override def next(p: Pattern): Next = DefaultImplementation.ConcreteNext(p)

  override def rewrite(p: Pattern, q: Pattern): Rewrite = DefaultImplementation.ConcreteRewrite(p, q)

  override def equals(p: Pattern, q: Pattern): Equals = DefaultImplementation.ConcreteEquals(p, q)

  override def definition(modules: Seq[Module], att: Attributes): Definition = DefaultImplementation.ConcreteDefinition(modules, att)

  override def defImport(name: String, att: Attributes): Import = DefaultImplementation.ConcreteImport(name, att)

  override def module(name: String, args: Seq[Sentence], att: Attributes): Module = DefaultImplementation.ConcreteModule(name, args, att)

  override def sortDeclaration(sort: String, att: Attributes): SortDeclaration = DefaultImplementation.ConcreteSortDeclaration(sort, att)

  override def symbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes): SymbolDeclaration = DefaultImplementation.ConcreteSymbolDeclaration(sort, label, args, att)

  override def rule(p: Pattern, att: Attributes): Rule = DefaultImplementation.ConcreteRule(p, att)

  override def axiom(p: Pattern, att: Attributes): Axiom = DefaultImplementation.ConcreteAxiom(p, att)
}
