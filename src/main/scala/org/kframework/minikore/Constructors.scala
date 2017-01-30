package org.kframework.minikore

import org.kframework.minikore.NewKore._


abstract class Constructors {

  def variable(name: String, sort: String): Variable

  def application(label: String, args: Seq[Pattern]): Application

  def domainValue(label: String, sort: String): DomainValue

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

}

object KoreConstructor extends Constructors {
  override def variable(name: String, sort: String): Variable = DefaultImplementation.ConcreteVariable(name, sort)

  override def application(label: String, args: Seq[Pattern]): Application = DefaultImplementation.ConcreteApplication(label, args)

  override def domainValue(label: String, sort: String): DomainValue = DefaultImplementation.ConcreteDomainValue(label, sort)

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
}
