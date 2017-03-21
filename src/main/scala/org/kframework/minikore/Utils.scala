package org.kframework.minikore

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders


case class MiniKorePatternUtils(b: Builders) {
    
  import b._

  // Map
  // ===

  def onChildren(f: Pattern => Pattern): Pattern => Pattern = {
    case Application(label, args) => Application(label, args map f)
    case And(p, q)                => And(f(p), f(q))
    case Or(p, q)                 => Or(f(p), f(q))
    case Not(p)                   => Not(f(p))
    case Implies(p, q)            => Implies(f(p), f(q))
    case Exists(v, p)             => Exists(v, f(p))
    case ForAll(v, p)             => ForAll(v, f(p))
    case Next(p)                  => Next(f(p))
    case Rewrite(p, q)            => Rewrite(f(p), f(q))
    case Equals(p, q)             => Equals(f(p), f(q))
    case p                        => p
  }

  // Traversals
  // ==========

  // `traverseTopDown` will first apply `f` to the root, then apply it to the sub-terms.
  // This will perform better than `traverseBottomUp` when `f: Pattern => Pattern` may eliminate sub-terms.
  def traverseTopDown(f: Pattern => Pattern): Pattern => Pattern = pattern => onChildren(traverseTopDown(f))(f(pattern))

  // `traverseBottomUp` will first apply `f` to the sub-terms, then to the root.
  def traverseBottomUp(f: Pattern => Pattern): Pattern => Pattern = pattern => f(onChildren(traverseBottomUp(f))(pattern))

  // Cons Lists
  // ==========
  // Create cons-lists given the klabel for the `cons` operator and the `nil` operator.
  // consListLeft( Symbol("apply"), Symbol("4"))(Seq(Symbol("1"),Symbol("2"),Symbol("3"))) => apply(1,apply(2,apply(3,4)))
  // consListRight(Symbol("apply"), Symbol("0"))(Seq(Symbol("1"),Symbol("2"),Symbol("3"))) => apply(apply(apply(0,1),2),3)

  def consListLeft(cons: Symbol, nil: Symbol)(ps: Seq[Pattern]): Application = ps.foldRight(Application(nil, Seq.empty))((acc, next) => Application(cons, Seq(acc, next)))
  def consListLeftSubsort(cons: Symbol, nil: Symbol)(ps: Seq[Pattern]): Pattern = ps.size match {
    case 0 => Application(nil, Seq.empty)
    case 1 => ps.head
    case _ => Application(cons, Seq(ps.head, consListLeftSubsort(cons, nil)(ps.tail)))
  }
  //def consListRight(cons: Symbol, nil: Symbol)(ps: Seq[Pattern]): Pattern = ps.foldLeft(Application(nil, Seq.empty))((acc, next) => Application(cons, Seq(acc, next)))

  // Flatten parse-trees
  // ===================
  // flattenBySymbols(apply(apply(apply(0,1),2),3)) => Seq(Symbol("0"),Symbol("1"),Symbol("2"),Symbol("3"))
  // flattenBySymbols(apply(1,apply(2,apply(3,4)))) => Seq(Symbol("1"),Symbol("2"),Symbol("3"),Symbol("4"))

  def flattenBySymbols(labels: Symbol*): Pattern => Seq[Pattern] = {
    case Application(label, args) if labels contains label => args flatMap flattenBySymbols(labels:_*)
    case parsed                                            => Seq(parsed)
  }
  
  def rebuildWith(b: Builders): Pattern => Pattern = {
    case Application(label, args)   => b.Application(label, args)
    case And(p, q)                  => b.And(p, q)
    case Or(p, q)                   => b.Or(p, q)
    case Not(p)                     => b.Not(p)
    case Implies(p, q)              => b.Implies(p, q)
    case Exists(v, p)               => b.Exists(v, p)
    case ForAll(v, p)               => b.ForAll(v, p)
    case Next(p)                    => b.Next(p)
    case Rewrite(p, q)              => b.Rewrite(p, q)
    case Equals(p, q)               => b.Equals(p, q)
    case Variable(name, sort)       => b.Variable(name, sort)
    case DomainValue(symbol, value) => b.DomainValue(symbol, value)
  }

  def rebuildAllWith(b: Builders): Pattern => Pattern = traverseBottomUp(rebuildWith(b))
}
