package org.kframework.minikore

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders

case class MiniKoreOuterUtils(b: Builders) {

  import b._

  // TODO: These should be abstracted
  import org.kframework.minikore.implementation.MiniKore.{Definition, Module, Sentence, Import, SortDeclaration, SymbolDeclaration, Attributes, Rule, Axiom}

  // Attributes
  // ==========

  // Apply Transformation to Attributes (Should be moved into MiniKore data-structures)
  // So each outer data-structure would implement "HasAttributes" or something, which would have
  // function `onAttributes` among others
  def onAttributesSent(f: Pattern => Pattern): Sentence => Sentence = {
    case Import(name, att)                         => Import(name, att map f)
    case SortDeclaration(sort, att)                => SortDeclaration(sort, att map f)
    case SymbolDeclaration(sort, label, args, att) => SymbolDeclaration(sort, label, args, att map f)
    case Rule(pattern, att)                        => Rule(pattern, att map f)
    case Axiom(pattern, att)                       => Axiom(pattern, att map f)
  }
  
  def onAttributesMod(f: Pattern => Pattern): Module => Module = {
    case Module(name, sentences, att) => Module(name, sentences map onAttributesSent(f), att map f)
  }
  
  def onAttributesDef(f: Pattern => Pattern): Definition => Definition = {
    case Definition(modules, att) => Definition(modules map onAttributesMod(f), att map f)
  }

  def getAttributeKey(key: Symbol, atts: Attributes): Seq[Seq[Pattern]] = atts collect { case Application(`key`, args) => args }

  def updateAttribute(key: Symbol, value: Pattern*): Attributes => Attributes = _ map {
    case Application(`key`, _) => Application(key, value)
    case pattern               => pattern
  }

  // Definitions
  // ===========

  def allSentences(d: Definition): Seq[Sentence] = d.modules flatMap (_.sentences)

  def allSorts(d: Definition): Set[Sort] = allSentences(d) collect {
    case SortDeclaration(sort, _)         => sort
    case SymbolDeclaration(sort, _, _, _) => sort
  } toSet
}


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

  def consListLeft(cons: Symbol, nil: Symbol)(ps: Seq[Pattern]): Pattern = ps.foldRight(Application(nil, Seq.empty))((acc, next) => Application(cons, Seq(acc, next)))
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
}
