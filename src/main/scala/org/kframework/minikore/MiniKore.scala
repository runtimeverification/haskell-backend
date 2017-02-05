package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore extends i.Constructor {

  type Attributes = Seq[Pattern]

  case class Definition(modules: Seq[Module], att: Attributes)
  case class Module(name: String, sentences: Seq[Sentence], att: Attributes)

  sealed trait Sentence
  case class Import(name: String, att: Attributes) extends Sentence
  case class SortDeclaration(sort: String, att: Attributes) extends Sentence
  case class SymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends Sentence
  case class Rule(pattern: Pattern, att: Attributes) extends Sentence
  case class Axiom(pattern: Pattern, att: Attributes) extends Sentence

  sealed trait Pattern extends i.Pattern
  case class Variable   (name:  String, sort: String      ) extends Pattern with i.Variable    { override def constructor: (String, String)         => i.Variable    = Variable.apply }
  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application { override def constructor: (String, Seq[i.Pattern]) => i.Application = Application.apply }
  case class DomainValue(label: String, value: String     ) extends Pattern with i.DomainValue { override def constructor: (String, String)         => i.DomainValue = DomainValue.apply }
  //
  case class True () extends Pattern with i.True  { override def constructor: () => i.True  = True.apply }
  case class False() extends Pattern with i.False { override def constructor: () => i.False = False.apply }
  //
  case class And    (p: Pattern , q: Pattern) extends Pattern with i.And     { override def constructor: (i.Pattern , i.Pattern) => i.And     = And.apply }
  case class Or     (p: Pattern , q: Pattern) extends Pattern with i.Or      { override def constructor: (i.Pattern , i.Pattern) => i.Or      = Or.apply }
  case class Not    (p: Pattern             ) extends Pattern with i.Not     { override def constructor: (i.Pattern            ) => i.Not     = Not.apply }
  case class Implies(p: Pattern , q: Pattern) extends Pattern with i.Implies { override def constructor: (i.Pattern , i.Pattern) => i.Implies = Implies.apply }
  case class Exists (v: Variable, p: Pattern) extends Pattern with i.Exists  { override def constructor: (i.Variable, i.Pattern) => i.Exists  = Exists.apply }
  case class ForAll (v: Variable, p: Pattern) extends Pattern with i.ForAll  { override def constructor: (i.Variable, i.Pattern) => i.ForAll  = ForAll.apply }
  case class Next   (p: Pattern             ) extends Pattern with i.Next    { override def constructor: (i.Pattern            ) => i.Next    = Next.apply }
  case class Rewrite(p: Pattern , q: Pattern) extends Pattern with i.Rewrite { override def constructor: (i.Pattern , i.Pattern) => i.Rewrite = Rewrite.apply }
  case class Equal  (p: Pattern , q: Pattern) extends Pattern with i.Equal   { override def constructor: (i.Pattern , i.Pattern) => i.Equal   = Equal.apply }

  // implementation of i.Constructor

  object Variable    extends ((String, String)         => i.Variable   ) { /* def apply(name: String, sort: String): i.Variable = Variable(name, sort) */ }
  object Application extends ((String, Seq[i.Pattern]) => i.Application) { def apply(label: String, args: Seq[i.Pattern]): i.Application = Application(label, args.asInstanceOf[Seq[Pattern]]) }
  object DomainValue extends ((String, String)         => i.DomainValue) { /* def apply(label: String, value: String): i.DomainValue = DomainValue(label, value) */ }
  object True        extends ((                     )  => i.True       ) { /* def apply(): i.True = True() */ }
  object False       extends ((                     )  => i.False      ) { /* def apply(): i.False = False() */ }
  object And         extends ((i.Pattern , i.Pattern)  => i.And        ) { def apply(p: i.Pattern , q: i.Pattern): i.And     = And    (p.asInstanceOf[Pattern] , q.asInstanceOf[Pattern]) }
  object Or          extends ((i.Pattern , i.Pattern)  => i.Or         ) { def apply(p: i.Pattern , q: i.Pattern): i.Or      = Or     (p.asInstanceOf[Pattern] , q.asInstanceOf[Pattern]) }
  object Not         extends ((i.Pattern            )  => i.Not        ) { def apply(p: i.Pattern               ): i.Not     = Not    (p.asInstanceOf[Pattern]                          ) }
  object Implies     extends ((i.Pattern , i.Pattern)  => i.Implies    ) { def apply(p: i.Pattern , q: i.Pattern): i.Implies = Implies(p.asInstanceOf[Pattern] , q.asInstanceOf[Pattern]) }
  object Exists      extends ((i.Variable, i.Pattern)  => i.Exists     ) { def apply(v: i.Variable, p: i.Pattern): i.Exists  = Exists (v.asInstanceOf[Variable], p.asInstanceOf[Pattern]) }
  object ForAll      extends ((i.Variable, i.Pattern)  => i.ForAll     ) { def apply(v: i.Variable, p: i.Pattern): i.ForAll  = ForAll (v.asInstanceOf[Variable], p.asInstanceOf[Pattern]) }
  object Next        extends ((i.Pattern            )  => i.Next       ) { def apply(p: i.Pattern               ): i.Next    = Next   (p.asInstanceOf[Pattern]                          ) }
  object Rewrite     extends ((i.Pattern , i.Pattern)  => i.Rewrite    ) { def apply(p: i.Pattern , q: i.Pattern): i.Rewrite = Rewrite(p.asInstanceOf[Pattern] , q.asInstanceOf[Pattern]) }
  object Equal       extends ((i.Pattern , i.Pattern)  => i.Equal      ) { def apply(p: i.Pattern , q: i.Pattern): i.Equal   = Equal  (p.asInstanceOf[Pattern] , q.asInstanceOf[Pattern]) }
}
