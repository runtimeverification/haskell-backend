package org.kframework.minikore

object MiniKoreInterface {

  // abstract interface

  sealed trait Ast

  // for Variable and DomainValue
  sealed trait Leaf extends Ast {
    def data: (String, String)
    def build: (String, String) => Leaf
  }

  // for Application and Matching logic connectives
  sealed trait Node[T <: Ast] extends Ast {
    def data: String
    def children: Seq[T]
    def build: (String, Seq[T]) => T
  }

  // ground interface

  trait Pattern extends Ast

  trait Variable extends Pattern with Leaf {
    def name: String
    def sort: String
    def constructor: (String, String) => Variable
    //
    def data: (String, String) = (name, sort)
    def build: (String, String) => Variable = constructor
  }

  trait Application extends Pattern with Node[Pattern] {
    def label: String
    def args: Seq[Pattern]
    def constructor: (String, Seq[Pattern]) => Application
    //
    def data: String = label
    def children: Seq[Pattern] = args
    def build: (String, Seq[Ast]) => Application = (d,c) => {
      assert(d == data)
      constructor(d, c.asInstanceOf[Seq[Pattern]])
    }
  }

  trait DomainValue extends Pattern with Leaf {
    def label: String
    def value: String
    def constructor: (String, String) => DomainValue
    //
    def data: (String, String) = (label, value)
    def build: (String, String) => DomainValue = constructor
  }

  trait True    extends Pattern with Node[Pattern] with ML0[True]    { def data: String = "\\True"    }
  trait False   extends Pattern with Node[Pattern] with ML0[False]   { def data: String = "\\False"   }
  trait And     extends Pattern with Node[Pattern] with ML2[And]     { def data: String = "\\And"     }
  trait Or      extends Pattern with Node[Pattern] with ML2[Or]      { def data: String = "\\Or"      }
  trait Not     extends Pattern with Node[Pattern] with ML1[Not]     { def data: String = "\\Not"     }
  trait Implies extends Pattern with Node[Pattern] with ML2[Implies] { def data: String = "\\Implies" }
  trait Exists  extends Pattern with Node[Pattern] with MLV[Exists]  { def data: String = "\\Exists"  }
  trait ForAll  extends Pattern with Node[Pattern] with MLV[ForAll]  { def data: String = "\\ForAll"  }
  trait Next    extends Pattern with Node[Pattern] with ML1[Next]    { def data: String = "\\Next"    }
  trait Rewrite extends Pattern with Node[Pattern] with ML2[Rewrite] { def data: String = "\\Rewrite" }
  trait Equal   extends Pattern with Node[Pattern] with ML2[Equal]   { def data: String = "\\Equal"   }

  // macros for Matching logic connectives

  sealed trait ML0[T <: Pattern] {
    def constructor: () => T
    //
    def data: String
    def children: Seq[Pattern] = Seq()
    def build: (String, Seq[Ast]) => T = (d,c) => {
      assert(d == data)
      assert(c.size == 0)
      constructor()
    }
  }

  sealed trait ML1[T <: Pattern] {
    def p: Pattern
    def constructor: (Pattern) => T
    //
    def data: String
    def children: Seq[Pattern] = Seq(p)
    def build: (String, Seq[Ast]) => T = (d,c) => {
      assert(d == data)
      assert(c.size == 1)
      constructor(c(0).asInstanceOf[Pattern])
    }
  }

  sealed trait ML2[T <: Pattern] {
    def p: Pattern
    def q: Pattern
    def constructor: (Pattern, Pattern) => T
    //
    def data: String
    def children: Seq[Pattern] = Seq(p,q)
    def build: (String, Seq[Ast]) => T = (d,c) => {
      assert(d == data)
      assert(c.size == 2)
      constructor(c(0).asInstanceOf[Pattern], c(1).asInstanceOf[Pattern])
    }
  }

  sealed trait MLV[T <: Pattern] {
    def v: Variable
    def p: Pattern
    def constructor: (Variable, Pattern) => T
    //
    def data: String
    def children: Seq[Pattern] = Seq(v,p)
    def build: (String, Seq[Ast]) => T = (d,c) => {
      assert(d == data)
      assert(c.size == 2)
      constructor(c(0).asInstanceOf[Variable], c(1).asInstanceOf[Pattern])
    }
  }

  // factory of constructors

  trait Constructor {
    def Variable    : (String, String) => Variable
    def Application : (String, Seq[Pattern]) => Application
    def DomainValue : (String, String) => DomainValue
    def True        : () => True
    def False       : () => False
    def And         : (Pattern, Pattern) => And
    def Or          : (Pattern, Pattern) => Or
    def Not         : (Pattern) => Not
    def Implies     : (Pattern, Pattern) => Implies
    def Exists      : (Variable, Pattern) => Exists
    def ForAll      : (Variable, Pattern) => ForAll
    def Next        : (Pattern) => Next
    def Rewrite     : (Pattern, Pattern) => Rewrite
    def Equal       : (Pattern, Pattern) => Equal
  }

}
