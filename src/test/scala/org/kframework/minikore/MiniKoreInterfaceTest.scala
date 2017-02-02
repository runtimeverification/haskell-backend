package org.kframework.minikore

import org.junit.Test

/**
  * Created by daejunpark on 2/1/17.
  */
class MiniKoreInterfaceTest {


  // Interface 1: generic AST nodes
  // Useful for generic traversals
  sealed trait Ast
  trait Leaf extends Ast {
    def i:Int
  }
  object Leaf {  // so you can match with Leaf(_) on Ast objects
  def unapply(l: Leaf): Option[Int] = Some(l.i)
  }
  trait Node extends Ast {
    def e1:Ast
    def e2:Ast
  }
  object Node {
    def unapply(n: Node): Option[(Ast, Ast)] = Some((n.e1, n.e2))
  }

  // Interface 2: expressions with their specific constructs
  // Useful for specific traversals
  // Note how concrete constructs extend their corresponding generic construct, too
  sealed trait Exp extends Ast
  trait Val extends Exp with Leaf {
    def i:Int
  }
  object Val {
    def unapply(v: Val): Option[Int] = Some(v.i)
  }
  trait Plus extends Exp with Node {
    def e1:Exp
    def e2:Exp
  }
  object Plus {
    def unapply(p: Plus): Option[(Exp, Exp)] = Some((p.e1, p.e2))
  }
  trait Mult extends Exp with Node {
    def e1:Exp
    def e2:Exp
  }
  object Mult {
    def unapply(m: Mult): Option[(Exp, Exp)] = Some((m.e1, m.e2))
  }

  // Implementation of Ast
  case class LeafC(i:Int) extends Leaf
  case class NodeC(e1:Ast, e2:Ast) extends Node

  // Implementation 1 of Exp
  case class Val1(i:Int) extends Val
  case class Plus1(e1:Exp, e2:Exp) extends Plus
  case class Mult1(e1:Exp, e2:Exp) extends Mult

  // Implementation 2 of Exp
  case class Val2(i:Int) extends Val
  case class Plus2(e1:Exp, e2:Exp) extends Plus
  case class Mult2(e1:Exp, e2:Exp) extends Mult


    // Generic size: can also be called on Exp objects, at no translation cost
    def size(t:Ast): Int = t match {
      case _:Leaf => 1
      //case Node(e1,e2) => size(e1) + size(e2)
      //case t:Plus => size(t.e1) + size(t.e2)
      case t:Node => size(t.e1) + size(t.e2)
    }

    // Specific eval
    def eval(e:Exp): Int = e match {
      case e:Val => e.i
      case e:Plus => eval(e.e1) + eval(e.e2)
      case Mult(e1,e2) => eval(e1) * eval(e2)
    }

    // Translator from any implementation of Exp to one implementation of Ast
    def ExpToAstC(e:Exp):Ast = e match {
      case Val(i) => LeafC(i)
      case Plus(e1,e2) => NodeC(ExpToAstC(e1),ExpToAstC(e2))
      case Mult(e1,e2) => NodeC(ExpToAstC(e1),ExpToAstC(e2))
    }

    // Translator from any implementation of Exp to one implementation of Exp (second)
    def ExpToExp2(e:Exp):Exp = e match {
      case Val(i) => Val2(i)
      case Plus(e1,e2) => Plus2(ExpToExp2(e1),ExpToExp2(e2))
      case Mult(e1,e2) => Mult2(ExpToExp2(e1),ExpToExp2(e2))
    }

    // Translator from any implementation of Ast to one implementation of Exp (second)
    def AstToExp2(t:Ast):Exp = t match {
      case Leaf(i) => Val2(i)
      case Node(t1,t2) => Plus2(AstToExp2(t1),AstToExp2(t2))
    }

    def test(): Unit = {
      val e1 = Plus1(Val1(1),Mult1(Val1(2),Val1(3)))                // Implementation 1
      val e2 = Plus2(Mult2(Val2(1),Mult2(Val2(2),Val2(3))),Val2(4)) // Implementation 2
      val e3 = Plus2(Mult2(Val1(1),Mult1(Val1(2),Val1(3))),Val2(4)) // Mixed
      println(e1)
      println(e2)
      println(e3)
      println(size(e1))  // no translation from Exp to Ast needed
      println(size(e2))  // no translation from Exp to Ast needed
      println(size(e3))  // no translation from Exp to Ast needed
      println(eval(e1))
      println(eval(e2))
      println(eval(e3))
      println(ExpToAstC(e1))
      println(ExpToAstC(e2))
      println(ExpToAstC(e3))
      println(ExpToExp2(e1))
      println(ExpToExp2(e2))
      println(ExpToExp2(e3))
      println(AstToExp2(e1))  // no translation from Exp to Ast needed
      println(AstToExp2(e2))  // no translation from Exp to Ast needed
      println(AstToExp2(e3))  // no translation from Exp to Ast needed
    }

}
