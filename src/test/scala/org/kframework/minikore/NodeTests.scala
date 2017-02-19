package org.kframework.minikore

import org.junit.Test
import org.kframework.minikore.PatternInterface._
import org.kframework.minikore.TreeInterface._



class NodeTest {

  object TestFunctions {

    def size(p: Pattern): Int = {
      p.asInstanceOf[AST[Pattern]] match {
        case Node(c: Seq[Pattern]) => c.map(x => size(x)).sum
        case Leaf(_) => 1
      }
    }

    def getLabelledNodesCount(p: Pattern): Int =  {
      p.asInstanceOf[AST[Pattern]] match {
        case LabelledNode(_, c: Seq[Pattern]) => c.map(x => getLabelledNodesCount(x)).sum + 1
        case Node(c: Seq[Pattern]) => c map getLabelledNodesCount sum
        case _ => 0
      }
    }


  }

  object TestPatterns {
    val b: Builders = DefaultBuilders.build

    val int1: Pattern = b.DomainValue("1", "Int")

    val int2: Pattern = b.DomainValue("2", "Int")

    val stringFoo: Pattern = b.DomainValue("Foo", "String")

    val intVar = b.Variable("A", "Int")

    val e1: Pattern = b.And(intVar, int1)

    val e2: Pattern = b.And(b.Variable("C", "String"), stringFoo)

    val plusApp: Pattern = b.Application("Plus", Seq(int1, int2))

  }

  def b: Builders = DefaultBuilders.build

  def t = TestPatterns

  @Test def sizeTest1(): Unit = {
    assert(TestFunctions.size(TestPatterns.e1) == 2)
  }

  @Test def sizeTest2(): Unit = {
    assert(TestFunctions.size(b.Equals(t.plusApp, t.int1)) == 3)
  }
  @Test def labelledNodeCountTest(): Unit = {
    assert(TestFunctions.getLabelledNodesCount(t.b.Equals(t.intVar, t.plusApp)) == 1)
  }


}
