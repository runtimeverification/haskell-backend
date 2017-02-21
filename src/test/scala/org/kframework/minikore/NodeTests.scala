package org.kframework.minikore

import org.junit.Test
import org.kframework.minikore.PatternInterface._
import org.kframework.minikore.TreeInterface._


class NodeTest {

  object TestFunctions {

    def size(p: Pattern): Int = {
      p match {
        case Node(c: Seq[Pattern]) => c.map(size).sum
        case Leaf(_) => 1
      }
    }

    def getLabelledNodesCount(p: Pattern): Int = {
      p match {
        case LabelledNode(_, c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum + 1
        case Node(c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum
        case _ => 0
      }
    }

    def map(f: (Pattern) => Pattern)(p: Pattern): Pattern = {
      p match {
        case n: Node[Pattern] => n.build(n.children.map(f))
        case l: Leaf[Pattern, _] => f(l)
      }
    }
  }

  object TestPatterns {
    val b: Builders = DefaultBuilders.build

    val int1: Pattern = b.DomainValue("1", "Int")

    val int2: Pattern = b.DomainValue("2", "Int")

    val int4: Pattern = b.DomainValue("4", "Int")

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

  @Test def identityFunctionTest(): Unit = {
    val pList: Seq[Pattern] = Seq(t.plusApp, t.e1, t.e2, t.b.And(t.e1, t.e2))

    def identityF: (Pattern) => Pattern = (x) => x

    assert(pList.map(TestFunctions.map(identityF)).equals(pList))
  }

  @Test def mapTest1(): Unit = {
    val e1: Pattern = t.b.Application("IntContainer", Seq(t.int1, t.int2))
    val intSort: String = "Int"

    def doubleInt: (Pattern) => Pattern = { (p) =>
      p match {
        case DomainValue(intString: String, `intSort`) => t.b.DomainValue((intString.toInt * 2) toString, intSort)
        case other => other
      }
    }

    val e2: Pattern = t.b.Application("IntContainer", Seq(t.int2, t.int4))

    assert(TestFunctions.map(doubleInt)(e1) == e2)

  }

}
