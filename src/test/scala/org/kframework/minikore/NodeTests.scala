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
        case LabeledNode(_, c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum + 1
        case Node(c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum
        case _ => 0
      }
    }

    def map(f: (Pattern) => Pattern)(p: Pattern): Pattern = {
      p match {
        case n: Node => {
          val c: Seq[Pattern] = n.children.map(map(f))
          n.build(c)
        }
        case l: Leaf[_] => f(l)
      }
    }
  }

  object TestPatterns {
    val b: Build.Builders = DefaultBuilders

    val int1: Pattern = b.DomainValue("1", "Int")

    val int2: Pattern = b.DomainValue("2", "Int")

    val int4: Pattern = b.DomainValue("4", "Int")

    val stringFoo: Pattern = b.DomainValue("Foo", "String")

    val intVar = b.Variable("A", "Int")

    val e1: Pattern = b.And(intVar, int1)

    val e2: Pattern = b.And(b.Variable("C", "String"), stringFoo)

    val plusApp: Pattern = b.Application("Plus", Seq(int1, int2))

    val simpleVariable: Variable = b.Variable("X", "Test")

    val simpleDomainValue: DomainValue = b.DomainValue("test", "String")

    val top: Top = b.Top()

    val bottom: Bottom = b.Bottom()

    val simpleAnd: And = b.And(top, bottom)

    val simpleOr: Or = b.Or(top, bottom)

    val simpleNot: Not = b.Not(top)

    val simpleImplies: Implies = b.Implies(bottom, top)

    val simpleIntVar: Variable = b.Variable("A", "Int")

    val simpleExists: Exists = b.Exists(simpleIntVar, b.Equals(simpleIntVar, int1))

    val simpleForAll: ForAll = b.ForAll(simpleIntVar, b.Equals(simpleIntVar, b.Variable("Y", "Int")))

    val simpleEquals: Equals = b.Equals(simpleOr, top)

    val simpleList: Seq[Pattern] = Seq(top, bottom, simpleAnd, simpleOr, simpleNot, simpleImplies,
      simpleIntVar, simpleExists, simpleForAll, simpleEquals)
  }


  def b: Build.Builders = DefaultBuilders

  def t = TestPatterns

  def identityF: (Pattern) => Pattern = (x) => x

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
    val pList: Seq[Pattern] = TestPatterns.simpleList

    assert(pList.map(TestFunctions.map(identityF)).equals(pList))
  }

  @Test def simpleQuantifierTests(): Unit = {

    def changeVar: (Pattern) => Pattern = { p =>
      p match {
        case Variable(name, sort) => b.Variable("#" + name, sort)
        case n@_ => n
      }
    }

    val changedVar: Variable = b.Variable("#A", "Int")

    val changedExists: Exists = b.Exists(changedVar, b.Equals(changedVar, TestPatterns.int1))

    assert(TestFunctions.map(changeVar)(TestPatterns.simpleExists) == changedExists)

  }


}
