package org.kframework.minikore

import org.junit.Test
import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.tree._
import org.kframework.minikore.implementation.DefaultBuilders
import org.kframework.minikore.interfaces.build


class NodeTest {

  object TestFunctions {

    def size(p: Pattern): Int = p match {
      case Node(c: Seq[Pattern]) => c.map(size).sum
      case Leaf(_) => 1
    }

    def getNode0Count(p: Pattern): Int = p match {
      case Node0() => 1
      case Node(c: Seq[Pattern]) => c.map(getNode0Count) sum
      case _ => 0
    }

    def getLabelledNodesCount(p: Pattern): Int = p match {
      case LabeledNode(_, c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum + 1
      case Node(c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum
      case _ => 0
    }

    def getNode1Count(p: Pattern): Int = p match {
      case Node1(p: Pattern) => 1 + getNode1Count(p)
      case Node(c: Seq[Pattern]) => 0 + (c.map(getNode1Count) sum)
      case Leaf(_) => 0
    }

    def getNode2Count(p: Pattern): Int = p match {
      case Node2(x: Pattern, y: Pattern) => 1 + (getNode2Count(x) + getNode2Count(y))
      case Node(c: Seq[Pattern]) => 0 + (c.map(getNode1Count) sum)
      case _ => 0
    }

    def getLeafCount(p: Pattern): Int = p match {
      case Leaf(_) => 1
      case Node(c: Seq[Pattern]) => c.map(getLeafCount) sum
      case _ => 0
    }

    def getLeaf2Count(p: Pattern): Int = p match {
      case Leaf2(_, _) => 1
      case Node(c: Seq[Pattern]) => c.map(getLeaf2Count) sum
      case _ => 0
    }

    def renameVariable(p: Pattern): Pattern = p match {
      case n@BinderNode(v@Variable(Name(name), _), p: Pattern) => {
        val freshVar: Pattern = v.build(Name("#" + name), v._2)
        n.build(freshVar, renameVariable(p))
      }
      case n@Node(c: Seq[Pattern]) => n.build(c.map(renameVariable))
      case Variable(Name(name: String), s: Sort) => b.Variable(Name("#" + name), s)
      case other@_ => other
    }

    def map(f: Pattern => Pattern)(p: Pattern): Pattern = p match {
      case n@Node2(p: Pattern, q: Pattern) => n.build(map(f)(p), map(f)(q))
      case n@Node(c: Seq[AST]) => n.build(c.map(map(f)))
      case l@Leaf(_) => f(l)
    }

  }

  object TestPatterns {
    val b: build.Builders = DefaultBuilders

    val int1: Pattern = b.DomainValue(Label("Int"), Value("1"))

    val int2: Pattern = b.DomainValue(Label("Int"), Value("2"))

    val int4: Pattern = b.DomainValue(Label("Int"), Value("4"))

    val stringFoo: Pattern = b.DomainValue(Label("String"), Value("foo"))

    val intVar = b.Variable(Name("A"), Sort("Int"))

    val e1: Pattern = b.And(intVar, int1)

    val e2: Pattern = b.And(b.Variable(Name("C"), Sort("String")), stringFoo)

    val plusApp: Pattern = b.Application(Label("Plus"), Seq(int1, int2))

    val simpleVariable: Variable = b.Variable(Name("X"), Sort("Test"))

    val simpleDomainValue: DomainValue = b.DomainValue(Label("test"), Value("String"))

    val top: Top = b.Top()

    val bottom: Bottom = b.Bottom()

    val simpleAnd: And = b.And(top, bottom)

    val simpleOr: Or = b.Or(top, bottom)

    val simpleNot: Not = b.Not(top)

    val simpleImplies: Implies = b.Implies(bottom, top)

    val simpleIntVar: Variable = b.Variable(Name("A"), Sort("Int"))

    val simpleExists: Exists = b.Exists(simpleIntVar, b.Equals(simpleIntVar, int1))

    val simpleForAll: ForAll = b.ForAll(simpleIntVar, b.Equals(simpleIntVar, b.Variable(Name("Y"), Sort("Int"))))

    val simpleEquals: Equals = b.Equals(simpleOr, top)

    val simpleList: Seq[Pattern] = Seq(top, bottom, simpleAnd, simpleOr, simpleNot, simpleImplies,
      simpleIntVar, simpleExists, simpleForAll, simpleEquals, plusApp, e1, e2)
  }


  def b: build.Builders = DefaultBuilders

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

  @Test def node1CountTest(): Unit = {
    assert(TestFunctions.getNode1Count(t.simpleNot) == 1)
  }

  @Test def node2CountTest(): Unit = {
    val n2Pattern: Pattern = b.And(t.simpleAnd, b.And(t.simpleAnd, b.Bottom()))
    println(TestFunctions.getNode2Count(n2Pattern))

    assert(TestFunctions.getNode2Count(n2Pattern) == 4)
  }

  @Test def node0CountTest(): Unit = {
    val n0Pattern = b.And(b.Top, b.Bottom())

    assert(TestFunctions.getNode0Count(n0Pattern) == 2)
  }

  @Test def leaf2CountTest(): Unit = {
    val leafPattern = b.Equals(TestPatterns.simpleIntVar, TestPatterns.int1)

    assert(TestFunctions.getLeaf2Count(leafPattern) == 2)
  }

  @Test def identityFunctionTest(): Unit = {
    val pList: Seq[Pattern] = TestPatterns.simpleList

    assert(pList.map(TestFunctions.map(identityF)).equals(pList))
  }

  @Test def simpleQuantifierTests(): Unit = {
    def changeVar: (Pattern) => Pattern = {
      case Variable(Name(name), sort) => b.Variable(Name("#" + name), sort)
      case n@_ => n
    }

    val changedVar: Variable = b.Variable(Name("#A"), Sort("Int"))

    val changedExists: Exists = b.Exists(changedVar, b.Equals(changedVar, TestPatterns.int1))

    assert(TestFunctions.map(changeVar)(TestPatterns.simpleExists) == changedExists)
  }

  @Test def binderTest(): Unit = {
    def binder: Seq[Pattern] = Seq(t.simpleExists, t.simpleForAll)

    val changedVars: Seq[Pattern] = binder.map(TestFunctions.renameVariable)
    assert(Seq(b.Exists(b.Variable(Name("#A"), Sort("Int")),
      b.Equals(b.Variable(Name("#A"), Sort("Int")), TestPatterns.int1)), b.ForAll(b.Variable(Name("#A"), Sort("Int")),
      b.Equals(b.Variable(Name("#A"), Sort("Int")), b.Variable(Name("#Y"), Sort("Int"))))) == changedVars)
  }

  @Test def binderAsNode2Test(): Unit = {
    val node2Patterns: Seq[Pattern] = Seq(TestPatterns.simpleExists, TestPatterns.simpleForAll,
      TestPatterns.simpleAnd)

    val notNode2Patterns: Seq[Pattern] = Seq(TestPatterns.plusApp, TestPatterns.int1)

    val collectedPatterns: Seq[Pattern] = (node2Patterns :+ notNode2Patterns).collect({
      case n@Node2(x: Pattern, y: Pattern) => n.build(x, y)
    })

    assert(node2Patterns == collectedPatterns)
  }
}
