package org.kframework.kore

import org.junit.Test
import org.junit.Assert.assertEquals
import org.kframework.kore.implementation.builders.DefaultPatternBuilders
import org.kframework.kore.interfaces.builders.PatternBuilders
import org.kframework.kore.interfaces.pattern._
import org.kframework.kore.interfaces.tree._


case class TestPatterns(b: PatternBuilders) {

  import b._

  private val symbol = interfaces.pattern.Symbol("Int")

  val int1: Pattern = DomainValue(symbol, "1")

  val int2: Pattern = DomainValue(symbol, "2")

  val int4: Pattern = DomainValue(symbol, "4")

  val stringFoo: Pattern = DomainValue(Symbol("String"), "foo")

  val intVar = Variable("A", Sort("Int"))

  val e1: Pattern = And(intVar, int1)

  val e2: Pattern = And(Variable("C", Sort("String")), stringFoo)

  val plusApp: Pattern = Application(Symbol("Plus"), Seq(int1, int2))

  val simpleVariable: Variable = Variable("X", Sort("Test"))

  val simpleDomainValue: DomainValue = DomainValue(Symbol("test"), "String")

  val top: Top = Top()

  val bottom: Bottom = Bottom()

  val simpleAnd: And = And(top, bottom)

  val simpleOr: Or = Or(top, bottom)

  val simpleNot: Not = Not(top)

  val simpleImplies: Implies = Implies(bottom, top)

  val simpleIntVar: Variable = Variable("A", Sort("Int"))

  val simpleExists: Exists = Exists(simpleIntVar, Equals(simpleIntVar, int1))

  val simpleForAll: ForAll = ForAll(simpleIntVar, Equals(simpleIntVar, Variable("Y", Sort("Int"))))

  val simpleEquals: Equals = Equals(simpleOr, top)

  val simpleList: Seq[Pattern] = Seq(top, bottom, simpleAnd, simpleOr, simpleNot, simpleImplies,
    simpleIntVar, simpleExists, simpleForAll, simpleEquals, plusApp, e1, e2)
}

object ASTTestUtils {

  def size(p: Pattern): Int = p match {
    case Node(c: Seq[Pattern]) => c.map(size).sum
    case Leaf(_) => 1
  }

  def getNode0Count(p: Pattern): Int = p match {
    case Node0() => 1
    case Node(c: Seq[Pattern]) => c.map(getNode0Count).sum
    case Leaf(_) => 0
  }

  def getLabelledNodesCount(p: Pattern): Int = p match {
    case LabeledNode(_, c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum + 1
    case Node(c: Seq[Pattern]) => c.map(getLabelledNodesCount).sum
    case Leaf(_) => 0
  }

  def getNode1Count(p: Pattern): Int = p match {
    case Node1(p: Pattern) => getNode1Count(p) + 1
    case Node(c: Seq[Pattern]) => c.map(getNode1Count).sum
    case Leaf(_) => 0
  }

  def getNode2Count(p: Pattern): Int = p match {
    case Node2(x: Pattern, y: Pattern) => getNode2Count(x) + getNode2Count(y) + 1
    case Node(c: Seq[Pattern]) => c.map(getNode1Count).sum
    case Leaf(_) => 0
  }

  def getLeafCount(p: Pattern): Int = p match {
    case Leaf(_) => 1
    case Node(c: Seq[Pattern]) => c.map(getLeafCount).sum
  }

  def getLeaf2Count(p: Pattern): Int = p match {
    case Leaf2(_, _) => 1
    case Leaf(_) => 0
    case Node(c: Seq[Pattern]) => c.map(getLeaf2Count).sum
  }

  def renameAllVariables(p: Pattern): Pattern = p match {
    case n@Node(c: Seq[Pattern]) => n.build(c.map(renameAllVariables))
    case l@Leaf2(x: Name, y: Sort) => l match {
      case _: Variable => l.build("#" + x, y)
      case other@_ => other
    }
    case other@_ => other
  }

  def map(f: Pattern => Pattern)(p: Pattern): Pattern = p match {
    case n@Node2(p: Pattern, q: Pattern) => n.build(map(f)(p), map(f)(q))
    case n@Node(c: Seq[AST]) => n.build(c.map(map(f)))
    case l@Leaf(_) => f(l)
  }

  def subst(m: Map[Variable, Pattern])(p: Pattern): Pattern = {
    def fresh(v: Variable): Variable = v.build(v._1 + "!new!", v._2)

    p match {
      case v@Variable(_, _) => if (m.contains(v)) m(v) else p
      case bn@BinderNode(boundVar, boundPattern) => {
        val freshVar: Variable = fresh(boundVar)
        bn.build(freshVar, subst(m + (boundVar -> freshVar))(boundPattern))
      }
      case _ => map(subst(m))(p)
    }
  }

}

class NodeTest {

  import ASTTestUtils._

  //TODO: Make Tests Parametric Over Builders.
  val builder: PatternBuilders = DefaultPatternBuilders

  import builder._

  val testPatterns: TestPatterns = TestPatterns(builder)

  import testPatterns._

  @Test def sizeTest1(): Unit = {
    assertEquals(size(e1), 2)
  }

  @Test def sizeTest2(): Unit = {
    assertEquals(size(Equals(plusApp, int1)), 3)
  }

  @Test def labelledNodeCountTest(): Unit = {
    assertEquals(getLabelledNodesCount(Equals(intVar, plusApp)), 1)
  }

  @Test def node1CountTest(): Unit = {
    assertEquals(1, getNode1Count(simpleNot))
  }

  @Test def node2CountTest(): Unit = {
    val n2Pattern: Pattern = And(simpleAnd, And(simpleAnd, Bottom()))
    assertEquals(4, getNode2Count(n2Pattern))
  }

  @Test def node0CountTest(): Unit = {
    val n0Pattern = And(Top(), Bottom())

    assertEquals(2, getNode0Count(n0Pattern))
  }

  @Test def leaf2CountTest(): Unit = {
    val leafPattern = Equals(simpleIntVar, int1)

    assertEquals(2, getLeaf2Count(leafPattern))
  }

  @Test def identityFunctionTest(): Unit = {
    val pList: Seq[Pattern] = simpleList

    def identityF: (Pattern) => Pattern = (x) => x

    assertEquals(pList, pList.map(map(identityF)))
  }

  @Test def simpleQuantifierTests(): Unit = {
    val changedVar: Variable = Variable("#A", Sort("Int"))

    val changedExists: Exists = Exists(changedVar, Equals(changedVar, int1))

    assertEquals(changedExists, map(renameAllVariables)(simpleExists))
  }

  @Test def binderTest(): Unit = {
    def binder: Seq[Pattern] = Seq(simpleExists, simpleForAll)

    val changedVars: Seq[Pattern] = binder.map(renameAllVariables)
    assertEquals(Seq(Exists(Variable("#A", Sort("Int")),
      Equals(Variable("#A", Sort("Int")), int1)), ForAll(Variable("#A", Sort("Int")),
      Equals(Variable("#A", Sort("Int")), Variable("#Y", Sort("Int"))))), changedVars)
  }

  @Test def binderAsNode2Test(): Unit = {
    val node2Patterns: Seq[Pattern] = Seq(simpleExists, simpleForAll, simpleAnd)

    val notNode2Patterns: Seq[Pattern] = Seq(plusApp, int1)

    val collectedPatterns: Seq[Pattern] = (node2Patterns :+ notNode2Patterns).collect({
      case n@Node2(x: Pattern, y: Pattern) => n.build(x, y)
    })

    assertEquals(node2Patterns, collectedPatterns)
  }

  @Test def testSubstitution(): Unit = {
    val p = Top()
    val v = Bottom()
    val x = Variable("x", Sort("K"))
    val e = Exists(x, x)
    val x1 = Variable("x!new!", Sort("K"))
    val e1 = Exists(x1, x1)
    val m = Map(x -> v)
    assertEquals(subst(m)(p), p)
    assertEquals(subst(m)(x), v)
    assertEquals(subst(m)(e), e1)
  }

}
