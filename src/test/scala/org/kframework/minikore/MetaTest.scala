package org.kframework.minikore

import org.junit.Test
import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.tree._
import org.kframework.minikore.implementation.DefaultBuilders
import org.kframework.minikore.interfaces.build
import org.kframework.minikore.MiniKoreMeta._


class MetaTest {

  val b: build.Builders = DefaultBuilders
  import b._

  def testMetaLevel[A](ioPairs: Seq[(A, Application)], up: A => Application, down: Pattern => A): Unit = {
    ioPairs forEach ((input, output) => {

      // test inverse of up/down functions
      assertEquals(output, up(input))
      assertEquals(input, down(output))

      // test stability of representation wrt upPattern/downPattern
      val upP2   : Pattern => Pattern = upPattern   andThen upPattern
      val downP2 : Pattern => Pattern = downPattern andThen downPattern
      assertEquals(input, down(downP2(upP2(up(input)))))
      assertEquals(output, downP2(upP2(up(input))))
      assertEquals(input, down(downPattern(downP2(upPattern(upP2(up(input)))))))
      assertEquals(output, downPattern(downP2(upPattern(upP2(up(input))))))
    })
  }

  @Test def domainValueTest(): Unit = {
    val dvTests: Seq[(DomainValue, Application)]
        = Seq( (DomainValue(Symbol("Sym1"), "mySymbol") , Application(KMLDomainValue, Seq(Application(Symbol("Sym1"), Seq.empty), Application(Symbol("mySymbol"), Seq.empty))))
             , (DomainValue(Symbol("Sym2"), "_+_")      , Application(KMLDomainValue, Seq(Application(Symbol("Sym2"), Seq.empty), Application(Symbol("_+_"), Seq.empty))))
             )
    testMetaLevel(dvTests, upDomainValue, downDomainValue)
  }

  @Test def variableTest(): Unit = {
    val varTests: Seq[(Variable, Application)]
        = Seq( (Variable("x", Sort("Int"))   , Application(KMLVariable, Seq(Application(Symbol("x"), Seq.empty), Application(Symbol("Int"), Seq.empty))))
             , (Variable("y", Sort("Float")) , Application(KMLVariable, Seq(Application(Symbol("y"), Seq.empty), Application(Symbol("Float"), Seq.empty))))
             )
    testMetaLevel(varTests, upVariable, downVariable)
  }

  @Test def symbolTest(): Unit = {
    val symbolTests: Seq[(Symbol, Application)]
        = Seq( (Symbol("mySym")  , Application(KMLDomainValue, Seq(Application(KSymbol, Seq.empty), Application(Symbol("mySym"), Seq.empty))))
             , (Symbol("mySym2") , Application(KMLDomainValue, Seq(Application(KSymbol, Seq.empty), Application(Symbol("mySym2"), Seq.empty))))
             )
    testMetaLevel(symbolTests, upSymbol, downSymbol)
  }

  def sortTest(): Unit = ???
  def nameTest(): Unit = ???
  def valueTest(): Unit = ???
  def sortListTest(): Unit = ???

  def patternTest(): Unit = ???
  def patternListTest(): Unit = ???

  def attributesTest(): Unit = ???
  def sentenceTest(): Unit = ???

  def moduleTest(): Unit = ???
  def definitionTest(): Unit = ???

}
