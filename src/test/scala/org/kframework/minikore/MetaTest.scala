package org.kframework.minikore

import org.junit.Test
import org.junit.Assert._
import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.tree._
import org.kframework.minikore.implementation.DefaultBuilders
import org.kframework.minikore.interfaces.build


class MetaTest {

  val b: build.Builders = DefaultBuilders
  val metaLevel = MiniKoreMeta(b)
  import b._
  import metaLevel._

  def testMetaLevel[A](ioPairs: Seq[(A, Application)], up: A => Application, down: Pattern => A): Unit = {
    ioPairs foreach { case (input, output) =>

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
    }
  }

  @Test def domainValueTest(): Unit = {
    val dvTests: Seq[(DomainValue, Application)]
        = Seq( ( DomainValue(Symbol("Sym1"), "mySymbol") , Application(KMLDomainValue, Seq(Application(Symbol("Sym1"), Seq.empty), Application(Symbol("mySymbol"), Seq.empty))) )
             , ( DomainValue(Symbol("Sym2"), "_+_")      , Application(KMLDomainValue, Seq(Application(Symbol("Sym2"), Seq.empty), Application(Symbol("_+_"), Seq.empty)))      )
             )
    testMetaLevel(dvTests, upDomainValue, downDomainValue)
  }

  @Test def variableTest(): Unit = {
    val varTests: Seq[(Variable, Application)]
        = Seq( ( Variable("x", Sort("Int"))   , Application(KMLVariable, Seq(Application(Symbol("x"), Seq.empty), upSort(Sort("Int"))))   )
             , ( Variable("y", Sort("Float")) , Application(KMLVariable, Seq(Application(Symbol("y"), Seq.empty), upSort(Sort("Float")))) )
             )
    testMetaLevel(varTests, upVariable, downVariable)
  }

  @Test def symbolTest(): Unit = {
    val symbolTests: Seq[(Symbol, Application)]
        = Seq( ( Symbol("mySym")  , Application(KMLDomainValue, Seq(Application(KSymbol, Seq.empty), Application(Symbol("mySym"), Seq.empty)))  )
             , ( Symbol("mySym2") , Application(KMLDomainValue, Seq(Application(KSymbol, Seq.empty), Application(Symbol("mySym2"), Seq.empty))) )
             )
    testMetaLevel(symbolTests, upSymbol, downSymbol)
  }

  @Test def sortTest(): Unit = {
    val sortTests: Seq[(Sort, Application)]
        = Seq( ( Sort("Int")   , Application(KMLDomainValue, Seq(Application(KSort, Seq.empty), Application(Symbol("Int"), Seq.empty)))   )
             , ( Sort("Float") , Application(KMLDomainValue, Seq(Application(KSort, Seq.empty), Application(Symbol("Float"), Seq.empty))) )
             )
    testMetaLevel(sortTests, upSort, downSort)
  }

  @Test def nameTest(): Unit = {
    val nameTests: Seq[(Name, Application)]
        = Seq( ( "x"     , Application(Symbol("x"), Seq.empty)     )
             , ( "zoenu" , Application(Symbol("zoenu"), Seq.empty) )
             )
    testMetaLevel(nameTests, upName, downName)
  }

  @Test def valueTest(): Unit = {
    val valueTests: Seq[(Value, Application)]
        = Seq( ( "x"     , Application(Symbol("x"), Seq.empty)     )
             , ( "zoenu" , Application(Symbol("zoenu"), Seq.empty) )
             )
    testMetaLevel(valueTests, upValue, downValue)
  }

  @Test def sortListTest(): Unit = {
    val sortListTests: Seq[(Seq[Sort], Application)]
        = Seq( ( Seq.empty                                          , Application(KSortListMt, Seq.empty)                                                                                     )
             , ( Seq(Sort("Int"))                                   , Application(KSortList, Seq(upSort(Sort("Int")), Application(KSortListMt, Seq.empty)))                                   )
             , ( Seq(Sort("Int"), Sort("Float"), Sort("List{Int}")) , Application(KSortList, Seq( upSort(Sort("Int"))
                                                                                                , Application(KSortList, Seq( upSort(Sort("Float"))
                                                                                                                            , Application(KSortList, Seq( upSort(Sort("List{Int}"))
                                                                                                                                                        , Application(KSortListMt, Seq.empty)
                                                                                                                                                        ))))))                                )
             )
    testMetaLevel(sortListTests, upSortList, downSortList)
  }

  def patternTest(): Unit = ???
  def patternListTest(): Unit = ???

  def attributesTest(): Unit = ???
  def sentenceTest(): Unit = ???

  def moduleTest(): Unit = ???
  def definitionTest(): Unit = ???

}
