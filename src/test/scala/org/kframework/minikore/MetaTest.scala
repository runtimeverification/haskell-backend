package org.kframework.minikore

import org.junit.Test
import org.junit.Assert._
import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.implementation.DefaultBuilders
import org.kframework.minikore.interfaces.build
import org.kframework.minikore.implementation.MiniKore.{Attributes, Sentence, Import, SortDeclaration, SymbolDeclaration, Rule, Axiom, Module, Definition}


class MetaTest {

  val b: build.Builders = DefaultBuilders
  val metaLevel = MiniKoreMeta(b)
  import b._
  import metaLevel._

  def testMetaLevel[A](ioPairs: Seq[(A, Pattern)], up: A => Pattern, down: Pattern => A): Unit = {
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

  @Test def symbolTest(): Unit = {
    val symbolTests: Seq[(Symbol, DomainValue)]
        = Seq( ( Symbol("mySym")  , DomainValue(KSymbol, "mySym")  )
             , ( Symbol("mySym2") , DomainValue(KSymbol, "mySym2") )
             )
    testMetaLevel(symbolTests, upSymbol, downSymbol)
  }

  @Test def sortTest(): Unit = {
    val sortTests: Seq[(Sort, DomainValue)]
        = Seq( ( Sort("Int")   , DomainValue(KSort, "Int")   )
             , ( Sort("Float") , DomainValue(KSort, "Float") )
             )
    testMetaLevel(sortTests, upSort, downSort)
  }

  @Test def nameTest(): Unit = {
    val nameTests: Seq[(Name, DomainValue)]
        = Seq( ( "x"     , DomainValue(KName, "x")     )
             , ( "zoenu" , DomainValue(KName, "zoenu") )
             )
    testMetaLevel(nameTests, upName, downName)
  }

  @Test def valueTest(): Unit = {
    val valueTests: Seq[(Value, DomainValue)]
        = Seq( ( "x"     , DomainValue(KValue, "x")     )
             , ( "zoenu" , DomainValue(KValue, "zoenu") )
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

  @Test def domainValueTest(): Unit = {
    val dvTests: Seq[(DomainValue, Application)]
        = Seq( ( DomainValue(Symbol("Sym1"), "mySymbol") , Application(KDomainValue, Seq(upSymbol(Symbol("Sym1")), upValue("mySymbol"))) )
             , ( DomainValue(Symbol("Sym2"), "_+_")      , Application(KDomainValue, Seq(upSymbol(Symbol("Sym2")), upValue("_+_")))      )
             )
    testMetaLevel(dvTests, upDomainValue, downDomainValue)
  }

  @Test def variableTest(): Unit = {
    val varTests: Seq[(Variable, Application)]
        = Seq( ( Variable("x", Sort("Int"))   , Application(KVariable, Seq(upName("x"), upSort(Sort("Int"))))   )
             , ( Variable("y", Sort("Float")) , Application(KVariable, Seq(upName("y"), upSort(Sort("Float")))) )
             )
    testMetaLevel(varTests, upVariable, downVariable)
  }

  @Test def patternTest(): Unit = {

    def mTop: Application                             = Application(KTop, Seq.empty)
    def mBot: Application                             = Application(KBottom, Seq.empty)
    def mNot(p: Pattern): Application                 = Application(KNot, Seq(p))
    def mAnd(p: Pattern, q: Pattern): Application     = Application(KAnd, Seq(p, q))
    def mOr(p: Pattern, q: Pattern): Application      = Application(KOr, Seq(p, q))
    def mImplies(p: Pattern, q: Pattern): Application = Application(KImplies, Seq(p, q))
    def mExists(p: Pattern, q: Pattern): Application  = Application(KExists, Seq(p, q))
    def mForAll(p: Pattern, q: Pattern): Application  = Application(KForAll, Seq(p, q))
    def mNext(p: Pattern): Application                = Application(KNext, Seq(p))
    def mRewrite(p: Pattern, q: Pattern): Application = Application(KRewrite, Seq(p, q))
    def mEquals(p: Pattern, q: Pattern): Application  = Application(KEquals, Seq(p, q))
    def mVar(n: Name, s: Sort): Application           = upVariable(Variable(n, s))
    def mDV(s: Symbol, v: Value): Application         = upDomainValue(DomainValue(s, v))

    val patternTests: Seq[(Pattern, Pattern)]
        = Seq( ( Bottom()                                     , mBot                                   )
             , ( Top()                                        , mTop                                   )
             , ( And(Bottom(), Top())                         , mAnd(mBot, mTop)                       )
             , ( Or(Top(), Top())                             , mOr(mTop, mTop)                        )
             , ( Implies(Top(), Bottom())                     , mImplies(mTop, mBot)                   )
             , ( Exists(Variable("x", Sort("Int")), Top())    , mExists(mVar("x", Sort("Int")), mTop)  )
             , ( ForAll(Variable("y", Sort("Bool")), Bottom()), mForAll(mVar("y", Sort("Bool")), mBot) )
             , ( Next(Top())                                  , mNext(mTop)                            )
             , ( Rewrite(Bottom(), Top())                     , mRewrite(mBot, mTop)                   )
             , ( Variable("x", Sort("Int"))                   , mVar("x", Sort("Int"))                 )
             , ( DomainValue(Symbol("dec"), "10")             , mDV(Symbol("dec"), "10")               )
             )
    testMetaLevel(patternTests, upPattern, downPattern)
  }

//    case Application(label, Nil)  => Application(KApplication, Seq(upSymbol(label)))
//    case Application(label, args) => Application(KApplication, Seq(upSymbol(label), upPatternList(args)))
//    case Top()                    => Application(KTop, Seq.empty)
//    case Bottom()                 => Application(KBottom, Seq.empty)
//    case And(p, q)                => Application(KAnd, Seq(upPattern(p), upPattern(q)))
//    case Or(p, q)                 => Application(KOr,  Seq(upPattern(p), upPattern(q)))
//    case Not(p)                   => Application(KNot,  Seq(upPattern(p)))
//    case Implies(p, q)            => Application(KImplies,  Seq(upPattern(p), upPattern(q)))
//    case Exists(v, p)             => Application(KExists,  Seq(upPattern(p)))
//    case ForAll(v, p)             => Application(KForAll,  Seq(upPattern(p)))
//    case Next(p)                  => Application(KNext,  Seq(upPattern(p)))
//    case Rewrite(p, q)            => Application(KRewrite,  Seq(upPattern(p), upPattern(q)))
//    case Equals(p, q)             => Application(KEquals,  Seq(upPattern(p), upPattern(q)))
//    case vb@Variable(_, _)        => upVariable(vb)
//    case dv@DomainValue(_, _)     => upDomainValue(dv)

  @Test def patternListTest(): Unit = {
    val patternListTests: Seq[(Seq[Pattern], Application)]
        = Seq( ( Seq.empty, Application(KPatternListMt, Seq.empty) )
             , ( Seq(Top()), Application(KPatternList, Seq(upPattern(Top()), Application(KPatternListMt, Seq.empty))) )
             , ( Seq(Top(), Next(Top()), Bottom()), Application(KPatternList, Seq(upPattern(Top()),
                   Application(KPatternList, Seq(upPattern(Next(Top())),
                     Application(KPatternList, Seq(upPattern(Bottom()),
                       Application(KPatternListMt, Seq.empty)))))))                                                    )
             )
    testMetaLevel(patternListTests, upPatternList, downPatternList)
  }

  @Test def attributesTest(): Unit = {
    val attributesTest: Seq[(Attributes, Pattern)]
        = Seq( ( Seq.empty, Application(KAttributesMt, Seq.empty)                                                                   )
             , ( Seq(Top()), Application(KAttributes, Seq(upPatternList(Seq(Top()))))                                               )
             , ( Seq(Top(), Next(Top()), Bottom()), Application(KAttributes, Seq(upPatternList(Seq(Top(), Next(Top()), Bottom())))) )
             )
    testMetaLevel(attributesTest, upAttributes, downAttributes)
  }

  @Test def sentenceTest(): Unit = {
    val sentenceTest: Seq[(Sentence, Application)]
        = Seq ( ( Import("EXP", Seq(Top()))              , Application(KImport, Seq(upName("EXP"), upAttributes(Seq(Top()))))               )
              , ( SortDeclaration(Sort("Int"), Seq.empty), Application(KSortDeclaration, Seq(upSort(Sort("Int")), upAttributes(Seq.empty))) )
              , ( SymbolDeclaration(Sort("Exp"), Symbol("myExp"), Seq(Sort("Exp"), Sort("Int")), Seq.empty),
                    Application(KSymbolDeclaration, Seq(upSort(Sort("Exp")), upSymbol(Symbol("myExp")),
                      upSortList(Seq(Sort("Exp"), Sort("Int"))), upAttributes(Seq.empty)))                                                  )
              , ( Rule(Top(), Seq(Bottom()))             , Application(KRule, Seq(upPattern(Top()), upAttributes(Seq(Bottom()))))           )
              , ( Axiom(Bottom(), Seq(Top()))            , Application(KAxiom, Seq(upPattern(Bottom()), upAttributes(Seq(Top()))))          )
              )
    testMetaLevel(sentenceTest, upSentence, downSentence)
  }

  @Test def moduleTest(): Unit = {
    val importSent = Import("BOOL", Seq(Top()))
    val symbolDecSent = SymbolDeclaration(Sort("Exp"), Symbol("myExp"), Seq(Sort("Exp"), Sort("Int")), Seq.empty)
    val moduleTest: Seq[(Module, Application)]
        = Seq( ( Module("BOOL", Seq.empty, Seq.empty),
                   Application(KModule, Seq(upName("BOOL"), Application(KSentenceListMt, Seq.empty), upAttributes(Seq.empty))) )
             , ( Module("EXP", Seq(importSent, symbolDecSent), Seq(Top())),
                   Application(KModule, Seq(upName("EXP"),
                     Application(KSentenceList, Seq(upSentence(importSent),
                       Application(KSentenceList, Seq(upSentence(symbolDecSent),
                         Application(KSentenceListMt, Seq.empty))))),
                     upAttributes(Seq(Top())))) )
             )
    testMetaLevel(moduleTest, upModule, downModule)
  }

  @Test def definitionTest(): Unit = {
    val importSent = Import("BOOL", Seq(Top()))
    val symbolDecSent = SymbolDeclaration(Sort("Exp"), Symbol("myExp"), Seq(Sort("Exp"), Sort("Int")), Seq.empty)
    val emptyModule = Module("BOOL", Seq.empty, Seq.empty)
    val nonEmptyModule = Module("EXP", Seq(importSent, symbolDecSent), Seq(Top()))
    val definitionTest: Seq[(Definition, Application)]
        = Seq( ( Definition(Seq.empty, Seq.empty),
                   Application(KDefinition, Seq(upAttributes(Seq.empty), Application(KModuleListMt, Seq.empty))) )
             , ( Definition(Seq(emptyModule, nonEmptyModule), Seq(Bottom())),
                   Application(KDefinition, Seq(upAttributes(Seq(Bottom())),
                     Application(KModuleList, Seq(upModule(emptyModule),
                       Application(KModuleList, Seq(upModule(nonEmptyModule),
                         Application(KModuleListMt, Seq.empty))))))) )
             )
    testMetaLevel(definitionTest, upDefinition, downDefinition)
  }

}
