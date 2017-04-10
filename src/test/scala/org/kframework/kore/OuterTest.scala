package org.kframework.kore

import org.junit.Test
import org.junit.Assert.assertEquals
import org.kframework.kore.implementation.builders.DefaultOuterBuilders
import org.kframework.kore.implementation.builders.DefaultPatternBuilders
import org.kframework.kore.interfaces.builders.OuterBuilders
import org.kframework.kore.interfaces.builders.PatternBuilders
import org.kframework.kore.interfaces.outer._
import org.kframework.kore.interfaces.pattern._
import org.kframework.kore.parser.TextToMini


class OuterTest {

  import DefaultOuterBuilders._
  import DefaultPatternBuilders._

  val int1: Pattern = DomainValue(interfaces.pattern.Symbol("Int"), "1")

  val patternBuilder: PatternBuilders = DefaultPatternBuilders
  val outerBuilder: OuterBuilders = DefaultOuterBuilders

  val import1: Import = Import("B", Seq.empty)
  val sortDec: SortDeclaration = SortDeclaration(Sort("Exp"), Seq.empty)
  val symbolDec: SymbolDeclaration = SymbolDeclaration(Sort("Exp"), Symbol("myExp"), Seq(Sort("Exp"), Sort("Int")), Seq.empty)
  val rule: Rule = Rule(int1, Seq.empty)
  val axiom: Axiom = Axiom(int1, Seq.empty)

  val emptyModule: Module = Module("A", Seq.empty, Seq.empty)
  val importModule: Module = Module("A", Seq(import1), Seq.empty)
  val sortDecModule: Module = Module("A", Seq(sortDec), Seq.empty)
  val symbolDecModule: Module = Module("A", Seq(symbolDec), Seq.empty)
  val ruleModule: Module = Module("A", Seq(rule), Seq.empty)
  val axiomModule: Module = Module("A", Seq(axiom), Seq.empty)

  val combinedModule1 = Module("B", Seq(sortDec, symbolDec), Seq.empty)
  val combinedModule2 = Module("C", Seq(import1, symbolDec, rule, axiom), Seq.empty)

  val emptyModuleDef: Definition = Definition(Seq(emptyModule), Seq.empty)
  val importDef: Definition = Definition(Seq(importModule), Seq.empty)
  val sortDef: Definition = Definition(Seq(sortDecModule), Seq.empty)
  val symbolDecDef: Definition = Definition(Seq(symbolDecModule), Seq.empty)
  val ruleDef: Definition = Definition(Seq(ruleModule), Seq.empty)
  val axiomDef: Definition = Definition(Seq(axiomModule), Seq.empty)

  val combinedDef: Definition = Definition(Seq(emptyModule, combinedModule1, combinedModule2), Seq.empty)

  val textEmptyModuleDef: String = {
    """
    []
    module A
    endmodule []
    """
  }

  val textImportDef: String = {
    """
    []
    module A
      import B []
    endmodule []
    """
  }

  val textSortDecDef: String = {
    """
    []
    module A
      syntax Exp []
    endmodule []
    """
  }

  val textSymbolDecDef: String = {
    """
    []
    module A
      syntax Exp ::= myExp(Exp, Int) []
    endmodule []
    """
  }

  val textRuleDef: String = {
    """
    []
    module A
      rule `Int`("1") []
    endmodule []
    """
  }

  val textAxiomDef: String = {
    """
    []
    module A
      axiom `Int`("1") []
    endmodule []
    """
  }

  val textCombinedDef: String = {
    """
    []
    module A
    endmodule []
    module B
      syntax Exp []
      syntax Exp ::= myExp(Exp, Int) []
    endmodule []
    module C
      import B []
      syntax Exp ::= myExp(Exp, Int) []
      rule `Int`("1") []
      axiom `Int`("1") []
    endmodule []
    """
  }

  def parseAndTest(source: String, expected: Definition): Unit = {
    val parser = TextToMini(outerBuilder, patternBuilder)
    assertEquals(parser.parse(io.Source.fromString(source)), expected)
  }

  @Test def emptyModuleDefTest(): Unit = {
    parseAndTest(textEmptyModuleDef, emptyModuleDef)
  }

  @Test def importTest(): Unit = {
    parseAndTest(textImportDef, importDef)
  }

  @Test def sortDecTest(): Unit = {
    parseAndTest(textSortDecDef, sortDef)
  }

  @Test def symbolDecTest(): Unit = {
    parseAndTest(textSymbolDecDef, symbolDecDef)
  }

  @Test def ruleTest(): Unit = {
    parseAndTest(textRuleDef, ruleDef)
  }

  @Test def axiomTest(): Unit = {
    parseAndTest(textAxiomDef, axiomDef)
  }

  @Test def combinedTest(): Unit = {
    parseAndTest(textCombinedDef, combinedDef)
  }

}
