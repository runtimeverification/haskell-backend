package org.kframework.kore

import org.apache.commons.io.FileUtils
import org.junit.Assert.assertEquals
import org.junit.Test
import org.kframework.kore.implementation.DefaultBuilders
import org.kframework.kore.parser.{KoreToText, ParseError, TextToKore}

class TextToKoreTest {

  @Test def parseTest1(): Unit = {
    parseFromFile("imp-lesson-4.kore")
  }

  @Test def parseTest2(): Unit = {
    parseFromFile("kool-typed-dynamic.kore")
  }

  @Test def parseTest3(): Unit = {
    parseFromFile("imp.kore")
  }

  @Test def parseFileTest4(): Unit = {
    parseFromFile("p4.kore")
  }

  @Test def parseTest4(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  import B []
        |  axiom \top ( ) [ ]
        |  axiom \and  (  \top (   ) ,   \bottom (  )  )  [   ]
        |  axiom \or  (  \top (   ) ,   \bottom (  )  )  [   ]
        |  axiom \forall  ( X:K, \top() ) [ ]
        |  axiom ` f o o `() []
        |  axiom ` _,_( ) `() []
        |endmodule []
        |""")
    parseFromString(s)
  }

  @Test def parseTest5(): Unit = {
    val s =
      strip("""
        |[]
        |""")
    parseFromString(s)
  }

  @Test def parseTest6(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |endmodule []
        |""")
    parseFromString(s)
  }

  @Test def parseTest7(): Unit = {
    val s = "[] \t"
    parseFromString(s)
  }

  @Test def parseTestFail1(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  impor t B []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 8: Expected 't', but ' '
            |  impor t B []
            |       ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail2(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  import B OOL []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 12: Expected '[', but 'O'
            |  import B OOL []
            |           ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail3(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom fo o() []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 12: Expected ':' or '(', but 'o'
            |  axiom fo o() []
            |           ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail4(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom ` ...\`... `() []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 16: Expected ':' or '(', but '.'
            |  axiom ` ...\`... `() []
            |               ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail5(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom foo(X:K, Y:K, ) []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 23: Expected <Symbol>, but ')'
            |  axiom foo(X:K, Y:K, ) []
            |                      ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail6(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom foo(, Y:K) []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 13: Expected <Symbol>, but ','
            |  axiom foo(, Y:K) []
            |            ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail7(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom \my()
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 11: Expected \top, \bottom, \and, \or, \not, \implies, \exists, \forall, \next, \rewrite, or \equals, but '\my'
            |  axiom \my()
            |          ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail8(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  i mport B []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 4: Expected 'm', but ' '
            |  i mport B []
            |   ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail9(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom \to p() []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 12: Expected 'p', but ' '
            |  axiom \to p() []
            |           ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail10(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom \t op() []
        |endmodule []
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 11: Expected \top, \bottom, \and, \or, \not, \implies, \exists, \forall, \next, \rewrite, or \equals, but '\t '
            |  axiom \t op() []
            |          ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail11(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  axiom \t
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 11: Expected \top, \bottom, \and, \or, \not, \implies, \exists, \forall, \next, \rewrite, or \equals, but '\t '
            |  axiom \t
            |          ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail12(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  syntax X
        |endmodule
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 4: Column 1: Expected '[' or ':', but 'e'
            |endmodule
            |^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail13(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  dummy
        |endmodule
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 3: Expected import, syntax, rule, axiom, or endmodule, but 'd'
            |  dummy
            |  ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail14(): Unit = {
    val s =
      strip("""
        |[]
        |module _A
        |endmodule
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 2: Column 8: Expected <ModuleName>, but '_'
            |module _A
            |       ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFail15(): Unit = {
    val s =
      strip("""
        |[]
        |module A
        |  syntax X ::= x(Y Z) []
        |endmodule
        |""")
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
            |ERROR: Line 3: Column 20: Expected ')' or ',', but 'Z'
            |  syntax X ::= x(Y Z) []
            |                   ^
            |"""),
          msg)
    }
  }

  @Test def parseTestFailWhiteSpacesPrefix(): Unit = {
    val s =
      """
        |
        |
        |
        |[]
        |module A
        |endmodule [}
        |""".stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
                  |ERROR: Line 7: Column 12: Expected <Symbol>, but '}'
                  |endmodule [}
                  |           ^
                  |"""),
          msg)
    }
  }
// TODO: Improve error message above to say "Expected <Symbol> or ']' ..."

  @Test def parseTestFailWhiteSpacesSuffix(): Unit = {
    val s =
      """
        |[]
        |module A
        |endmodule [}
        |
        |
        |
        |""".stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
                  |ERROR: Line 4: Column 12: Expected <Symbol>, but '}'
                  |endmodule [}
                  |           ^
                  |"""),
          msg)
    }
  }

  @Test def parseTestFailUnfinishedModule(): Unit = {
    val s =
      """
        |[]
        |module A
        |endmodule
        |""".stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
                  |ERROR: Unexpected end of file while parsing
                  |"""),
          msg)
    }
  }

  @Test def parseTestFailJunkAfterModule(): Unit = {
    val s =
      """
        |[]
        |module A
        |endmodule []
        |  junk
        |""".stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case ParseError(msg) =>
        assertEquals(
          strip("""
                  |ERROR: Line 5: Column 3: Expected 'm', but 'j'
                  |  junk
                  |  ^
                  |"""),
          msg)
    }
  }
// TODO: Improve error message above to say "Expected 'm' or <EOF> ..."

  def strip(s: String): String = {
    trim(s.stripMargin)
  }

  def trim(s: String): String = {
    s.replaceAll("^\\s+|\\s+$", "") // s.replaceAll("^\\s+", "").replaceAll("\\s+$", "")
  }

  def parseFromStringWithExpected(s: String, expected: String): Unit = {
    val src = io.Source.fromString(s)
    try {
      parseTest(SourceFOS(src), s)
    } finally {
      src.close()
    }
  }

  def parseFromString(s: String): Unit = {
    val src = io.Source.fromString(s)
    try {
      parseTest(SourceFOS(src), s)
    } finally {
      src.close()
    }
  }

  def parseFromFile(file: String): Unit = {
    val f = FileUtils.toFile(getClass.getResource("/" + file))
    parseTest(FileFOS(f), FileUtils.readFileToString(f))
  }

  sealed trait FileOrSource
  case class FileFOS(x: java.io.File) extends FileOrSource
  case class SourceFOS(x: io.Source) extends FileOrSource

  /** Tests if parse is correct.
    *
    * Check:
    *   t == u(p(t))
    * otherwise,
    *   t == u(p(t)) modulo whitespaces
    *     and
    *   p(t) == p(u(p(t)))
    *
    * where:
    *   e in MiniKore
    *   t in String
    *   p : String -> MiniKore
    *   u : MiniKore -> String
    */
  def parseTest(src: FileOrSource, expected: String): Unit = {
    //TODO: Make test file parametric over builders.
    val builder: Builders = DefaultBuilders
    val begin = java.lang.System.nanoTime()
    val minikore = src match {
      case src: FileFOS => TextToKore(builder).parse(src.x)
      case src: SourceFOS => TextToKore(builder).parse(src.x)
    }
    val end = java.lang.System.nanoTime(); println(end - begin)
    val text = KoreToText(minikore)
    // val outputfile = new java.io.File("/tmp/x")
    // FileUtils.writeStringToFile(outputfile, text)
    if (expected == text) () // t == u(p(t))
    else if (trim(expected) == trim(text)) () // t == u(p(t)) modulo leading/trailing whitespaces
    else {
      assertEquals(expected.replaceAll("\\s+", ""), text.replaceAll("\\s+", "")) //   t  ==   u(p(t))  modulo whitespaces
      assertEquals(minikore, new TextToKore(builder).parse(io.Source.fromString(text))) // p(t) == p(u(p(t)))
    }
  }

//  @Test def errorTest(): Unit = {
//    new TextToMini().error('a', "abc") match {
//      case ParseError(msg) =>
//        assertEquals(
//          strip("""
//            |ERROR: Line 0: Column 0: Expected 'a', but abc
//            |null
//            |^
//            |"""),
//          msg)
//      case _ => assert(false)
//    }
//  }

}
