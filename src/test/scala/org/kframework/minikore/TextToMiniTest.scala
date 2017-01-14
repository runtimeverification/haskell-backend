package org.kframework.minikore

import org.apache.commons.io.FileUtils
import org.junit.Assert.assertEquals
import org.junit.Test
import org.kframework.minikore.MiniKore._

class TextToMiniTest {

  @Test def parseTest1(): Unit = {
    parseFromFile("imp-lesson-4.kore")
  }

  @Test def parseTest2(): Unit = {
    parseFromFile("kool-typed-dynamic.kore")
  }

  @Test def parseTest3(): Unit = {
    parseFromFile("imp.kore")
  }

  @Test def parseTest4(): Unit = {
    val s =
      """
        |[]
        |module A
        |  import B []
        |  axiom \true ( ) [ ]
        |  axiom \and  (  \true (   ) ,   \false (  )  )  [   ]
        |  axiom ` f o o `() []
        |  axiom ` _,_( ) `() []
        |endmodule []
      """.stripMargin
    parseFromString(s)
  }

  @Test def parseTest5(): Unit = {
    val s =
      """
        |[]
      """.stripMargin
    parseFromString(s)
  }

  @Test def parseTest6(): Unit = {
    val s =
      """
        |[]
        |module A
        |endmodule []
      """.stripMargin
    parseFromString(s)
  }

  // TODO(Daejun): compare error messages

  @Test def parseTestFail1(): Unit = {
    val s =
      """
        |[]
        |module A
        |  impor t B []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 8: Expected 't', but ' '
            |  impor t B []
            |       ^
          """.stripMargin
    }
  }

  @Test def parseTestFail2(): Unit = {
    val s =
      """
        |[]
        |module A
        |  import B OOL []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 12: Expected '[', but 'O'
            |  import B OOL []
            |           ^
          """.stripMargin
    }
  }

  @Test def parseTestFail3(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom fo o() []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 12: Expected ':' or '(', but 'o'
            |  axiom fo o() []
            |           ^
          """.stripMargin
    }
  }

  @Test def parseTestFail4(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom ` ...\`... `() []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 16: Expected ':' or '(', but '.'
            |  axiom ` ...\`... `() []
            |               ^
          """.stripMargin
    }
  }

  @Test def parseTestFail5(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom foo(X:K, Y:K, ) []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 23: Expected <Symbol>, but ')'
            |  axiom foo(X:K, Y:K, ) []
            |                      ^
          """.stripMargin
    }
  }

  @Test def parseTestFail6(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom foo(, Y:K) []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 13: Expected <Symbol>, but ','
            |  axiom foo(, Y:K) []
            |            ^
          """.stripMargin
    }
  }

  @Test def parseTestFail7(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom \my()
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 11: Expected \true, \false, \and, \or, \not, \implies, \exists, \forall, \next, \rewrite, or \equal, but (m,y)
            |  axiom \my()
            |          ^
          """.stripMargin
    }
  }

  @Test def parseTestFail8(): Unit = {
    val s =
      """
        |[]
        |module A
        |  i mport B []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 4: Expected 'm', but ' '
            |  i mport B []
            |   ^
          """.stripMargin
    }
  }

  @Test def parseTestFail9(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom \tr ue() []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 12: Expected 'u', but ' '
            |  axiom \tr ue() []
            |           ^
          """.stripMargin
    }
  }

  @Test def parseTestFail10(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom \t rue() []
        |endmodule []
      """.stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 11: Expected \true, \false, \and, \or, \not, \implies, \exists, \forall, \next, \rewrite, or \equal, but (t, )
            |  axiom \t rue() []
            |          ^
          """.stripMargin
    }
  }

  @Test def parseTestFail11(): Unit = {
    val s =
      """
        |[]
        |module A
        |  axiom \t""".stripMargin
    try {
      parseFromString(s)
      assert(false)
    } catch {
      case _: Throwable => ()
        val msg =
          """
            |ERROR: Line 4: Column 12: Expected 'u', but ' '
            |  axiom \tr ue() []
            |           ^
          """.stripMargin
    }
  }

  def parseFromStringWithExpected(s: String, expected: String): Unit = {
    val src = io.Source.fromString(s)
    parseTest(src, s, true)
  }

  def parseFromString(s: String): Unit = {
    val src = io.Source.fromString(s)
    parseTest(src, s, true)
  }

  def parseFromFile(file: String): Unit = {
    val src1 = io.Source.fromResource(file)
    val src2 = io.Source.fromResource(file)
    parseTest(src1, src2.mkString, true)
  }

  def parseTest(src: io.Source, expected: String, ignoreSpaces: Boolean): Unit = {
    val begin = java.lang.System.nanoTime()
    val minikore = new TextToMini().parse(src)
    val end = java.lang.System.nanoTime(); println(end - begin)
    src.close()
    val text = MiniToText.apply(minikore)
//    val outputfile = new java.io.File("/tmp/x")
//    FileUtils.writeStringToFile(outputfile, text)
    if (ignoreSpaces) {
      assertEquals(expected.replaceAll("\\s+", ""), text.replaceAll("\\s+", ""))
    } else {
      assertEquals(expected, text)
    }
  }

}
