package org.kframework

import org.apache.commons.io.FileUtils
import org.junit.Assert.assertEquals
import org.junit.Test
import org.kframework.kore.Builders
import org.kframework.kore.implementation.DefaultBuilders
import org.kframework.kore.parser.{KoreToText, ParseError, TextToKore}

class TextToKoreTest {

  /* Run all tests "testx.kore" for x = 1, 2, ... */
  @Test def runAllTests(): Unit = {
    var totalTestsNumber = 10
    var i = 1;
    for(i <- 1 to totalTestsNumber){
      var testfilename = "test" + i + ".kore"
      parseFromFile(testfilename)
    }
  }

  /*
  @Test def test1(): Unit = {
    parseFromFile("test1.kore")
  }
  @Test def test2(): Unit = {
    parseFromFile("test2.kore")
  }
  @Test def test3(): Unit = {
    parseFromFile("test3.kore")
  }
  @Test def test4(): Unit = {
    parseFromFile("test4.kore")
  }
  @Test def test5(): Unit = {
    parseFromFile("test5.kore")
  }
  @Test def test6(): Unit = {
    parseFromFile("test6.kore")
  }
  */


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
