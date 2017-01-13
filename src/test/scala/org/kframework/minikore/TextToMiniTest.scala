package org.kframework.minikore

import org.apache.commons.io.FileUtils
import org.junit.Assert.assertEquals
import org.junit.Test
import org.kframework.minikore.MiniKore._

class TextToMiniTest {

  @Test def parseTest1(): Unit = {
    parseTest("imp-lesson-4.kore")
  }

  @Test def parseTest2(): Unit = {
    parseTest("kool-typed-dynamic.kore")
  }

  @Test def parseTest3(): Unit = {
    parseTest("imp.kore")
  }

  def parseTest(file: String): Unit = {
    val src1 = io.Source.fromResource(file)
    val src2 = io.Source.fromResource(file)
    val begin = java.lang.System.nanoTime()
    val minikore = new TextToMini().parse(src1)
    val end = java.lang.System.nanoTime(); println(end - begin)
    val text = MiniToText.apply(minikore)
//    val outputfile = new java.io.File("/tmp/x")
//    FileUtils.writeStringToFile(outputfile, text)
    assertEquals(src2.mkString, text)
    src1.close()
    src2.close()
  }

}
