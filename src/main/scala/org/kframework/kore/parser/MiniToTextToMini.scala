package org.kframework.kore.parser

import org.apache.commons.io.FileUtils
import org.kframework.kore.implementation.builders.DefaultKOREBuilders
import org.kframework.kore.interfaces.builders.KOREBuilders
import org.kframework.kore.interfaces.outer._

// TODO(Daejun): drop this file

object MiniToTextToMini {

  def koreBuilder: KOREBuilders = DefaultKOREBuilders

  def apply(d: Definition): Definition = {
    val text = MiniToText.apply(d)
    val file = new java.io.File("/tmp/x")
    FileUtils.writeStringToFile(file, text)
    val d2 = new TextToMini(koreBuilder).parse(file)
    val text2 = MiniToText.apply(d2)
    assert(d == d2)
    d2
  }

  def assertequal(d1: Definition, d2: Definition): Unit = assert(d1 == d2)
}
