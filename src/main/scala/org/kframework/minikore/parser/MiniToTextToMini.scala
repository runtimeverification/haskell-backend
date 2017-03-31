package org.kframework.minikore.parser

import org.apache.commons.io.FileUtils
import org.kframework.minikore.implementation.outer.DefaultOuterBuilders
import org.kframework.minikore.implementation.pattern.DefaultPatternBuilders
import org.kframework.minikore.interfaces.outer._
import org.kframework.minikore.interfaces.pattern._

// TODO(Daejun): drop this file

object MiniToTextToMini {

  def defaultOuter: OuterBuilders = DefaultOuterBuilders
  def defaultPattern: PatternBuilders = DefaultPatternBuilders

  def apply(d: Definition): Definition = {
    val text = MiniToText.apply(d)
    val file = new java.io.File("/tmp/x")
    FileUtils.writeStringToFile(file, text)
    val d2 = new TextToMini(defaultOuter, defaultPattern).parse(file)
    val text2 = MiniToText.apply(d2)
    assert(d == d2)
    d2
  }

  def assertequal(d1: Definition, d2: Definition): Unit = assert(d1 == d2)
}
