package org.kframework.kore

object implicits {
  implicit class RichBuilders(b: Builders) {
    def convert(att: Attributes): Attributes = ???
    def convert(t: Pattern): Pattern = ???
    def convert(t: Module): Module = ???
  }
}
