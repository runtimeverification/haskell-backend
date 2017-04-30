package org.kframework.kore.extended

import org.kframework.kore

trait RichDefinition {
  def apply(defintion: kore.Definition): RichDefinition
}

trait RichModule {
  def apply(module: kore.Module): RichModule
}

trait RichAttributes {
  def apply(attributes: kore.Attributes) : RichAttributes
}

