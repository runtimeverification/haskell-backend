package org.kframework.kore.extended

import org.kframework.kore


class RichDefinition(val koreDefinition: kore.Definition) {


}

object RichDefinition {
  def apply(koreDefinition: kore.Definition): RichDefinition = new RichDefinition(koreDefinition)
}

class RichModule(val koreModule: kore.Module, val imports: Seq[kore.Module]) {

}

object RichModule {
  def apply(koreModule: kore.Module, imports: Seq[kore.Module]): RichModule = new RichModule(koreModule, imports)
}




