package org.kframework.kore.extended

import org.kframework.kore

// Each Construct only has the minimal information required to derive everything.

class RichDefinition(val koreDefinition: kore.Definition) {
}

object RichDefinition {
  def apply(koreDefinition: kore.Definition): RichDefinition = new RichDefinition(koreDefinition)

}

class RichModule(val koreModule: kore.Module, val imports: Seq[RichModule]) {

  lazy val allSentences: Seq[kore.Sentence] = koreModule.sentences ++ importedSentences

  lazy val importedSentences: Seq[kore.Sentence] = imports.flatMap(_.allSentences)

}

object RichModule {
  def apply(koreModule: kore.Module, imports: Seq[RichModule]): RichModule = new RichModule(koreModule, imports)
}




