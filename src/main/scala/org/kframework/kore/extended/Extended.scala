package org.kframework.kore.extended

import org.kframework.kore

// Each Construct only has the minimal information required to derive everything.

class RichDefinition(val koreDefinition: kore.Definition) {
}

object RichDefinition {
  def apply(koreDefinition: kore.Definition): RichDefinition = new RichDefinition(koreDefinition)
}

class RichModule(val koreModule: kore.Module, val imports: Seq[RichModule]) {

  val sentences: Seq[kore.Sentence] = koreModule.sentences

  lazy val allSentences: Seq[kore.Sentence] = sentences ++ importedSentences

  lazy val importedSentences: Seq[kore.Sentence] = imports.flatMap(_.allSentences)

  lazy val sorts: Seq[kore.Sort]  = allSentences.collect({
    case kore.SymbolDeclaration(s, _, _, _) => s
    case kore.SortDeclaration(s, _) => s
  })

}

object RichModule {
  def apply(koreModule: kore.Module, imports: Seq[RichModule]): RichModule = new RichModule(koreModule, imports)
}

//Rewriter may need a module to begin with. Still a WIP.
//Needs a definition and a Module to start with.
trait Rewriter {
  def step(p: kore.Pattern, steps: Int=1): kore.Pattern
}

//Backend provides access to the definition (after its conversion) and it's set of Builders
trait Backend extends kore.Definition with kore.Builders


//Way to Create a backend give a Kore Definition. Since Backends need the entire definition to
//Function, they can only provide Builders once they've processed the definition
trait BackendCreator extends (kore.Definition => Backend)



