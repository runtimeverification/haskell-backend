package org.kframework.kore.extended

import org.kframework.kore
// Each Construct only has the minimal information required to derive everything.

object implicits {

  implicit class RichDefinition(val koreDefinition: kore.Definition) {
    lazy val modulesMap: Map[kore.ModuleName, kore.Module] = koreDefinition.modules.groupBy(_.name).mapValues(_.head)
  }

  implicit class RichModule(val koreModule: kore.Module)(implicit val d: kore.Definition) {

    lazy val imports: Seq[kore.Module] = koreModule.sentences.collect({
      case kore.Import(m, _) => d.modulesMap(m)
    })

    lazy val localSentences = koreModule.sentences

    lazy val allSentences: Seq[kore.Sentence] = localSentences ++ importedSentences

    lazy val importedSentences: Seq[kore.Sentence] = imports.flatMap(_.allSentences)

    lazy val sorts: Seq[kore.Sort] = allSentences.collect({
      case kore.SymbolDeclaration(s, _, _, _) => s
      case kore.SortDeclaration(s, _) => s
    })

  }

  implicit class RichAttributes(val attributes: kore.Attributes) {

    def findSymbol(symbol: kore.Symbol): Option[kore.Pattern] = {
      attributes.patterns.collect({
        case p@kore.Application(`symbol`, _) => Some(p)
        case _ => None
      }).head
    }
  }

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


