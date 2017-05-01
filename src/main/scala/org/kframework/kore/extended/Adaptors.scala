package org.kframework.kore.extended

import org.kframework.kore



object Adaptors {

  implicit def asRichDefinition(d: kore.Definition): RichDefinition = RichDefinition(d)

  implicit def asRichModule(m: kore.Module)(implicit d: kore.Definition): RichModule = {

    val importDecs = m.sentences.collect({
      case kore.Import(n, _) => n
    })

    val relevantImports = d.modules.filter(x => importDecs.contains(x.name))

    RichModule(m, relevantImports)
  }
}

