package org.kframework.minikore.interfaces

/**
  * Created by lpena on 3/23/17.
  */
object outer {

  import org.kframework.minikore.interfaces.{pattern => p}

  type Attributes = Seq[p.Pattern]

  trait HasAttributes {
    val att: Attributes

    def onAttributes(f: p.Pattern => p.Pattern): HasAttributes

    // Derived operations
    def getBySymbol(key: p.Symbol): Seq[Seq[p.Pattern]] = att collect { case p.Application(`key`, args) => args }

    def onAttributeBySymbol(key: p.Symbol)(f: p.Pattern => p.Pattern): HasAttributes = onAttributes {
      case app@p.Application(`key`, _) => f(app)
      case pattern                     => pattern
    }

    def updateAttribute(key: p.Symbol, value: p.Pattern*): HasAttributes = onAttributeBySymbol(key) {
      case a@p.Application(`key`, _) => a.build(key, value)
    }
  }

  trait Definition extends HasAttributes {
    val modules: Seq[Module]

    // Derived operations
    val sorts: Set[p.Sort] = modules flatMap (_.sorts) toSet
    val symbols: Set[p.Symbol] = modules flatMap (_.symbols) toSet
    val sentences: Seq[Sentence] = modules flatMap (_.sentences)

    override def onAttributes(f: p.Pattern => p.Pattern): Definition
  }

  trait Module extends HasAttributes {
    val name: p.Name
    val sentences: Seq[Sentence]

    // Derived operations
    val sorts: Set[p.Sort] = sentences flatMap (_.sorts) toSet
    val symbols: Set[p.Symbol] = sentences flatMap (_.symbols) toSet

    override def onAttributes(f: p.Pattern => p.Pattern): Module
  }

  trait Sentence extends HasAttributes {
    val sorts: Set[p.Sort] = Set.empty
    val symbols: Set[p.Symbol] = Set.empty

    override def onAttributes(f: p.Pattern => p.Pattern): Sentence
  }

//  val sorts: Definition => Set[p.Sort] = d => d.modules flatMap sorts toSet
//  val sorts: Module => Set[p.Sort] = m => m.sentences flatMap sorts toSet
//  val sorts: Sentence => Set[p.Sort] = {
//    case SortDeclaration(sort, _) => Set(sort)
//    case SymbolDeclaration(sort, _, _, _) => Set(sort)
//    case _ => Set.empty
//  }

}
