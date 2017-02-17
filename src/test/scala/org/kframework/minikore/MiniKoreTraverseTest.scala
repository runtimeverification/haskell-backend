package org.kframework.minikore

import org.junit.Test
import org.kframework.minikore.PatternInterface.{DomainValue, Pattern}
import org.kframework.minikore.TreeInterface.{Leaf, Node}
import org.kframework.minikore.{Builders => c}

class MiniKoreTraverseTest {

//  @Test def testSize(): Unit = {
//    val x1 = MiniKore.Variable("x!new!", "K")
//    val e1 = MiniKore.Exists(x1, x1)
//    assert(MiniKoreTraverse.size(e1) == 2)
//  }
//
//  @Test def testMapIdentity(): Unit = {
//    val p = MiniKore.And(MiniKore.True(), MiniKore.False())
//
//    def identity: Pattern => Pattern = { (p) =>
//      p match {
//        case p: Leaf[Pattern] => p
//        case p: Node[Pattern] => p.construct(p.children)
//        case p: NodeApply[Pattern] => p.construct(p.label, p.children)
//      }
//    }
//
//    assert(MiniKoreTraverse.map(identity)(p) == p)
//  }

}
