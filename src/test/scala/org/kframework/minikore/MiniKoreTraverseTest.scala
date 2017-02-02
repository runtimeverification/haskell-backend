package org.kframework.minikore

import org.junit.Assert.assertEquals
import org.junit.Test
import org.kframework.minikore.{MiniKoreInterface => i}

class MiniKoreTraverseTest {

  @Test def test(): Unit = {
    val p = MiniKore.True()
    val v = MiniKore.False()
    val x = MiniKore.Variable("x", "K")
    val e = MiniKore.Exists(x, x)
    val x1 = MiniKore.Variable("x!new!", "K")
    val e1 = MiniKore.Exists(x1, x1)
    val m = Map(x.asInstanceOf[i.Variable] -> v)
    assertEquals(MiniKoreTraverse.subst(m)(p), p)
    assertEquals(MiniKoreTraverse.subst(m)(x), v)
    assertEquals(MiniKoreTraverse.subst(m)(e), e1)
  }

  @Test def test2(): Unit = {
    val p = MiniKore.And(MiniKore.True(), MiniKore.False())
    val c = MiniKore
    assertEquals(MiniKoreTraverse.fold(c)(x => x, x => x, x => x, x => x, x => x, x => x)(p), p)
  }

}
