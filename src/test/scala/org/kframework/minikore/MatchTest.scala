package org.kframework.minikore

import org.junit.Test

class MatchTest {
  @Test def matchTest1(): Unit = {

    val text = "[] module A import B [] endmodule []"

    val impo = MyConstructor.import1("B", Seq())

    val impo2 = MyConstructor.import1("C", Seq())

    val module = NewKore.Module("A", Seq(impo, impo2), Seq())

    module.sentences collect {
      case NewKore.Import(x:String, _) => x
    } map println

    assert(true)
  }

}
