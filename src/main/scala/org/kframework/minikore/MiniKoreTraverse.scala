package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

object MiniKoreTraverse {

  def size(p: i.Pattern): Int = p match {
    case p:i.Leaf => 1
    case p:i.Node[i.Pattern] => p.children.map(size).sum
  }

  def iter(f: i.Pattern => Unit)(p: i.Pattern): Unit = p match {
    case p:i.Leaf => f(p)
    case p:i.Node[i.Pattern] => p.children.foreach(iter(f))
  }

  def map(f: i.Pattern => i.Pattern)(p: i.Pattern): i.Pattern = p match {
    case p:i.Leaf => f(p)
    case p:i.Node[i.Pattern] => p.build(p.data, p.children.map(map(f)))
  }

  def fold
      (c: i.Constructor)
      (fp: i.Pattern => i.Pattern, fv: i.Variable => i.Variable,
       fn: String => String, fs: String => String, fl: String => String, fval: String => String)
      (p: i.Pattern): i.Pattern = {
    def loop(p: i.Pattern): i.Pattern = fold(c)(fp,fv,fn,fs,fl,fval)(p)
    p match {
      case p:i.Variable    => fv(c.Variable(fn(p.name), fs(p.sort)))
      case p:i.Application => fp(c.Application(fl(p.label), p.args.map(loop)))
      case p:i.DomainValue => fp(c.DomainValue(fl(p.label), fval(p.value)))
      case p:i.True        => fp(c.True())
      case p:i.False       => fp(c.False())
      case p:i.And         => fp(c.And(loop(p.p), loop(p.q)))
      case p:i.Or          => fp(c.Or(loop(p.p), loop(p.q)))
      case p:i.Not         => fp(c.Not(loop(p.p)))
      case p:i.Implies     => fp(c.Implies(loop(p.p), loop(p.q)))
      case p:i.Exists      => fp(c.Exists(fv(p.v), loop(p.p)))
      case p:i.ForAll      => fp(c.ForAll(fv(p.v), loop(p.p)))
      case p:i.Next        => fp(c.Next(loop(p.p)))
      case p:i.Rewrite     => fp(c.Rewrite(loop(p.p), loop(p.q)))
      case p:i.Equal       => fp(c.Equal(loop(p.p), loop(p.q)))
    }
  }

  def subst(m: Map[i.Variable, i.Pattern])(p: i.Pattern): i.Pattern = {
    def fresh(x: i.Variable): i.Variable = {
      x.constructor(x.name + "!new!", x.sort) // TODO: make it really fresh
    }
    p match {
      case v:i.Variable => if (m.contains(v)) m(v) else p
      case p:i.MLV[_] =>
        val x = fresh(p.v)
        p.constructor(x, subst(m + (p.v -> x))(p.p))
      case p:i.Node[i.Pattern] =>
        p.build(p.data, p.children.map(subst(m)))
      case _:i.Leaf => p
    }
  }

}
