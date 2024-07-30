# Tests for `kore-rpc-booster` handling `?`-variables correctly

When rewriting with a rule that introduces a fresh variable (aka `?`-variable, aka "existential") on the right-hand side, we need to be careful not to capture existing variables in the configuration. While Kore does it right, Booster used to be less careful. These tests are here to make sure the two agree.

The `../resourses/questionmark-vars.k` semantics is used, which consists of two simple state
transition rules that unconditionally introduce a fresh variable in the configuration. While the two rules use the same name, `?X`, we need to make sure the backends always introduce a fresh one.

1) _one-ques_

   Rewrites with one rule, introducing a single `?`-variable into `<a-state>` cell.

   _Input:_

```
   <k> #setAStateSymbolic </k>
   <a-state> .State       </a-state>
   <b-state> .State       </b-state>
```

   _Expected:_

```
   <k> .K                 </k>
   <a-state> ?X           </a-state>
   <b-state> .State       </b-state>
```

2) _two-ques-internal_

   Rewrites with two rules, introducing two distinctly-named variables

   _Input:_

```
   <k> #setAStateSymbolic ~> #setBStateSymbolic </k>
   <a-state> .State       </a-state>
   <b-state> .State       </b-state>
```

   _Expected:_

```
   <k> .K                 </k>
   <a-state> ?X           </a-state>
   <b-state> ?X0          </b-state>
```

3) _two-ques-external_

   Starting from the final state of _one-ques_, rewrite with one rule, introducing a variable with a fresh name, arriving at the final state of _two-ques-internal_.

   _Input:_

```
   <k> #setBStateSymbolic </k>
   <a-state> ?X           </a-state>
   <b-state> .State       </b-state>
```

   _Expected:_

```
   <k> .K                 </k>
   <a-state> ?X           </a-state>
   <b-state> ?X0          </b-state>
```

4) _two-ques-internal_

   Both variables already have counters, and the first one is rewritten twice. The responses for `kore-rpc-booster` and `kore-rpc-dev` diverge, highlighting the difference in variable freshening mechanisms in Booster and Kore.

   _Input:_

```
   <k> #setAStateSymbolic ~> #setAStateSymbolic </k>
   <a-state> ?X0           </a-state>
   <b-state> ?X1       </b-state>
```

   _Expected kore-rpc-booster:_

```
   <k> .K                 </k>
   <a-state> ?X0           </a-state>
   <b-state> ?X1          </b-state>
```

   _Expected kore-rpc-dev:_

```
   <k> .K                 </k>
   <a-state> ?X2          </a-state>
   <b-state> ?X1          </b-state>
```

5) _ques-and-substitution_

   If a substitution `X ==K b` is supplied, it will be applied before rewriting.
   However, the variable `X` can still not be used because the substitution will also be returned in the result (for information).
   Therefore, the newly created variable cannot be `X0`.

   _Input:_

```
   <k> #setAStateSymbolic </k>
   <a-state> ?X0      </a-state>
   <b-state> ?X       </b-state>
    #And
   ?X ==K b #And ?X0 ==K ?X1 #And ?X2 ==K ?X3 // substitutions
```

   _Expected:_

```
   <k> .K                 </k>
   <a-state> ?X0          </a-state>
   <b-state> b            </b-state>
    #And
   ?X ==K b #And ?X0 ==K ?X1 #And ?X2 ==K ?X3 // substitutions
    #And 
   condition(?X3)
```
