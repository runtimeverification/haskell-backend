module LLVM
  imports INT
  imports BYTES
  imports BOOL
  imports MAP
  imports SET
  imports K-EQUAL
  imports MAP-VAL-TO-VAL

  syntax Num ::= Even | Odd
  syntax Even ::= Zero() | Two() | Four() | Six() | Eight() | Ten()
  syntax Odd ::= One() | Three() | Five() | Seven() | Nine()

  syntax Num ::= pred(Num) [function]

  rule pred(One()) => Zero()
  rule pred(Two()) => One()
  rule pred(Three()) => Two()
  rule pred(Four()) => Three()
  rule pred(Five()) => Four()
  rule pred(Six()) => Five()
  rule pred(Seven()) => Six()
  rule pred(Eight()) => Seven()
  rule pred(Nine()) => Eight()
  rule pred(Ten()) => Nine()

  syntax Int ::= eval(Num) [function, total]

  rule eval(Zero()) => 0
  rule eval(SomeNum) => 1 +Int eval(pred(SomeNum))
    requires notBool SomeNum ==K Zero()

  syntax Num ::= div2(Even) [function, total]

  rule div2(Zero()) => Zero()
  rule div2(Two()) => One()
  rule div2(Four()) => Two()
  rule div2(Six()) => Three()
  rule div2(Eight()) => Four()
  rule div2(Ten()) => Five()

endmodule

module MAP-VAL-TO-VAL
  imports WRAPPED-INT

  syntax Val ::= WrappedInt
 // -----------------------

  syntax MapValToVal [hook(MAP.Map)]
  syntax MapValToVal ::= MapValToVal MapValToVal
         [ left, function, hook(MAP.concat), symbol(_MapValToVal_),
           assoc, comm, unit(.MapValToVal), element(_Val2Val|->_)
         ]
  syntax MapValToVal ::= ".MapValToVal"
         [function, total, hook(MAP.unit),symbol(.MapValToVal)]
  syntax MapValToVal ::= Val "Val2Val|->" Val
         [function, total, hook(MAP.element), symbol(_Val2Val|->_)]

  syntax MapValToVal ::= MapValToVal "[" key: Val "<-" value: Val "]"
         [function, total, symbol(MapVal2Val:update), hook(MAP.update), prefer]

  syntax priority _Val2Val|->_ > _MapValToVal_ .MapValToVal
  syntax non-assoc _Val2Val|->_

  syntax MapValToVal ::= MapValToVal "{{" key: Val "<-" value: Val "}}"
         [ function, total, symbol(MapValToVal:primitiveUpdate), prefer]
  rule M:MapValToVal {{ Key:Val <- Value:Val }}
      => M[Key <- Value]

endmodule

module WRAPPED-INT
  imports INT

  syntax WrappedInt ::= wrap(Int)  [symbol(wrapInt)]
  // -------------------------------------------------------

  syntax Int ::= unwrap(WrappedInt)
         [function, total, injective, symbol(unwrapInt)]
  // ---------------------------------------------------------------------------------------
  rule unwrap(wrap(A:Int)) => A
endmodule
