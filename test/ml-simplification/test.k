module TEST
    imports INT
    imports BOOL

    rule {I +Int J #Equals I +Int K} => #Bottom
        requires notBool J ==Int K [simplification]

    syntax Test ::= runTest( K ) | doneTest( K )

    rule <k> runTest( X ) => doneTest ( X ) ... </k>

endmodule

// TODO: remove, just tracking the kore output here
//
// // rule #Equals{Int,#SortParam}(`_+Int_`(I,J),`_+Int_`(I,K))=>#Bottom{#SortParam}(.KList) requires `notBool_`(`_==Int_`(J,K)) ensures #token("true","Bool") [UNIQUE_ID(53328a2399f7fc79acf1a79872e887e6a049fe2dc6f9de5085a72d2925eccf5d), org.kframework.attributes.Location(Location(5,10,6,35)), org.kframework.attributes.Source(Source(/Users/anapantilie/RV/kore/test/ml-simplification/test.k)), org.kframework.definition.Production(syntax #RuleContent ::= #RuleBody "requires" Bool [klabel(#ruleRequires), symbol]), simplification, sortParams({Q0})]
//   axiom{R,Q0} \implies{R} (
//     \equals{SortBool{},R}(
//         LblnotBool'Unds'{}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarJ:SortInt{},VarK:SortInt{})),
//         \dv{SortBool{}}("true")),
//     \equals{Q0,R} (
//       \equals{SortInt{}, Q0}(Lbl'UndsPlus'Int'Unds'{}(VarI:SortInt{},VarJ:SortInt{}),Lbl'UndsPlus'Int'Unds'{}(VarI:SortInt{},VarK:SortInt{})),
//      \and{Q0} (
//        \bottom{Q0}(),
//         \top{Q0}())))
//   [sortParams{}("{Q0}"), org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(/Users/anapantilie/RV/kore/test/ml-simplification/test.k)"), org'Stop'kframework'Stop'definition'Stop'Production{}("syntax #RuleContent ::= #RuleBody \"requires\" Bool [klabel(#ruleRequires), symbol]"), org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(5,10,6,35)"), simplification{}(""), UNIQUE'Unds'ID{}("53328a2399f7fc79acf1a79872e887e6a049fe2dc6f9de5085a72d2925eccf5d")]
