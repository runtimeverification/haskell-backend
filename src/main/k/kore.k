// Copyright (c) 2018 K Team. All Rights Reserved.
module KORE-SYNTAX
  // imports STRING

  syntax Module ::= Attribute "module" ModuleName Declarations "endmodule" Attribute

  // Lexicals form p49
  
  syntax Identifier ::= ObjectIdentifier
                      | MetaIdentifier

  syntax ObjectIdentifier ::= ObjectNonSlashIdentifier
                            | ObjectSlashIdentifier

  syntax ObjectNonSlashIdentifier ::= r"[A-Za-z][-A-Za-z0-9_']*" [prec(1), notInRules, token, autoReject] 
  syntax ObjectSlashIdentifier ::= r"\\[A-Za-z][-A-Za-z0-9_']*"  [prec(1), notInRules, token, autoReject]

 
  /**
  syntax MetaIdentifier ::= r"#[A-Za-z][A-Za-z0-9_'-]*"    [prec(1), notInRules, token, autoReject]
                          | r"#\\[A-Za-z][A-Za-z0-9_'-]*"  [prec(1), notInRules, token, autoReject]
                          | r"#`[A-Za-z][A-Za-z0-9_'-]*"   [prec(1), notInRules, token, autoReject]
  **/
  // the above doesn't work. I have to use the following, which accepts more things
  syntax MetaIdentifier ::= r"#.?[A-Za-z][A-Za-z0-9_'-]*"    [prec(1), notInRules, token, autoReject]

  // Lexicals from p50

  syntax Sort ::= ObjectSort
                | MetaSort

  syntax ObjectSort ::= ObjectSortVariable
                      | ObjectNonVariableSort

  syntax ObjectSortVariable ::= ObjectIdentifier

  syntax ObjectNonVariableSort ::= ObjectSortConstructor "{" ObjectSortList "}"

  syntax ObjectSortConstructor ::= ObjectIdentifier

  syntax ObjectSortList ::=
       ObjectSort
     | ObjectSort "," ObjectSortList
     | ""

  syntax MetaSort ::= MetaSortVariable
                      | MetaNonVariableSort

  syntax MetaSortVariable ::= MetaIdentifier

  syntax MetaNonVariableSort ::= MetaSortConstructor "{" "}"

  syntax MetaSortConstructor ::=
       "#Char" | "#CharList" | "#String" | "#Sort" | "#SortList"
     | "#Symbol" | "#SymbolList" | "#Variable" | "#VariableList" | "#Pattern" | "#PatternList"

  syntax MetaSortList ::=
       MetaSort
     | MetaSort "," MetaSortList
     | ""

  // Heads and Patterns

  syntax Head ::= ObjectHead
                | MetaHead

  syntax ObjectHead ::= ObjectHeadConstructor "{" ObjectSortList "}"

  syntax ObjectHeadConstructor ::= ObjectIdentifier

  syntax MetaHead ::= MetaHeadConstructor "{" MetaSortList "}"

  syntax MetaHeadConstructor ::= MetaIdentifier

  syntax Pattern ::= ObjectPattern
                   | MetaPattern

  syntax Variable ::= ObjectVariable
                    | MetaVariable

  syntax ObjectPattern ::= ObjectVariable
                         | ObjectHead "(" PatternList ")"
                         | "\\and" "{" ObjectSort "}" "(" Pattern "," Pattern ")"
                         | "\\not" "{" ObjectSort "}" "(" Pattern ")"
                         | "\\or" "{" ObjectSort "}" "(" Pattern "," Pattern ")"
                         | "\\implies" "{" ObjectSort "}" "(" Pattern "," Pattern ")"
                         | "\\iff" "{" ObjectSort "}" "(" Pattern "," Pattern ")"
                         | "\\forall" "{" ObjectSort "}" "(" ObjectVariable "," Pattern ")"
                         | "\\exists" "{" ObjectSort "}" "(" ObjectVariable "," Pattern ")"
                         | "\\ceil" "{" ObjectSort "," ObjectSort "}" "(" Pattern ")"
                         | "\\floor" "{" ObjectSort "," ObjectSort "}" "(" Pattern ")"
                         | "\\equals" "{" ObjectSort "," ObjectSort "}" "(" Pattern "," Pattern ")"
                         | "\\in" "{" ObjectSort "," ObjectSort "}" "(" Pattern "," Pattern ")"
                         | "\\top" "{" ObjectSort "}" "(" ")"
                         | "\\bottom" "{" ObjectSort "}" "(" ")"
                         | "\\dv" "{" ObjectSort "}" "(" MetaPattern ")"
                         | "\\next" "{" ObjectSort "}" "(" Pattern ")"
                         | "\\rewrites" "{" ObjectSort "}" "(" Pattern "," Pattern ")"

  syntax ObjectVariable ::= ObjectIdentifier ":" ObjectSort

  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]

  syntax MetaPattern ::= MetaVariable
                         | String
                         | r"'.'"
                         | MetaHead "(" PatternList ")"
                         | "\\and" "{" MetaSort "}" "(" Pattern "," Pattern ")"
                         | "\\not" "{" MetaSort "}" "(" Pattern ")"
                         | "\\or" "{" MetaSort "}" "(" Pattern "," Pattern ")"
                         | "\\implies" "{" MetaSort "}" "(" Pattern "," Pattern ")"
                         | "\\iff" "{" MetaSort "}" "(" Pattern "," Pattern ")"
                         | "\\forall" "{" MetaSort "}" "(" MetaVariable "," Pattern ")"
                         | "\\exists" "{" MetaSort "}" "(" MetaVariable "," Pattern ")"
                         | "\\ceil" "{" MetaSort "," MetaSort "}" "(" Pattern ")"
                         | "\\floor" "{" MetaSort "," MetaSort "}" "(" Pattern ")"
                         | "\\equals" "{" MetaSort "," MetaSort "}" "(" Pattern "," Pattern ")"
                         | "\\in" "{" MetaSort "," MetaSort "}" "(" Pattern "," Pattern ")"
                         | "\\top" "{" MetaSort "}" "(" ")"
                         | "\\bottom" "{" MetaSort "}" "(" ")"

  syntax MetaVariable ::= MetaIdentifier ":" MetaSort

  syntax PatternList ::= ""
                       | Pattern
                       | Pattern "," PatternList


  syntax Attribute ::= "[" PatternList "]"

  // Modules

  syntax Definition ::= Attribute Modules

  syntax Modules ::= Module | Module Modules

  syntax Module ::= "module" ObjectIdentifier Declarations "endmodule" Attribute

  syntax Declarations ::= Declaration Declarations
  syntax Declarations ::= ""

  syntax Declaration ::= ImportDeclaration
                       | SortDeclaration
                       | SymbolDeclaration
                       | AliasDeclaration
                       | AxiomDeclaration
                       | HookDeclaration

  syntax ImportDeclaration ::= "import" ModuleName Attribute

  syntax SortDeclaration ::= "sort" ObjectSortConstructor "{" ObjectSortVariableList "}" Attribute

  syntax SymbolDeclaration ::= ObjectSymbolDeclaration
                             | MetaSymbolDeclaration

  syntax ObjectSymbolDeclaration ::= "symbol" ObjectHeadConstructor "{" ObjectSortVariableList "}"
                                     "(" ObjectSortList ")" ":" ObjectSort Attribute

  syntax MetaSymbolDeclaration ::= "symbol" MetaHeadConstructor "{" MetaSortVariableList "}"
                                     "(" MetaSortList ")" ":" MetaSort Attribute

  syntax AliasDeclaration ::= ObjectAliasDeclaration | MetaAliasDeclaration

  /**
  syntax ObjectAliasDeclaration ::= "alias" ObjectHeadConstructor "{" ObjectSortVariableList "}"
        "(" ObjectSortList ")" ":" ObjectSort "where"
        ObjectHeadConstructor "{" ObjectSortVariableList "}"
        "(" ObjectVariableList ")" ":=" ObjectPattern Attribute

  syntax MetaAliasDeclaration ::= "alias" MetaHeadConstructor "{" MetaSortVariableList "}"
        "(" MetaSortList ")" ":" MetaSort "where"
        MetaHeadConstructor "{" MetaSortVariableList "}"
        "(" MetaVariableList ")" ":=" MetaPattern Attribute
  **/
  // Update the alias syntax to the above when tests are updated.

  syntax ObjectAliasDeclaration ::= "alias" ObjectHeadConstructor "{" ObjectSortVariableList "}"
                                     "(" ObjectSortList ")" ":" ObjectSort Attribute

  syntax MetaAliasDeclaration ::= "alias" MetaHeadConstructor "{" MetaSortVariableList "}"
                                     "(" MetaSortList ")" ":" MetaSort Attribute

  syntax AxiomDeclaration ::= "axiom" "{" SortVariableList "}" Pattern Attribute

  syntax HookDeclaration ::=
      "hooked-sort" ObjectSortConstructor "{" ObjectSortVariableList "}" Attribute
    | "hooked-symbol" ObjectHeadConstructor "{" ObjectSortVariableList "}" "(" ObjectSortList ")" 
      ":" ObjectSort  Attribute

  syntax SortVariableList ::=
       ObjectSortVariable
     | MetaSortVariable
     | ObjectSortVariable "," SortVariableList
     | MetaSortVariable "," SortVariableList
     | ""

  syntax ObjectSortVariableList ::=
       ObjectSortVariable
     | ObjectSortVariable "," ObjectSortVariableList
     | ""
  
  syntax MetaSortVariableList ::=
       MetaSortVariable
     | MetaSortVariable "," MetaSortVariableList
     | ""

  syntax ModuleName ::= ObjectIdentifier

  // These seem to be missing from the K document.

  syntax ObjectVariableList ::= 
      ObjectVariable
    | ObjectVariable "," ObjectVariableList
    | ""

  syntax MetaVariableList ::= 
      MetaVariable
    | MetaVariable "," MetaVariableList
    | ""

endmodule

module KORE

  imports KORE-SYNTAX

  configuration <k> $PGM:Definition </k>

endmodule
