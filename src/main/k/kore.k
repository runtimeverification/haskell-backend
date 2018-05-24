module KORE-SYNTAX

  imports DOMAINS-SYNTAX

  syntax Sort ::= Id "{" Sorts "}"

  syntax Sorts ::= List{Sort, ","}

  syntax Symbol ::= Id "{" Sorts "}"

  syntax Variable ::= Id ":" Sort

  syntax Pattern ::= Variable
                   | Symbol "(" Patterns ")"
                   | "\\and" "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\not" "{" Sort "}" "(" Pattern ")"
                   | "\\or"  "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\implies"  "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\iff"  "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\forall" "{" Sort "}" "(" Variable "," Pattern ")"
                   | "\\exists" "{" Sort "}" "(" Variable "," Pattern ")"
                   | "\\ceil" "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\floor" "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\equals"  "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\in" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\top" "{" Sort "}" "(" ")"
                   | "\\bottom" "{" Sort "}" "(" ")"
                   | "\\dv" "{" Sort "}" "(" Pattern ")"

  syntax Patterns ::= List{Pattern, ","}
  
  syntax Attribute ::= "[" Patterns "]"
  
  syntax Declaration ::=
    "import" Id Attribute
  | "sort" Id "{" Ids "}" Attribute
  | "symbol" Id "{" Ids "}" "(" Sorts ")" ":" Sort Attribute
  | "axiom" "{" Ids "}" Pattern Attribute
  
  syntax Ids ::= List{Id, ","}
  
  syntax Declarations ::= List{Declaration, ""}
  
  syntax Module ::= "module" Id Declarations "endmodule" Attribute
  
  syntax Modules ::= List{Module, ""}
  
  syntax Definition ::= Attribute Modules

endmodule


module KORE

  import KORE-SYNTAX
  
  configuration <T>
                  <k> $PGM:Definition </k>
                </T>

endmodule
