module KORE-COMMON

  imports STRING-SYNTAX

  syntax Name // defined in KORE-SYNTAX

  syntax Sort ::= Name | Name "{" Sorts "}"

  syntax Sorts ::= List{Sort, ","}

  syntax Symbol ::= Name "{" Sorts "}"

  syntax Variable ::= Name ":" Sort

  // Copied from domains.k
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]

  syntax Pattern ::= Variable
                   | String
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
                   | "\\next" "{" Sort "}" "(" Pattern ")"
                   | "\\rewrites" "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\dv" "{" Sort "}" "(" Pattern ")"

  syntax Patterns ::= List{Pattern, ","}
  
  syntax Attribute ::= "[" Patterns "]"
  
  syntax Declaration ::=
    "import" Name Attribute
  | "sort" Name "{" Names "}" Attribute
  | "hook-sort" Name "{" Names "}" Attribute
  | "symbol" Name "{" Names "}" "(" Sorts ")" ":" Sort Attribute
  | "hook-symbol" Name "{" Names "}" "(" Sorts ")" ":" Sort Attribute
  | "axiom" "{" Names "}" Pattern Attribute
  
  syntax Names ::= List{Name, ","}

  syntax Declarations ::= List{Declaration, ""}
  
  syntax Module ::= "module" Name Declarations "endmodule" Attribute
  
  syntax Modules ::= List{Module, ""}
  
  syntax Definition ::= Attribute Modules

endmodule

module KORE-SYNTAX

  imports KORE-COMMON

  // TODO:: Fix this regexp.
  syntax Name ::= r"[-#a-zA-Z0-9]*"     [autoReject, token, prec(2)]

endmodule


module KORE

  imports KORE-COMMON  // don't import KORE-SYNTAX
  
  configuration <T> <k> $PGM:Definition </k> </T>

endmodule
