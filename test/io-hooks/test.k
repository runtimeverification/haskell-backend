module TEST
  imports STRING
  imports INT
  imports K-IO

  syntax IOString ::= readFileAux(IOInt) | readFile(String) [function, impure]

  rule readFileAux(#ENOENT) => "File not found"
  rule readFileAux(FD:Int) =>
    #let TXT = #read(FD, 10) #in
    #let _ = #close(FD) #in TXT

  rule readFile(F) => readFileAux(#open(F))
endmodule
