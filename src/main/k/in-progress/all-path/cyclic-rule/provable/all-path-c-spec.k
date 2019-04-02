// Everything is provable if I can reach a cycling rule
module ALL-PATH-C-SPEC
  import PATH
  rule 
    <k> a => c </k>
  [claim, all-path]
endmodule
