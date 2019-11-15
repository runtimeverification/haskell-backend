// Everything is provable if I can reach a cycling rule
module ALL-PATH-B-SPEC
  import PATH
  rule 
    <k> a => b </k>
  [claim, all-path]
endmodule
