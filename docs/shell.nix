# > pdflatex $output
# > pdflatex $output
# > bibtex $output
# > pdflatex $output
let
  sources = import ../nix/sources.nix;
  pkgs = import sources."nixpkgs" {};
  inherit (pkgs) mkShell stdenv;
  inherit (pkgs) bibutils texlive;
in
mkShell {
  buildInputs = [
    (texlive.combine {
      inherit (texlive)
        scheme-full
        collection-mathscience
        collection-publishers
        ;
    })
    bibutils
  ];
}
