let
  default = import ../default.nix { };
  fourmolu = import ./fourmolu.nix { };
  inherit (default) pkgs;
  inherit (pkgs) fd;
  inherit (pkgs) lib mkShell stdenv glibcLocales;

in mkShell {
  LOCALE_ARCHIVE = lib.optionalString (stdenv.hostPlatform.libc == "glibc")
    "${glibcLocales}/lib/locale/locale-archive";
  buildInputs = [ fourmolu fd ];
}
