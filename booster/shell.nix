{ ghc ? "default" }:
(builtins.getFlake ("git+file://" + toString ./.)).devShells.${builtins.currentSystem}.${ghc}
