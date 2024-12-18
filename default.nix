let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  inherit (lock.nodes.flake-compat.locked) rev narHash;
  compat = fetchTarball {
    url = "https://github.com/edolstra/flake-compat/archive/${rev}.tar.gz";
    sha256 = narHash;
  };
in
(import compat { src = ./.; }).defaultNix
