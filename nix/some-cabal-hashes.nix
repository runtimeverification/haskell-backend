# Source: https://github.com/lf-/nix-lib/blob/main/lib/some-cabal-hashes.nix
#
# License: MIT License Copyright (c) 2023 Jade Lovelace
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is furnished
# to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice (including the next
# paragraph) shall be included in all copies or substantial portions of the
# Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
# OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
# WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
# OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

# Problem: `callCabal2nix` and `callHackage` by extension make poor usage of
# import-from-derivation, which badly serializes builds on the C++ Nix
# implementation if large numbers of import-from-derivation derivations have to
# be built.
#
# Solution: Generate one derivation that depends on all the cabal2nix executions.
# This is over an order of magnitude faster, since it only imports one
# derivation and can build in parallel.
#
# Usage:
# sourceOverrideHaskellOverlay = import ./some-cabal-hashes.nix {
#   overrides = {
#     vector = "0.12.3.1";
#     pipes = self.fetchFromGitHub {
#       owner = "gabriella439";
#       repo = "haskell-pipes-library";
#       # https://github.com/gabriella439/haskell-pipes-library/tree/main
#       rev = "3997b02a5e226b5ba2eba347cb34616bdf76b596";
#       sha256 = "sha256-9CN59Im0BC3vSVhL85v5eXPYYoPbV3NAuv893tXpr/U=";
#     };
#   };
#   inherit self;
# };
{ overrides, self }:
hself: hsuper:
let
  inherit (self.lib) filterAttrs concatMapStrings composeExtensions;
  inherit (self) lib;
  compose = self.haskell.lib.compose;

  archiveMembers = fetchedPackages:
    self.writeTextFile {
      name = "archive-members";
      text = ''
        ${concatMapStrings ({
            name,
            version,
            ...
          }: ''
            ${name}/${version}/${name}.json
            ${name}/${version}/${name}.cabal
          '')
          fetchedPackages}
      '';
    };

  # this is taken from the linkFarm sources in nixpkgs; it's the same but it
  # copies instead of linking. This is because IFD does not like imports of
  # symlinks.
  copyFarm = name: entries:
    self.runCommandNoCC name { }
      ''
        mkdir -p $out
        cd $out
        ${lib.concatMapStrings (x: ''
          mkdir -p "$(dirname ${lib.escapeShellArg x.name})"
          cp ${lib.escapeShellArg "${x.path}"} ${lib.escapeShellArg x.name}
        '')
        entries}
      '';

  oneNixExpr = some-cabal-hashes: name: src:
    let
      build =
        # Specifying a path or a derivation (due to toString coercion) as the
        # version of a thing will cabal2nix it with a path.
        if isPath src then hself.haskellSrc2nix { inherit name src; }
        # Otherwise, it will extract the hash from some-cabal-hashes and
        # cabal2nix it via hackage with a known hash.
        else rawHackage2nix some-cabal-hashes name src;
    in
    {
      name = "${name}/default.nix";
      path = "${build}/default.nix";
    };

  # This is one derivation that can be cached, containing all the cabal2nix
  # output.
  cabal2nixPackages = some-cabal-hashes: items:
    copyFarm "some-cabal2nixes" (map (name: oneNixExpr some-cabal-hashes name items.${name})
      (builtins.attrNames items));

  # adapted from https://github.com/nixos/nixpkgs/blob/d27e6f2d052214b21cbbbe2efc6ab46615ae3ee5/pkgs/development/haskell-modules/make-package-set.nix#L139-L143
  #
  # this is pretty horrifying, but: gnu tar has terrible perf on --wildcards
  # (10s vs 1s) and github gives us an archive with a leading component.
  # There seems to be no way to remove leading components PRIOR to matching
  # file names. So we have to bake it into the filenames.
  #
  # this is intentionally *not* runCommandLocal to get caching on the One Set
  # Of Cabal Files, to avoid having to grab the all-cabal-hashes archive if the
  # Cabal files have already been built on a caching machine.
  buildCabalHashes = items:
    self.runCommand "some-cabal-hashes" { } ''
      mkdir -p $out
      leadingComponent="$(tar -tzf "${self.all-cabal-hashes}" | head -n1 || true)"
      awk -v comp="$leadingComponent" '{if ($0) print comp $0}' ${archiveMembers items} > files
      tar --strip-components 1 --files-from=./files -xzf ${self.all-cabal-hashes} --one-top-level="$out"
    '';

  # This is largely copied from
  # https://github.com/nixos/nixpkgs/blob/d27e6f2d052214b21cbbbe2efc6ab46615ae3ee5/pkgs/development/haskell-modules/make-package-set.nix#L145-L149
  #
  # It replaces hackage2nix to use some-cabal-hashes
  rawHackage2nix = some-cabal-hashes: name: version:
    let
      component = "${some-cabal-hashes}/${name}/${version}";
    in
    hself.haskellSrc2nix {
      name = "${name}-${version}";
      sha256 = ''$(${self.jq}/bin/jq -r '.["package-hashes"].SHA256' "${component}/${name}.json")'';
      src = "${component}/${name}.cabal";
    };

  # Replaces the stock hackage2nix with one which fetches from one big
  # derivation that Nix can build in parallel and also supports non-Hackage
  # sources.
  #
  # Every package will depend on the same derivation so there is only one
  # import-from-derivation call.
  package2nix = some-cabal2nixes: name: src:
    let
      # XXX: Nix doesn't know how to deal with import-from-derivation
      # putting a path into a file: it's considered an "absolute path" and
      # rejected in pure evaluation mode.
      #
      # So we have to rehydrate the "src" attribute to be a derivation once it
      # comes off disk. This doesn't matter on hackage packages, since those
      # don't put store paths in their src attribute.
      #
      # This is immediately obvious to the most casual observer and is
      # Definitely(tm) completely reasonable.
      modifier =
        if isPath src then compose.overrideCabal (p: { inherit src; })
        else p: p;
    in
    args: modifier (hself.callPackage (some-cabal2nixes + "/${name}") args);

  isPath = x: builtins.substring 0 1 (toString x) == "/";
  toExtract = set: builtins.filter ({ name, version }: !(isPath version))
    (
      (builtins.map (name: { name = name; version = set.${name}; })
        (builtins.attrNames set))
    );

  extracted = buildCabalHashes (toExtract overrides);
  cabal2nixed = cabal2nixPackages extracted overrides;
in
(builtins.mapAttrs (name: src: package2nix cabal2nixed name src { }) overrides)
  //
{
  # debugging info :)
  some-cabal-hashes = {
    toExtract = toExtract overrides;
    inherit extracted;
    inherit cabal2nixed;
  };
}