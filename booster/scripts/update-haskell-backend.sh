set -euxo pipefail

# update the backend to a specific commit in the flake (if $1 is unset, will default to current master)
nix flake lock --override-input haskell-backend github:runtimeverification/haskell-backend/${1-}
# obtain the full rev hash
REV=$(cat flake.lock| jq '.nodes."haskell-backend".locked.rev' -r)
# We need to check if the old rev has remained unchanged
OLD_REV=$(cat cabal.project | grep -oPz 'haskell-backend.git\s+tag:\s+\K.+')
if [ $REV != $OLD_REV ]; then
  # Set the commit hash inside stack.yaml and cabal.project
  sed -i -r "/haskell-backend.git/{n;s/commit:.*$/commit: $REV/}" stack.yaml
  sed -i -r "/haskell-backend.git/{n;s/tag:.*$/tag: $REV/}" cabal.project
  # Update the stack.yaml.lock file by running a stack command that accesses dependencies
  stack ls dependencies --test > /dev/null
  # freeze cabal dependencies
  $(dirname $0)/freeze-cabal-to-stack-resolver.sh
  # since we use cabal.project as source of truth for nix builds, we need to provide
  # a valid --sha256 hash for the haskell-backend library
  # the easiest way to do this is to simply run nix, let it fail and substitute the
  # correct sha back into cabal.project
  SHA=$(nix build 2>&1 | grep -oP 'got:\s+\K.+') || true
  sed -i -r "/haskell-backend.git/{n;s/tag:.*$/tag: $REV/;n;s|--sha256:.*$|--sha256: $SHA|}" cabal.project
fi
