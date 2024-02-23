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
fi
