set -eux

PLUGIN_DIR=${PLUGIN_DIR?"PLUGIN_DIR required to link in a crypto plugin dependency"}

NAME=$(basename ${0%.kompile})

# provide haskell definition
cp ${NAME}.haskell.kore ${NAME}.kore

# Regenerate llvm backend decision tree
mkdir -p ./dt
llvm-kompile-matching ${NAME}.llvm.kore qbaL ./dt 1/2

# kompile llvm-definition to interpreter

PLUGIN_LIB=${PLUGIN_DIR}/build/krypto/lib/krypto.a

llvm-kompile ${NAME}.llvm.kore ./dt c -- \
             -fPIC -std=c++17 -o interpreter \
             $PLUGIN_LIB -lcrypto -lssl -lsecp256k1 \
             -I /usr/include -I $PLUGIN_DIR

mv interpreter.* ${NAME}.dylib

# remove temporary artefacts
rm -r dt
