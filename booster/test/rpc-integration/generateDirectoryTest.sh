#!/usr/bin/env bash

tar=${1?"Please provide a tar file in a single argument"}

NAME=$(basename ${1%.tar.gz})

mkdir -p test-$NAME

tar xzf $tar -C test-$NAME definition.kore llvm_definition/definition.kore

mv test-$NAME/definition.kore resources/$NAME.haskell.kore
mv test-$NAME/llvm_definition/definition.kore resources/$NAME.llvm.kore
rm -r test-$NAME/llvm_definition


cat <<"TAGTEXTFILE" > resources/$NAME.kompile
set -eux

SCRIPT_DIR=$(dirname $0)
PLUGIN_DIR=${PLUGIN_DIR:-""}


if [ -z "$PLUGIN_DIR" ]; then
    echo "PLUGIN_DIR required to link in a crypto plugin dependency"
    exit 1
else
    for lib in libff libcryptopp libsecp256k1; do
        LIBFILE=$(find ${PLUGIN_DIR} -name "${lib}.a" | head -1)
        [ -z "$LIBFILE" ] && (echo "[Error] Unable to locate ${lib}.a"; exit 1)
        PLUGIN_LIBS+="$LIBFILE "
        PLUGIN_INCLUDE+="-I$(dirname $LIBFILE)/../include "
    done
    #PLUGIN_CPP=$(find ${PLUGIN_DIR}/plugin-c -name "*.cpp")
    PLUGIN_CPP="${PLUGIN_DIR}/include/plugin-c/blake2.cpp ${PLUGIN_DIR}/include/plugin-c/crypto.cpp ${PLUGIN_DIR}/include/plugin-c/plugin_util.cpp"
fi

NAME=$(basename ${0%.tar.gz.kompile})
NAMETGZ=$(basename ${0%.kompile})


# provide haskell definition
TAGTEXTFILE

cat >>resources/$NAME.kompile <<EOL
cp $NAME.haskell.kore $NAME.kore

# Regenerate llvm backend decision tree
llvm-backend-matching $NAME.llvm.kore qbaL ./dt 0

# kompile llvm-definition to interpreter

EOL

cat <<"TAGTEXTFILE" >> resources/$NAME.kompile
case "$OSTYPE" in
  linux*)   LPROCPS="-lprocps" ;;
  *)        LPROCPS="" ;;
esac

TAGTEXTFILE

cat >>resources/$NAME.kompile <<EOL
llvm-kompile $NAME.llvm.kore ./dt c -- \\
EOL

cat <<"TAGTEXTFILE" >> resources/$NAME.kompile
             -fPIC -std=c++17 -o interpreter \
             $PLUGIN_LIBS $PLUGIN_INCLUDE $PLUGIN_CPP \
             -lcrypto -lssl $LPROCPS

TAGTEXTFILE

cat >>resources/$NAME.kompile <<EOL
mv interpreter.* $NAME.dylib

# remove temporary artefacts
rm -r dt
EOL

tar xzf $tar -C test-$NAME --wildcards "rpc_*/*.json"
cd test-$NAME

mv rpc_*/*.json .
rm -r rpc_*/
rename -f 's/(\d+)_request.json/state-$1.send/s' *_request.json
rename -f 's/(\d+)_response.json/response-$1.json/s' *_response.json