set -eux

SCRIPT_DIR=$(dirname $0)
PLUGIN_DIR=${PLUGIN_DIR:-""}

if [ -z "$PLUGIN_DIR" ]; then
    echo "PLUGIN_DIR required to link in a crypto plugin dependency"
    exit 1
else
    for lib in libff libcryptopp blake2; do
        LIBFILE=$(find ${PLUGIN_DIR} -name "${lib}.a" | head -1)
        [ -z "$LIBFILE" ] && (echo "[Error] Unable to locate ${lib}.a"; exit 1)
        PLUGIN_LIBS+="$LIBFILE "
        PLUGIN_INCLUDE+="-I$(dirname $LIBFILE) -I$(dirname $LIBFILE)/../include "
    done
    #PLUGIN_CPP=$(find ${PLUGIN_DIR}/plugin-c -name "*.cpp")
    PLUGIN_CPP="${PLUGIN_DIR}/include/plugin-c/crypto.cpp ${PLUGIN_DIR}/include/plugin-c/plugin_util.cpp"
fi


NAME=$(basename ${0%.kompile})
NAMETGZ=$(basename ${0%.kompile})


# Regenerate llvm backend decision tree
mkdir -p ./dt
llvm-kompile-matching ${NAME}.llvm.kore qbaL ./dt 0

# kompile llvm-definition to interpreter

case "$OSTYPE" in
  linux*)   LPROCPS="-lprocps" ;;
  *)        LPROCPS="" ;;
esac

llvm-kompile ${NAME}.llvm.kore ./dt c -- \
             -fPIC -std=c++20 -o interpreter \
             $PLUGIN_LIBS $PLUGIN_INCLUDE $PLUGIN_CPP \
             -lcrypto -lssl $LPROCPS -lsecp256k1
mv interpreter.* ${NAME}.dylib

# remove temporary artefacts
rm -r dt

# provide haskell definition
cp ${NAME}.haskell.kore ${NAME}.kore
