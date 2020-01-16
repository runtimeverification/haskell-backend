KREFLECTION_KORE_EXEC_OPTS="--disable-log-timestamps"
KREFLECTION_KRUN_OPTS="--haskell-backend-command \"$KORE_EXEC $KREFLECTION_KORE_EXEC_OPTS\""
COMMAND="$KRUN $KREFLECTION_KRUN_OPTS -d . 1.kreflection 2>test-kreflection.sh.out || true"
#KOMPILE="$TOP/.build/k/bin/kompile kreflection.k --backend haskell"
#eval $KOMPILE
eval $COMMAND
sed -i "s,(.*/kreflection/.*),(path removed)," test-kreflection.sh.out