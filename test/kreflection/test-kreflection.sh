${KRUN:?} ${KRUN_OPTS:?} 1.kreflection 2>&1 \
    | sed -e 's,(.*/definition.kore .*),(path removed),'
