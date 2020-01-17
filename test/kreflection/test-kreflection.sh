${KRUN:?} ${KRUN_OPTS:?} 1.kreflection 2>&1 || true \
    | sed -e 's,(.*/definition.kore .*),(path removed),'
