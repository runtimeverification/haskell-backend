out=test-kreflection.sh.out
${KRUN:?} ${KRUN_OPTS:?} 1.kreflection >$out.tmp 2>&1 || true
grep 'Error .* found KREFLECTION\.isConcrete hook' $out.tmp \
    | sed -e 's,([^()]*/definition.kore [^()]*),(...),' >$out \
    || true
rm $out.tmp
