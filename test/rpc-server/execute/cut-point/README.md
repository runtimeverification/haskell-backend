# Stopping at a cut-point rule

* K model: `a => b | c ` `c => d => e => f` with rules labeled with
  their transition (e.g., label `AB` for `a => b`)
* Start state `c`
* Parameters: `cut-point-rules: [ TEST.DE, TEST.AB]`

Expected:
* Execution stops at `d` with `depth: 1`,
* reporting `reason: cut-point-rule` with `rule: TEST.DE` and
  `next-states: [ e ]`
