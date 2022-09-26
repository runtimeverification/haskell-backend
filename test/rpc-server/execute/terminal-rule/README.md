# Stopping at a given terminal-rule

* K model: `a => b | c ` `c => d => e => f` with rules labeled with
  their transition (e.g., label `AB` for `a => b`)
* Start state `c`
* Parameters: `terminal-rules: [ TEST.DE, TEST.AB]`

Expected:
* Execution stops at `3` with `depth: 2`,
* reporting `reason: terminal-rule`.
