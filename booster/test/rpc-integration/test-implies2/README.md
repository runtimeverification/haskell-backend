These tests were collected from pyk integration tests, see: https://github.com/runtimeverification/k/blob/04d55ad993e9afb3d0d57ab8233d674eb4745c77/pyk/src/tests/integration/proof/test_implies_proof.py#L31-L67 :

```python
IMPLIES_PROOF_TEST_DATA: Iterable[tuple[str, tuple[str, ...], tuple[str, ...], bool, ProofStatus]] = (
    (
        'antecedent-bottom',
        ('X <=Int 0', '0 <Int X'),
        ('X <Int 3',),
        True,
        ProofStatus.PASSED,
    ),
    (
        'consequent-top',
        ('X <Int 3',),
        ('X <Int X +Int 1',),
        True,
        ProofStatus.PASSED,
    ),
    (
        'satisfiable-not-valid',
        ('X <Int 3',),
        ('X <Int 2',),
        True,
        ProofStatus.FAILED,
    ),
    (
        'satisfiable-not-valid-true-antecedent',
        (),
        ('X <=Int 0',),
        True,
        ProofStatus.FAILED,
    ),
    (
        'satisfiable-not-valid-existential',
        (),
        ('X <=Int 0',),
        False,
        ProofStatus.PASSED,
    ),
)
111