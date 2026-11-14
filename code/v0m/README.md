# V0-M internal verification

Run `python code/verify.py` from the repository root after installing
`code/requirements.txt`. The entry point retains the static laboratory,
then runs six V0-M checks in dependency order. No external datasets are read.

| Check | Evidence | Limitation |
|---|---|---|
| `sampled_checks.py` | Exact rational funding/support checks and sampled allocation identities | Finite samples, not a universal proof |
| `verified_linear_operator.py` | Directed 80-digit Decimal enclosures, graph defects and inverse bounds | Conditional on the specified equations and implementation |
| `verified_nonlinear_radius.py` | Curvature, contraction budgets and financial margins | Conservative local sufficient radius |
| `audit_selector_tree.py` | Finite checks of the common selector argument | Complements the written tree proof |
| `audit_regime_bounds.py` | Euler barriers and deposit-corner margins | Local regime information |
| `finite_bridge.py` | Boundary root, 33 residuals, two Jacobians and four instrument derivatives | Local comparisons with common inherited states and announcements |

The folders retain dates to identify stages of the calculation. Earlier
diagnostics do not substitute for later certificates. The `.npz` inputs contain
matrix guesses used to propose preconditioners whose defects are enclosed
afterwards. They contain no data about people, firms or banks. The
`hand_linearization.py` input is only the coefficient stencil: its AST is
evaluated with exact-decimal interval parameters. It does not import an
exploratory solver or require SciPy.

`verification_report.json` records the manuscript, input, script and artifact
hashes and actual outcome. Certificate JSONs are retained as review evidence.
Re-execution may change timestamps and last digits of numerical preconditioners
across NumPy/LAPACK versions; the inequalities must still pass. A stale
manuscript ledger or a failed inequality stops the run.

The ledger inventories all 57 numbered statements and hashes their written
proofs. This source check and the certificates do not establish Lean coverage or
independently prove every analytical argument. This step does not execute Lean or produce IRFs. The separate `../irf/`
step now produces internal IRFs; no empirical calibration or external validation
is claimed.
