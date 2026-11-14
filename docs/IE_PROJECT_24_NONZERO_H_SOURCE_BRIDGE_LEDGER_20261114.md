# IE project 24 — nonzero-h SOURCE bridge: evidence ledger and next hard gate

Snapshot date: 2026-11-14. Branch:
`work/lean-ci-validation-source-33-row-20261114`.
NO merge to main. All claims must retain their exact source SHA.

## A. DEMOSTRADO in Lean (pinned successful jobs)

Each module below compiled in the indicated pinned Lean Actions job.
The theorems are conditional exactly on their written economic hypotheses;
a successful module does NOT establish an actual equilibrium root.

| Module and object | Pinned source SHA | Lean Actions |
| --- | --- | --- |
| `SourceBinding33NonzeroRemunerationCandidate`: 33 SOURCE row identity at arbitrary h, zero-set and row-5 rank equivalence | `92c492ed415fde181b6d426101789bf6e54ef7c8` | [#43588299136](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43588299136), success |
| `SourceAugmented34NonzeroRemunerationBoundaryCandidate`: 34 SOURCE boundary root iff original 33 binding rows at Pv(h) plus nu_L=0, and conditional L complementarity | `6e053421bdb2c7fc29da90b591b10e7fd39915bc` | [#43588359054](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43588359054), success |
| `SourceBinding33NonzeroPolicyLogRow5Candidate`: exact log(face_L/Gamma_L)=log(1-S_L), zero set and fixed-coordinate h invariance | `36b0cb97e67e45159156bc5d901821011bfd130f` | [#43588463838](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43588463838), success |
| `SourcePython33RowIndexPermutationCandidate`: exact bijection, inverse, and zero-preserving row reindexing with 6 nonidentity moves | `a898d9841033ee237daffcd8889e0986aa8dda57` | [#43588552593](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43588552593), success |

New precise row-order contract, from SOURCE row index to Python residual index:

`1->3, 2->1, 3->4, 4->2, 18->19, 19->18`; the remaining 27 positions are fixed.

The project also has prior source-typed Schur row-equivalence,
zero-policy row-5 scaling and a conditional actual 34-block rank
theorem. None prove the invertibility of the *economic* SOURCE Jacobian.

## B. New exact SOURCE objects SUBMITTED — compilation pending

The following are CANDIDATES until their individual Lean Actions run
completes successfully and their relevant dependencies/axioms are checked.

1. `SourceAugmented34CanonicalLogBoundaryCandidate.lean`, commit
   `7cd8a83ca8b8068e26ab06f6592d9181884ed104`.
   Defines 34 genuine SOURCE equations with row-5 log face/pledge
   instead of normalized slack; proves identical zero sets at ANY h
   on the positive face/pledge chart.
   [Lean #43589767500](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43589767500).
2. `SourceAugmented34CanonicalLogFrechetCandidate.lean`, commit
   `9a30011505c8eba6b6c569a65397470d70df6960`.
   Attempts source Fréchet calculation
   `D_z log(face_L/Gamma_L)=(1/Gamma_L)D_z R_L`
   at a true SOURCE binding root, including arbitrary h.
   [Lean #43589847750](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43589847750).
3. `SourceAugmented34PythonOrderSourceCanonicalCandidate.lean`, commit
   `480573ab00bfd3b811a8f4bf51d4d7581be19e70`.
   Defines the canonical 34 SOURCE equations in the PYTHON
   **OUTPUT ROW ORDER** and attempts exact zero-set equivalence.
   [Lean #43589881010](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43589881010).
4. `SourceLogLinearContinuationRuleCandidate.lean`, commit
   `4e7acf0fe3f545e2b8fe4ada13d3865367c7f7ae`.
   Defines an arbitrary 10x6 log-linear finite continuation
   `LocalPrefixStateSix -> LocalPrefixControlsTen` in genuine
   SOURCE economic types, and attempts to prove its baseline and
   exact log response. This is a SURROGATE, not a verified
   infinite-horizon equilibrium policy.
   [Lean #43590009760](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43590009760).

## C. NUMERICO / EXACT RATIONAL FOR SURROGATE MATRICES

- Frozen Python boundary, unchanged inherited nominal promises:
  `h*=0.007616947889328002`,
  `max abs 34-residual=8.767064851866735e-11`.
- Floating AD Schur: `-4.212023217372646`.
- Exact-rational Neumann test on DECIMAL-ROUNDED Python AD
  matrix: q34 approximately `2.8881849479728e-10`.
  The exact-rational Schur bracket is approximately
  `[-4.212023236694934,-4.212023198052517]`.
- The earlier 'raw residual = 32' report was a coding bug:
  iteration over dictionary keys rather than residual values.
  Correct raw maximum `3.681499549657019e-13`;
  Python regression successfully repeated in [build #43588606780](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43588606780).
- Existing independent source-shaped-to-Python row transport at the
  frontier reproduces the Python AD Jacobian within `4.2561794089124305e-09`.
  Its SOURCE-shaped formulas are still PYTHON transcriptions.

The P0 file `code/irf/inputs/rational_preconditioners.json`
contains 16x6 decimal strings: first 6 rows are an exact 6x6
identity; last 10 rows are the numerical finite tail control
response matrix. Python `decode_prefix` uses `P0[6:16]`
for date-two controls. Its new structural audit
`audit_source_python_p0_tail_structure.py` was added to
`code/verify.py` and upload-artifact, run from commit
`68dd4f47448cd3000309403b5587a2f7f5a9ac58`:
[build #43590089450](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43590089450).
The pinned [build #43590089450](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43590089450) completed **SUCCESS** at the cited code SHA. The audit logged the exact-rational 6x6 identity and the following NUMERICAL Python results: maximum source-state log-chart error `1.0585878961605344e-16`, maximum ten-control log-response error `1.0007186052041206e-16`, and baseline controls error `0.0`. The report explicitly records `p0_full_equilibrium_continuation_proved=false`.

IMPORTANT: exact decimal P0 strings and Python float64 numbers
do not have identical real-number semantics. The correct long-run
contract is to prove equality of a real-arithmetic lifting of the
algorithm to genuine SOURCE formulas, then separately enclose
binary float rounding errors. Do NOT claim a formal exact
equality between arbitrary real SOURCE functions and hardware floats.

## D. The next decisive scientific obligations

1. Validate the four new Lean candidates at their pinned SHAs,
   record the target declarations' axiom dependencies and correct
   specific failures before advancing the theorem ledger.
2. Instantiate the ten-by-six P0 control matrix and reference
   levels in SOURCE real arithmetic, while explicitly recognizing
   that a finite P0 rule has NOT been shown to be a true infinite
   equilibrium continuation.
3. Complete the **32 remaining row-level real-arithmetic SOURCE
   to Python-formula contracts**, including parameter mapping,
   the canonical log row, Euler shears, policy timing and exact
   inherited states. Numeric matching of equations/indices
   alone is insufficient.
4. Produce directed derivative intervals for the transformed
   genuine SOURCE 34x34 matrix. The previously computed
   conditional entrywise perturbation margin of approximately
   `7.957357478e-05` is only a numerical target.
5. Prove existence of a genuine SOURCE root inside the economic
   box (e.g. a validated Newton/Krawczyk argument), not merely
   nonsingularity of a surrogate Jacobian.
6. Prove full continuation, household/firm/bank KKT, equilibrium
   and then separate monetary-tool IRFs and long-run effects.

At the switch boundary S_L=0 and nu_L=0 simultaneously, ordinary
STRICT complementarity fails. Any cross-regime differentiability
or smooth growth inference requires separate justification.
