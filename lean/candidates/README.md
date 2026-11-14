# Isolated Lean candidate validation

- Parent project: alejandroventuraventurameza-tech/ai-project
- Immutable source commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86
- Review branch: work/lean-ci-validation-20261105 (never merge automatically)
- AppliedModelingLib base: 194edcc95df74806a39b961d10dedddc6e730cce
- Lean toolchain: leanprover/lean4:v4.30.0-rc2
- Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Every *Candidate.lean here is uncompiled draft proof code until CI proves otherwise. The GitHub Action reconstructs the exact upstream checkout, overlays the frozen source modules from lean/checkpoint/modules, and compiles each candidate explicitly in topological dependency order, without invoking the entire upstream default build. A successful compile is not in itself an axiom audit: the workflow also prints axioms for selected headline claims and rejects sorryAx.

The checkpoint's ProofInterface.lean includes admitted endpoints. It is intentionally not used as evidence of closure, nor is the module root's compilation used as proof of the candidate claims. The workflow does not modify upstream, the pinned checkpoint, main, or work/chat-continuity.

If the workflow fails, open the Action run and download lean-candidate-audit-logs. Check the earliest failing module from results.txt (or EconomicModel.log / mathlib-cache.log if bootstrap fails). Remaining modules have not been verified until their builds complete.
