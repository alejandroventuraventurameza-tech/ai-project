# Reconstruction protocol: freeze the inherited balance sheet before a date-zero monetary intervention

**Status:** research plan and source-code audit, not a proof of competitive equilibrium.
**Applicable evidence:** working branch `work/lean-ci-validation-otc-20261106`; exact 70-digit inherited-face detector at commit `96cc51aeb76434fdaff4659e975f4686fbc9db03`.
**Date:** 2026-11-09, America/Lima.

## 1. The economic difficulty

`BoundaryFullPrefixCandidate.lean` defines

```lean
boundaryInitialState G R :=
  { inheritedState G with
    capital := boundaryCapital R
    firmFace := boundaryInheritedFace G R (boundaryZeroSeed G R)
    bankFace := boundaryBankEquity R
    ... }
```

Thus inherited capital, inherited nominal entrepreneurial faces, and the
bank's inherited face are all changed when the proposed boundary loan rate
`R` is changed. In a date-zero *unanticipated* monetary intervention,
these are inherited **predetermined** positions, not newly selected
impact controls. This is a logical difference between a static root
construction and a valid impulse-response experiment.

The exact source condition `InheritedNominalFaceConsistency P I` requires

```text
R_D,-1 D^W_-1 - Σ_i μ_i F^i_-1
- R_R,-1 M^post_-1 + R_F,-1 F^facility_-1
+ F^B_-1 / a_B = 0.
```

The 33 reduced rows do not include this initial accounting condition.
A numerical high-precision diagnostic finds a nonzero gap ≈ +0.082915
for the SOURCE root with its constructed `boundaryInitialState`.
This is **NUMERICO**, not yet an exact Lean nonzero theorem. The root's
resource equation does not rectify inherited nominal debts.

## 2. A well-posed repair must keep the reference inherited state fixed

Define the baseline inherited state `I₀ := inheritedState G`, whose
`InheritedNominalFaceConsistency (primitives G) I₀` is already proved
by `ProposedStationaryInheritedState.inherited_nominalFaceConsistency G`.

For a date-zero surprise policy vector `v` and primitives `P(v)`, keep
`I(v) := I₀` and solve endogenous impact controls and continuation
jointly. If `v` modifies only policy innovations, the initial
inherited-face accounting identity ought to transport definitionally;
this last transport is a separate Lean target.

Formulate the actual finite prefix with the *same* `I₀` across the
counterfactuals:

```text
F_branch(Z ; P(v), I₀, continuation) = 0,
I₀ fixed, v = (reserve-rate innovation, reserve quantity,
                reserve requirement, corridor width).
```

Do **not** reuse the existing unique root `boundarySourceRate` as a
certificate for this different fixed-inheritance system. In particular,
the previous date-zero firm budget rows must be solved with the frozen
`I₀.firmFace i`; changing those faces to satisfy the rows is circular.

The intervention's reserve-remuneration shock and the encaje ratio
remain distinct. If adding a compatibility equation when inheritance
is left free, expose an additional endogenous variable and count
equations and unknowns honestly. When inheritance is correctly fixed
at baseline, compatibility is an initial-data admissibility condition,
not an independently adjustable endogenous equation.

## 3. Formal research gates

1. **Exact obstruction for the old carrier:** prove a rational interval
   enclosure of `sourceBoundaryInheritedNominalFaceGap G` near its
   **SOURCE** root (about 1.0291357995, not the parent bank loan rate
   1.012048236...). The original wide root bracket contains both
   signs of the nominal gap, so it is not a sufficient interval.
2. **Frozen initial-state carrier:** transport the existing stationary
   inherited nominal-face proof to intervention primitives, preserving
   all inherited stocks/faces. Show fixed inheritance literally.
3. **New reduced-to-literal prefix:** solve impact firm budgets, bank
   stocks, policy rules, resource market and OTC for that frozen
   inheritance, with exactly the announced policy shocks.
4. **Infinite continuation:** prove supported-history feasibility,
   private optimality, bank population Bellman problem, inherited
   renewal and non-Ponzi/TVC conditions rather than assuming
   them in the tail constructor.
5. **Economic claims:** only once a genuine equilibrium path and
   counterfactual exist may the paper attribute investment
   reallocation, IRF signs and long-run growth to policy.

A successful numerical gap detector is evidence of a suspected
inconsistency, not a computationally verified CE. The paper, slides and
figure captions must preserve that difference. `main` stays unchanged,
and PR #2 remains a draft until proof gates are met.
