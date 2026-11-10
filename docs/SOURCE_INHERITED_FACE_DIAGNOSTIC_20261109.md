# Diagnostic of inherited nominal-face compatibility at the SOURCE boundary

**Evidence class:** `NUMERICO`, not a kernel-checked impossibility proof.
**Original exact object:** `boundarySourceRate`, `boundaryInitialState G boundarySourceRate`, and `boundaryPrimitives G boundarySourceRate`.
**Source version examined:** `d195b1fd271d0da06578df0be49b10cb3686cd07`, branch `work/lean-ci-validation-otc-20261106`.
**Date:** 2026-11-09 (Lima).

## Exact condition in the model

`EconomicModel.lean` defines `InheritedNominalFaceConsistency` as strict positivity of `bankRenewalFactor P` and

```text
I.depositRateLag * I.householdDeposits
  + I.governmentBondRateLag * I.householdBonds
= (sum i, P.mass i * I.firmFace i)
  + (I.governmentBondRateLag * I.householdBonds
     + I.reserveRateLag * I.reservesLag
     - I.facilityRateLag * I.facilityBorrowingLag)
  - I.bankFace / bankRenewalFactor P.
```

The same public-bond term cancels exactly from both sides. Define the **gap** as left minus right:

```text
Delta_Face :=
  I.depositRateLag * I.householdDeposits
  - (sum i, P.mass i * I.firmFace i)
  - I.reserveRateLag * I.reservesLag
  + I.facilityRateLag * I.facilityBorrowingLag
  + I.bankFace / bankRenewalFactor P.
```

`InheritedNominalFaceConsistency P I` requires **Delta_Face = 0**; this constraint is not one of the 33 reduced equations. The `G`-dependent household public-bond position cancels; fixing `G` does not automatically repair it.

## Independently reconstructed numerical evidence

A 70-digit `decimal.Decimal` calculation rebuilding all quantities from named SOURCE formulas (see attached standalone Python reproducer for the full computation, not a Lean proof) gives:

| Quantity | Numerical result |
|---|---:|
| Root `boundarySourceRate` | 1.029135799507732095542150518344234298558 |
| Reduced boundary resource residual | -2.05e-68 |
| Stationary inherited-face gap | +1e-69 |
| SOURCE boundary inherited-face gap | **+0.082914964573431353836551547932934541443** |
| H inherited firm face | 1.676268884794872728995487265 |
| L inherited firm face | 7.486705243234991795333242052 |
| Hypothetical inherited household-deposit correction `-gap/RD_steady` | -0.082085814927697040298186032 |

The computation checks both the certified root bracket `[41/40,129/125]` and the parent stationary identity. The strict sign of the residual is wide relative to floating-point error, but **not yet formally certified** by interval enclosures in Lean. A second independent implementation should also be retained for scientific review.

## Interpretation and immediate restriction

The impact firm faces are chosen by `boundaryInheritedFace` in `BoundaryFirmBridgeCandidate.lean` to close each firm's date-zero budget. The inherited household deposits, reserves and facility borrowing remain those of the stationary predecessor, whereas `boundaryInitialState` also changes the bank face.

This mechanism can yield all firm budget rows equal to zero and a resource root equal to zero while leaving **the initial nominal-face aggregate identity unresolved**. If the nonzero result is exactly certified, `InheritedNominalFaceConsistency` will be false for this unmodified pair `(P,I)`, so the current SOURCE carrier cannot be advertised as a complete `CompetitiveEquilibrium`.

Do **not** silently adjust deposits, taxes, inherited faces or the root to manufacture a zero: such a change modifies the initial-condition / intervention contract and would require a newly declared model, additional endogenous degree of freedom, a fresh 33+/equation system, and independent validation.

## Exact work remaining

1. Establish a rigorous Lean/rational interval enclosure for `Delta_Face` at the named unique root (ideally `0.08 < Delta_Face < 0.09`), without `sorryAx`. This is **PENDIENTE**.
2. Separately audit `BankRenewalFlows`; a common-bank stock identity does not imply its source expected portfolio-return identity.
3. Only after reconciling the initial financial state should `HouseholdBudgetFlows` be attempted via the already available `householdBudgetFlows_withSourceAccountingCompletion_of_source_flows` theorem.
4. Preserve the parent model, policy instruments and definitions, and do not claim an equilibrium existence theorem for this candidate.
