import Ventura26LiquidityAllocation.DateZeroOneSidedPrimalGapCandidate
import Ventura26LiquidityAllocation.ScalarKKTMultiplierConstructionCandidate

/-!
# One-sided source optimality provides a scalar collateral Euler-row witness

The source FirmOptimal and a locally feasible *right* capital deviation imply
that the deterministic date-zero primal Euler gap is nonnegative. For a
strictly positive collateral coefficient, a scalar nonnegative multiplier
then closes the same capital Euler residual row in a dual-replaced carrier.

This is ONE scalar equation at the root, not a proof that the SOURCE dual
field equals the constructed scalar, or that the altered Allocation is a
CompetitiveEquilibrium. Nor does it prove a complete KKT system.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroScalarKKTFromOptimal

open ProposedDateZeroOneSidedPrimalGap
open ProposedContinuationContractAudit
open ProposedScalarKKTMultiplierConstruction
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The strictly positive collateral coefficient converts the source-derived
    one-sided Euler gap into a nonnegative scalar solving the capital row. -/
theorem firmOptimal_oneSided_exists_nonnegative_scalarCapitalMultiplier
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ v : S,
      0 < P.tree.transition (currentState h) v →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h v) *
          X.capitalPrice 1 (childHistory h v)))
    (hw0 : P.tree.historyWeight 0 (rootHistory P.tree) = 1)
    (hz0 : ∀ h : History S 0, h ≠ rootHistory P.tree →
      P.tree.historyWeight 0 h = 0)
    (hw1 : P.tree.historyWeight 1
      (childHistory (rootHistory P.tree) s) = 1)
    (hz1 : ∀ h : History S 1,
      h ≠ childHistory (rootHistory P.tree) s →
      P.tree.historyWeight 1 h = 0)
    (hunit : 0 < capitalEulerCollateralUnit P X i 0
      (rootHistory P.tree) s) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      localFirmCapitalEulerResidual P
        (replaceCollateralDual X (fun _ _ _ => mu))
        i 0 (rootHistory P.tree) s = 0 := by
  have hgap : 0 ≤ capitalEulerPrimalGap P X i 0
      (rootHistory P.tree) s :=
    firmOptimal_oneSided_root_primalGap_nonneg P I X i s
      hopt hcapital hcoeff hw0 hz0 hw1 hz1
  obtain ⟨mu, hmu, hrow⟩ :=
    exists_nonnegative_scalar_capitalDual P X i 0 (rootHistory P.tree)
      s hgap hunit
  refine ⟨mu, hmu, ?_⟩
  rw [capitalEulerResidual_eq_primalGap_sub_dual,
      capitalEulerPrimalGap_replaceDual,
      capitalEulerCollateralUnit_replaceDual]
  change capitalEulerPrimalGap P X i 0 (rootHistory P.tree) s -
    mu * capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s = 0
  exact hrow

end ProposedDateZeroScalarKKTFromOptimal
end Ventura26LiquidityAllocation
