import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# Literal normalized funding dual of firm L under sigmaE = 1

The illustrative Python bridge uses the intertemporal marginal
valuation betaE * consumption0L / consumption1L. The original
EconomicModel.lean defines CRRA marginal utility c^(-sigmaE).
This module proves their exact correspondence ONLY at sigmaE=1,
with strictly positive original source consumption levels.

This is one equation of the 34-dimensional economic source.
It does not assert equality of the other 33 Python/Lean rows,
a validated parameter instance, an IFT witness, or equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarDualSigmaOneBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The source CRRA marginal reduces to the reciprocal exactly
at unit entrepreneurial risk aversion, including as a real power. -/
theorem crraMarginal_sigma_one (c : ℝ) :
    crraMarginal 1 c = c⁻¹ := by
  simp [crraMarginal, Real.rpow_neg_one]

/-- The source ratio of marginal utilities equals the consumption
growth ratio in the numerical bridge under unit CRRA curvature.
Positive consumptions discharge every division condition. -/
theorem source_crra_ratio_sigma_one
    (c0 c1 : ℝ) (hc0 : 0 < c0) (hc1 : 0 < c1) :
    crraMarginal 1 c1 / crraMarginal 1 c0 = c0 / c1 := by
  rw [crraMarginal_sigma_one, crraMarginal_sigma_one]
  have hn0 : c0 ≠ 0 := ne_of_gt hc0
  have hn1 : c1 ≠ 0 := ne_of_gt hc1
  field_simp [hn0, hn1]

/-- The literal normalized L source dual agrees algebraically with
the betaE*C0/C1 structure of the illustrative Python evaluator,
conditional on unit entrepreneur risk aversion and positive source
consumptions. The source retains the ORIGINAL loan rate and inflation. -/
theorem source_normalized_L_dual_sigma_one
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc0 : 0 < Z.controlsZero.consumptionL)
    (hc1 : 0 < Z.controlsOne.consumptionL) :
    localNormalizedCollateralDualL P Z =
      1 / Z.controlsZero.loanRate -
      (P.entrepreneurDiscount *
        (Z.controlsZero.consumptionL / Z.controlsOne.consumptionL)) /
        Z.controlsOne.inflation := by
  unfold localNormalizedCollateralDualL
  rw [hsigma]
  rw [mul_div_assoc, source_crra_ratio_sigma_one _ _ hc0 hc1]

#print axioms crraMarginal_sigma_one
#print axioms source_crra_ratio_sigma_one
#print axioms source_normalized_L_dual_sigma_one

end ProposedLocalScalarDualSigmaOneBridge
end Ventura26LiquidityAllocation
