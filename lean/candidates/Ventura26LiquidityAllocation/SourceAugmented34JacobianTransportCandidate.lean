import Ventura26LiquidityAllocation.SourceAugmented34TwoRowRescaleCandidate

/-!
# Conditional rank transport for the SOURCE augmented 34 Jacobian

This theorem consumes an EXPLICIT equality between the original
economic directional Jacobian and its two-row log-normalized version.
It does not assume the desired invertibility: it proves a biconditional.

The semantic derivative equality is a separate obligation. In
particular, its row-21 premise must be derived from the actual
SOURCE common-pledge log ratio, while the row-5 scale is positive
1 / Gamma_L at a binding root. An abstract biconditional cannot
establish economic regularity or existence of a SOURCE root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

/-- A genuine 34-output derivative identity, once independently
proved, transports bijectivity through the two collateral rows. -/
theorem source34EconomicJacobian_bijective_iff_of_two_rows
    {E : Type*}
    (Joriginal Jnormalized : E → (Fin 33 → ℝ) × ℝ)
    (GammaL V2 : ℝ)
    (hGamma : GammaL ≠ 0) (hV : V2 ≠ 0)
    (hderiv : ∀ d : E,
      Jnormalized d =
        source34TwoRowRescale GammaL⁻¹ V2⁻¹ (Joriginal d)) :
    Function.Bijective Jnormalized ↔ Function.Bijective Joriginal := by
  have h5 : GammaL⁻¹ ≠ 0 := inv_ne_zero hGamma
  have h21 : V2⁻¹ ≠ 0 := inv_ne_zero hV
  have hfunctions :
      Jnormalized =
        (fun d => source34TwoRowRescale GammaL⁻¹ V2⁻¹
          (Joriginal d)) := funext hderiv
  rw [hfunctions]
  exact source34TwoRowRescale_comp_bijective_iff
    Joriginal GammaL⁻¹ V2⁻¹ h5 h21

#print axioms source34EconomicJacobian_bijective_iff_of_two_rows

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
