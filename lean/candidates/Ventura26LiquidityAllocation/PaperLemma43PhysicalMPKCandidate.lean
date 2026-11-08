import Ventura26LiquidityAllocation.PaperSourceLogCapitalRatioCandidate

/-!
# Lemma 4.3: physical marginal product of capital (MPK), not only Y/k

Two bridges:
  (1) differentiate the ORIGINAL firm Cobb-Douglas production
      F(k,ell) = A*k^a*ell^b with respect to physical k>0;
  (2) identify the derivative with a*F(k,ell)/k.

The prior source share equivalence uses per-firm Y/k. This makes
precise why it is an ordering of *physical marginal products* when
the two firms share strictly positive capital elasticity a.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperLemma43PhysicalMPK

theorem original_firm_production_hasDerivAt_capital
    (A k ell a b : ℝ)
    (hk : 0 < k) :
    HasDerivAt (fun x : ℝ => A * x ^ a * ell ^ b)
      (a * (A * k ^ (a - 1) * ell ^ b)) k := by
  have hr : HasDerivAt (fun x : ℝ => x ^ a)
      (a * k ^ (a - 1)) k :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))
  have h := (hr.const_mul A).mul_const (ell ^ b)
  convert h using 1 <;> ring

theorem original_firm_mpk_equals_elasticity_times_output_per_capital
    (A k ell a b : ℝ) (hk : 0 < k) :
    a * (A * k ^ a * ell ^ b / k) =
      a * (A * k ^ (a - 1) * ell ^ b) := by
  have hpow : k ^ (a - 1) = k ^ a / k := by
    rw [Real.rpow_sub hk a 1]
    simp
  rw [hpow]
  field_simp [ne_of_gt hk] <;> ring

#print axioms original_firm_production_hasDerivAt_capital
#print axioms original_firm_mpk_equals_elasticity_times_output_per_capital

end ProposedPaperLemma43PhysicalMPK
end Ventura26LiquidityAllocation
