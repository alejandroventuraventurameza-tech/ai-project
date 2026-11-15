import Ventura26LiquidityAllocation.SourcePythonOffRootLogResidualReparameterizationCandidate
import Ventura26LiquidityAllocation.SourceSixLogRowJacobianRankTransportCandidate
import Ventura26LiquidityAllocation.SourceFullyPinnedStationaryP0OperatorCandidate

/-!
# Exact SIX nonlinear SOURCE residual normalizations preserve ALL 33 zeros

The ORIGINAL SOURCE non-firm rows bank/labor and deposit Euler are
LEVEL or 1-minus-ratio residuals. The original Python equations are
LOG ratios, not literally the same functions. Their exact off-root
normalizations are log(1+source/B) and log(1-source), respectively.

This module constructs ONE 33-output nonlinear map using those SIX
transformations at zero-based positions 6,9,10,22,25,26, leaving
the other 27 coordinates untouched. If all positive log domains and
bank/labor normalization targets are supplied, the transformed vector
is zero IF AND ONLY IF the original vector is identically zero.
This is the exact full-vector algebraic zero-set firewall needed
before any SOURCE/Python 33-equation correspondence claim.

The targets are allowed to depend on the economic coordinates.
Consequently this is NOT a globally constant diagonal rescaling,
and does not prove the other 27 original Python expressions equal
SOURCE, nor identify the calibration or a true root.
-/

namespace Ventura26LiquidityAllocation

/-- Positive-denominator SOURCE level difference v has the same
zero as log(1+v/B), provided the log argument is positive. -/
theorem sourceLogOnePlusLevel_zero_iff
    (v B : ℝ) (hB : 0 < B) (harg : 0 < 1 + v / B) :
    Real.log (1 + v / B) = 0 ↔ v = 0 := by
  constructor
  · intro h
    have heq : 1 + v / B = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero harg h
    have hz : v / B = 0 := by linarith
    have hBne : B ≠ 0 := ne_of_gt hB
    calc
      v = (v / B) * B := by field_simp [hBne]
      _ = 0 := by rw [hz]; ring
  · intro hv
    rw [hv]
    norm_num

#print axioms sourceLogOnePlusLevel_zero_iff

/-- SOURCE 1-minus-ratio Euler normalization has the same
positive-domain zeros as log(1 - sourceEuler). -/
theorem sourceLogOneMinusEuler_zero_iff
    (v : ℝ) (harg : 0 < 1 - v) :
    Real.log (1 - v) = 0 ↔ v = 0 := by
  constructor
  · intro h
    have heq : 1 - v = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero harg h
    linarith
  · intro hv
    rw [hv]
    norm_num

#print axioms sourceLogOneMinusEuler_zero_iff

/-- The 33-output source vector with ONLY the six literal
bank/labor/Euler SOURCE level rows converted to their exact
off-root Python-shaped log normalizations. Other 27 rows are
left literally unchanged, *not* declared Python-equivalent. -/
noncomputable def sourceSixNonlinearLogRowNormalize
    (bank0 labor0 bank1 labor1 : ℝ)
    (v : Fin 33 → ℝ) (i : Fin 33) : ℝ :=
  if i = 6 then Real.log (1 + v i / bank0)
  else if i = 9 then Real.log (1 + v i / labor0)
  else if i = 10 then Real.log (1 - v i)
  else if i = 22 then Real.log (1 + v i / bank1)
  else if i = 25 then Real.log (1 + v i / labor1)
  else if i = 26 then Real.log (1 - v i)
  else v i

/-- Exact positive log-domain requirements on the six original
SOURCE rows. The four level targets are STRICTLY positive. -/
def SourceSixNonlinearLogDomain
    (bank0 labor0 bank1 labor1 : ℝ) (v : Fin 33 → ℝ) : Prop :=
  0 < bank0 ∧ 0 < labor0 ∧ 0 < bank1 ∧ 0 < labor1 ∧
  0 < 1 + v 6 / bank0 ∧ 0 < 1 + v 9 / labor0 ∧
  0 < 1 - v 10 ∧
  0 < 1 + v 22 / bank1 ∧ 0 < 1 + v 25 / labor1 ∧
  0 < 1 - v 26

/-- Prove equivalence ROWWISE, including all 27 untouched residuals:
normalization of a row vanishes precisely when its SOURCE row does. -/
theorem sourceSixNonlinearLogRow_zero_iff
    (bank0 labor0 bank1 labor1 : ℝ) (v : Fin 33 → ℝ)
    (hd : SourceSixNonlinearLogDomain bank0 labor0 bank1 labor1 v)
    (i : Fin 33) :
    sourceSixNonlinearLogRowNormalize bank0 labor0 bank1 labor1 v i = 0 ↔
      v i = 0 := by
  rcases hd with ⟨hb0, hl0, hb1, hl1, harg6, harg9, harg10,
    harg22, harg25, harg26⟩
  unfold sourceSixNonlinearLogRowNormalize
  split_ifs with h
  · subst i
    exact sourceLogOnePlusLevel_zero_iff (v 6) bank0 hb0 harg6
  · subst i
    exact sourceLogOnePlusLevel_zero_iff (v 9) labor0 hl0 harg9
  · subst i
    exact sourceLogOneMinusEuler_zero_iff (v 10) harg10
  · subst i
    exact sourceLogOnePlusLevel_zero_iff (v 22) bank1 hb1 harg22
  · subst i
    exact sourceLogOnePlusLevel_zero_iff (v 25) labor1 hl1 harg25
  · subst i
    exact sourceLogOneMinusEuler_zero_iff (v 26) harg26
  · rfl

#print axioms sourceSixNonlinearLogRow_zero_iff

/-- Any 33-output SOURCE economic residual has EXACTLY the same
zero set after the six nonlinear logarithmic reparameterizations,
including the fully pinned concrete SOURCE residual. This theorem
DOES NOT assert a root exists. -/
theorem sourceSixNonlinearLogRow_vector_zero_iff
    (bank0 labor0 bank1 labor1 : ℝ) (v : Fin 33 → ℝ)
    (hd : SourceSixNonlinearLogDomain bank0 labor0 bank1 labor1 v) :
    sourceSixNonlinearLogRowNormalize bank0 labor0 bank1 labor1 v = 0 ↔
      v = 0 := by
  constructor
  · intro h
    funext i
    have hi : sourceSixNonlinearLogRowNormalize
      bank0 labor0 bank1 labor1 v i = 0 := by
      simpa using congrFun h i
    exact (sourceSixNonlinearLogRow_zero_iff
      bank0 labor0 bank1 labor1 v hd i).mp hi
  · intro h
    funext i
    have hi : v i = 0 := by simpa using congrFun h i
    exact (sourceSixNonlinearLogRow_zero_iff
      bank0 labor0 bank1 labor1 v hd i).mpr hi

#print axioms sourceSixNonlinearLogRow_vector_zero_iff

/-- Apply the full-vector nonlinear transformation to the ACTUAL
fully pinned economic SOURCE reduced map: this equivalence is about
the same real SOURCE map, with no Python equality assumed. -/
theorem fullyPinnedSOURCE33_sixLogNormalized_root_iff
    (G : ℝ) (w : (Fin 32 → ℝ) × ℝ)
    (bank0 labor0 bank1 labor1 : ℝ)
    (hd : SourceSixNonlinearLogDomain bank0 labor0 bank1 labor1
      (fullyPinnedStationaryP0SOURCE33 G w)) :
    sourceSixNonlinearLogRowNormalize bank0 labor0 bank1 labor1
      (fullyPinnedStationaryP0SOURCE33 G w) = 0 ↔
    fullyPinnedStationaryP0SOURCE33 G w = 0 :=
  sourceSixNonlinearLogRow_vector_zero_iff
    bank0 labor0 bank1 labor1
    (fullyPinnedStationaryP0SOURCE33 G w) hd

#print axioms fullyPinnedSOURCE33_sixLogNormalized_root_iff

end Ventura26LiquidityAllocation
