import Mathlib

/-!
# Proposition 5.1: pinned decimal 6x6 graph and block-decay logic

Source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8,
  paper/body_compact_after.tex (prop:compact_exact_tail_power).
The 36 F0 coefficients below are reconstructed EXACTLY as rationals from
  code/irf/inputs/rational_preconditioners.json
  SHA256 d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94.

The exact rational matrix norm inequalities for F0^48 and all F0^r,
0<=r<48, are kernel-proved with finite rational decision and a separately
proved bridge from rational row sums to the actual real matrix operator norm.
The final theorem prop51_unconditional_exact establishes the full all-k/all-x
decay WITHOUT additional numerical norm hypotheses. The older conditional
theorem is retained as a reusable general algebraic lemma.

These proofs concern the PINNED DECIMAL 6x6 F0; equality to the 34-row
SOURCE equilibrium Jacobian, and nonlinear equilibrium stability, remain OPEN.
-/

open scoped NNReal Matrix Matrix.Norms.Operator

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

/-- Raw decimal literals of the local graph, interpreted as exact rational
values; any E-notation zeros in source are exactly zero in the rationals. -/
def exactDecimalF0Rat : Matrix (Fin 6) (Fin 6) ℚ :=
-- BEGIN EXACT_DECIMAL_F0
  ![
    ![((1007684401252265346095141001581161545920059067858232663 : ℚ) / (10 ^ 54 : ℚ)),
       ((3227130928315780132160088207069023990203014502525375559 : ℚ) / (10 ^ 56 : ℚ)),
       ((6149940649430797709847852884503041335066755427477067423 : ℚ) / (10 ^ 55 : ℚ)),
       ((1529257501068452456375826013220470387299601851769125064 : ℚ) / (10 ^ 55 : ℚ)),
       ((5475120089974215965843641517098575474721893768743396527 : ℚ) / (10 ^ 55 : ℚ)),
       ((-1320300665374014509718300698100319502571372167189312185 : ℚ) / (10 ^ 57 : ℚ))],
    ![((3592455648496423161445101647134086640926911643060260207 : ℚ) / (10 ^ 56 : ℚ)),
       ((1043404974921012197873289816790495471748359212146216357 : ℚ) / (10 ^ 54 : ℚ)),
       ((2736683016453429039680503640667390420866905490208719206 : ℚ) / (10 ^ 55 : ℚ)),
       ((-1900242433114985431058778251123589867677809691716658897 : ℚ) / (10 ^ 55 : ℚ)),
       ((1693635373535299442834831680835279533907035119118269999 : ℚ) / (10 ^ 55 : ℚ)),
       ((-4219405668551132337665469863143903164532878771738381253 : ℚ) / (10 ^ 58 : ℚ))],
    ![((3707242087802211912990619578493607539275017781056128293 : ℚ) / (10 ^ 56 : ℚ)),
       ((7620342503771904732720880029471711797985927015145172070 : ℚ) / (10 ^ 56 : ℚ)),
       ((-6373842986591236915366681223860056297620368090363648564 : ℚ) / (10 ^ 56 : ℚ)),
       ((-7899988309851051473975759350142160595169569194045083567 : ℚ) / (10 ^ 55 : ℚ)),
       ((-5173712205364173231747504752826743655592301757484324662 : ℚ) / (10 ^ 55 : ℚ)),
       ((1227441228356844511373353579088560363584023452776261292 : ℚ) / (10 ^ 57 : ℚ))],
    ![((1461371168521853235787204284670899510511202756222367918 : ℚ) / (10 ^ 56 : ℚ)),
       ((1972991980369983113148645897788682205685769466626531070 : ℚ) / (10 ^ 56 : ℚ)),
       ((1148878446830795106045440099179076091075969596217559869 : ℚ) / (10 ^ 55 : ℚ)),
       ((1140151122329136906526612482110399855381388967255369836 : ℚ) / (10 ^ 54 : ℚ)),
       ((6876292523326395324074168213157367548225362084042177746 : ℚ) / (10 ^ 55 : ℚ)),
       ((-1645325274758818478747246221211703361763237068186004336 : ℚ) / (10 ^ 57 : ℚ))],
    ![((3381521993923859771825849835615140209657706585772933519 : ℚ) / (10 ^ 56 : ℚ)),
       ((5929072747814507674442606577970761914463814345727933377 : ℚ) / (10 ^ 56 : ℚ)),
       ((2555375377315482460771254713499308333713477429692434328 : ℚ) / (10 ^ 55 : ℚ)),
       ((-3063175268399986163118263771962811111928047125751399404 : ℚ) / (10 ^ 55 : ℚ)),
       ((4465623830674757160614550253536998672469122737243726974 : ℚ) / (10 ^ 55 : ℚ)),
       ((1209919634836377171244965567528641128815738504290893474 : ℚ) / (10 ^ 58 : ℚ))],
    ![((0 : ℚ) / (10 ^ 0 : ℚ)),
       ((0 : ℚ) / (10 ^ 0 : ℚ)),
       ((0 : ℚ) / (10 ^ 0 : ℚ)),
       ((0 : ℚ) / (10 ^ 0 : ℚ)),
       ((0 : ℚ) / (10 ^ 0 : ℚ)),
       ((5000000000000000000000000000000000000000000000000000000 : ℚ) / (10 ^ 55 : ℚ))]
  ]
-- END EXACT_DECIMAL_F0

/-- The real local transition graph, obtained via rational-to-real cast.
This is a concrete 6x6 matrix and NOT an identified SOURCE DSGE Jacobian. -/
def exactDecimalF0 : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => (exactDecimalF0Rat i j : ℝ)

/-- Generic decay from finite block and within-block norm bounds.
The infinity norm here is the actual induced matrix row-sum norm and the
usual supremum norm on vectors, not a scalar surrogate. -/
theorem block48_decay_of_norm_bounds
    (F : Matrix (Fin 6) (Fin 6) ℝ)
    (hBlock : ‖F ^ 48‖ < (24 / 25 : ℝ))
    (hTransient : ∀ r : ℕ, r < 48 → ‖F ^ r‖ < (61 / 10 : ℝ))
    (k : ℕ) (x : Fin 6 → ℝ) :
    ‖(F ^ k) *ᵥ x‖ ≤
      (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) * ‖x‖ := by
  let m : ℕ := k / 48
  let r : ℕ := k % 48
  have hr : r < 48 := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hk : k = 48 * m + r := by
    dsimp [m, r]
    omega
  have hPowerIdentity : F ^ k = (F ^ 48) ^ m * F ^ r := by
    calc
      F ^ k = F ^ (48 * m + r) := by rw [← hk]
      _ = (F ^ 48) ^ m * F ^ r := by rw [pow_add, pow_mul]
  have hMainPower : ‖(F ^ 48) ^ m‖ ≤ (24 / 25 : ℝ) ^ m := by
    calc
      ‖(F ^ 48) ^ m‖ ≤ ‖F ^ 48‖ ^ m := norm_pow_le _ _
      _ ≤ (24 / 25 : ℝ) ^ m := by
        exact pow_le_pow_left₀ (norm_nonneg _) hBlock.le _
  have hTransientBound : ‖F ^ r‖ ≤ (61 / 10 : ℝ) :=
    (hTransient r hr).le
  have hMatrix :
      ‖F ^ k‖ ≤ (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) := by
    calc
      ‖F ^ k‖ = ‖(F ^ 48) ^ m * F ^ r‖ := by rw [hPowerIdentity]
      _ ≤ ‖(F ^ 48) ^ m‖ * ‖F ^ r‖ := norm_mul_le _ _
      _ ≤ (24 / 25 : ℝ) ^ m * (61 / 10 : ℝ) := by
        exact mul_le_mul hMainPower hTransientBound (norm_nonneg _)
          (pow_nonneg (by norm_num) _)
      _ = (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) := by
        dsimp [m]
        ring
  calc
    ‖(F ^ k) *ᵥ x‖ ≤ ‖F ^ k‖ * ‖x‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ((61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hMatrix (norm_nonneg x)
    _ = (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) * ‖x‖ := rfl

/-- This is the EXACT CURRENT SOURCE-SPEC reduction: a theorem for the
literal pinned matrix with the finite rational bounds still as hypotheses. -/
def prop51FiniteBoundSpec : Prop :=
  ‖exactDecimalF0 ^ 48‖ < (24 / 25 : ℝ) ∧
    (∀ r : ℕ, r < 48 → ‖exactDecimalF0 ^ r‖ < (61 / 10 : ℝ))

theorem prop51_conditional_exact
    (hFinite : prop51FiniteBoundSpec)
    (k : ℕ) (x : Fin 6 → ℝ) :
    ‖(exactDecimalF0 ^ k) *ᵥ x‖ ≤
      (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) * ‖x‖ := by
  exact block48_decay_of_norm_bounds exactDecimalF0 hFinite.1 hFinite.2 k x


/-!
# Source-specific finite-power KERNEL CERTIFICATE.
The rational-to-real operator norm bridge is proved below.
All finite powers are decided by Lean's kernel (decide +kernel);
no native_decide or external untrusted oracle is used.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 0

private theorem rationalF0_pow7_row_norm_lt :
    ∀ i : Fin 6,
      (∑ j : Fin 6, |((exactDecimalF0Rat ^ 7) i j)|) <
        (61 / 10 : ℚ) := by
  decide +kernel

private theorem rationalF0_pow48_row_norm_lt :
    ∀ i : Fin 6,
      (∑ j : Fin 6, |((exactDecimalF0Rat ^ 48) i j)|) <
        (24 / 25 : ℚ) := by
  decide +kernel


private theorem rationalF0_all_transient_rows :
    ∀ r : Fin 48, ∀ i : Fin 6,
      (∑ j : Fin 6, |((exactDecimalF0Rat ^ r.val) i j)|) <
        (61 / 10 : ℚ) := by
  decide +kernel


/-- The rational-to-real 6x6 row-sum bridge uses the actual matrix
operator norm, preserving the precise pinned decimal coefficients. -/
theorem rational_rows_imply_real_operator_norm
    (n : ℕ) (c : ℚ) (hc : 0 < c)
    (hRows : ∀ i : Fin 6,
      (∑ j : Fin 6, |((exactDecimalF0Rat ^ n) i j)|) < c) :
    ‖exactDecimalF0 ^ n‖ < (c : ℝ) := by
  have hPow :
      exactDecimalF0 ^ n =
        (exactDecimalF0Rat ^ n).map (Rat.castHom ℝ) := by
    rw [Matrix.map_pow]
    rfl
  have hRealRows (i : Fin 6) :
      (∑ j : Fin 6, ‖(exactDecimalF0 ^ n) i j‖) =
        ((∑ j : Fin 6, |((exactDecimalF0Rat ^ n) i j)| : ℚ) : ℝ) := by
    rw [hPow, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change ‖(((exactDecimalF0Rat ^ n) i j : ℚ) : ℝ)‖ =
      ((|((exactDecimalF0Rat ^ n) i j)| : ℚ) : ℝ)
    rw [Real.norm_eq_abs, Rat.cast_abs]
  let cN : ℝ≥0 := ⟨(c : ℝ), by exact_mod_cast hc.le⟩
  have hcN : (0 : ℝ≥0) < cN := by
    apply NNReal.coe_lt_coe.mp
    change (0 : ℝ) < (c : ℝ)
    exact_mod_cast hc
  have hNNRows (i : Fin 6) :
      (∑ j : Fin 6, ‖(exactDecimalF0 ^ n) i j‖₊ : ℝ≥0) < cN := by
    apply NNReal.coe_lt_coe.mp
    change ((∑ j : Fin 6, ‖(exactDecimalF0 ^ n) i j‖₊ : ℝ≥0) : ℝ) < (c : ℝ)
    simp only [NNReal.coe_sum, coe_nnnorm]
    rw [hRealRows]
    exact_mod_cast hRows i
  have hSup :
      ((Finset.univ : Finset (Fin 6)).sup
        fun i => ∑ j : Fin 6, ‖(exactDecimalF0 ^ n) i j‖₊ : ℝ≥0) < cN :=
    (Finset.sup_lt_iff hcN).mpr (by
      intro i hi
      exact hNNRows i)
  rw [Matrix.linfty_opNorm_def]
  change (((Finset.univ : Finset (Fin 6)).sup
    fun i => ∑ j : Fin 6, ‖(exactDecimalF0 ^ n) i j‖₊ : ℝ≥0) : ℝ) < (cN : ℝ)
  exact NNReal.coe_lt_coe.mpr hSup

/-- Finite bounds now established *inside Lean*, not postulated:
all 0..47 and the 48th power were kernel-decided over exact rationals. -/
theorem prop51FiniteBound_proved : prop51FiniteBoundSpec := by
  unfold prop51FiniteBoundSpec
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (rational_rows_imply_real_operator_norm 48 (24 / 25) (by norm_num)
        rationalF0_pow48_row_norm_lt)
  · intro r hr
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (rational_rows_imply_real_operator_norm r (61 / 10) (by norm_num)
        (fun i => rationalF0_all_transient_rows ⟨r, hr⟩ i))

/-- Source-specific, all-k/all-vector conclusion of current Prop. 5.1. -/
theorem prop51_unconditional_exact
    (k : ℕ) (x : Fin 6 → ℝ) :
    ‖(exactDecimalF0 ^ k) *ᵥ x‖ ≤
      (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) * ‖x‖ :=
  prop51_conditional_exact prop51FiniteBound_proved k x

#print axioms prop51FiniteBound_proved
#print axioms prop51_unconditional_exact

#print axioms rationalF0_all_transient_rows

#print axioms rationalF0_pow7_row_norm_lt
#print axioms rationalF0_pow48_row_norm_lt

#print axioms block48_decay_of_norm_bounds
#print axioms prop51_conditional_exact

end CurrentCompact
end Ventura26LiquidityAllocation
