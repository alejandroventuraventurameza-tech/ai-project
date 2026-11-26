import Ventura26LiquidityAllocation.CurrentPinnedOpenBankDomain
import Ventura26LiquidityAllocation.CurrentPinnedStationaryPrefix33Root
import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivRank

/-!
# Topological neighborhood at the exact binding SOURCE 33-row root

The prior SOURCE proofs establish:
* an exact binding finite-prefix root at the log origin;
* pointwise banking admissibility on the explicit region
    z(16) < log 2 and z(32) < log 2;
* a conditional Frechet Jacobian transport theorem requiring
    eventual admissibility at the same root.

Here we close the TOPOLOGICAL neighborhood obligation. This does
NOT establish differentiability of F or E, non-singularity or inverse
norm of the SOURCE economic Jacobian, an augmented 34-root, a Python
function identity, a global equilibrium or any policy IRF.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedLocalNeighborhood

open CurrentPinnedOpenBankDomain
open CurrentPinnedBankDomain
open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank
open scoped Topology

/-- The explicit 33-log-dimensional SOURCE bank-domain region. -/
def pinnedBankLogRegion : Set Row33 :=
  {z | z (16 : Fin 33) < Real.log 2 ∧
       z (32 : Fin 33) < Real.log 2}

/-- The two coordinate half-spaces are open for the actual
finite-dimensional product (equivalently normed pi) topology. -/
theorem pinnedBankLogRegion_isOpen : IsOpen pinnedBankLogRegion := by
  have h16 :
      IsOpen {z : Row33 | z (16 : Fin 33) < Real.log 2} := by
    change IsOpen
      ((fun z : Row33 => z (16 : Fin 33)) ⁻¹'
        Set.Iio (Real.log 2))
    exact isOpen_Iio.preimage (continuous_apply (16 : Fin 33))
  have h32 :
      IsOpen {z : Row33 | z (32 : Fin 33) < Real.log 2} := by
    change IsOpen
      ((fun z : Row33 => z (32 : Fin 33)) ⁻¹'
        Set.Iio (Real.log 2))
    exact isOpen_Iio.preimage (continuous_apply (32 : Fin 33))
  change IsOpen
    ({z : Row33 | z (16 : Fin 33) < Real.log 2} ∩
     {z : Row33 | z (32 : Fin 33) < Real.log 2})
  exact h16.inter h32

#print axioms pinnedBankLogRegion_isOpen

/-- The exact SOURCE stationary log root lies strictly inside this
region; no marginal-zero or financial equation is assumed here. -/
theorem pinnedBankLogRegion_zero_mem :
    (0 : Row33) ∈ pinnedBankLogRegion := by
  have hlog : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  change (0 : Row33) 16 < Real.log 2 ∧
    (0 : Row33) 32 < Real.log 2
  constructor <;> simpa using hlog

#print axioms pinnedBankLogRegion_zero_mem

/-- Eventual SOURCE bank admissibility of BOTH economic dates at
the exact binding stationary log root, discharged with no extra
domain assumption. The macro-economic parameter G remains symbolic. -/
theorem pinned_banking_admissible_eventually (G : ℝ) :
    ∀ᶠ z : Row33 in 𝓝 (0 : Row33),
      TargetBankAdmissible
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) ∧
      TargetBankAdmissible
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) := by
  have hnbhd :
      ∀ᶠ z : Row33 in 𝓝 (0 : Row33),
        z ∈ pinnedBankLogRegion :=
    pinnedBankLogRegion_isOpen.mem_nhds
      pinnedBankLogRegion_zero_mem
  filter_upwards [hnbhd] with z hz
  exact pinned_both_dates_bank_admissible G z hz.1 hz.2

#print axioms pinned_banking_admissible_eventually

/-- Apply the existing *actual SOURCE* Frechet transport theorem
at the now-proven binding root. No root nor banking-eventual
hypothesis remains; only the two substantive differentiation
premises hA and hF remain explicit. -/
theorem pinned_targetized_hasFDerivAt_stationary_root (G : ℝ)
    (J : Row33 →L[ℝ] Row33)
    (dA : Row33 →L[ℝ] (Row33 →L[ℝ] Row33))
    (hA : HasFDerivAt
      (economicLogShearCLM
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
        (sourceLogLinearContinuation
          ProposedStationaryRealScale.stateSix
          ProposedStationaryRealScale.controls
          sourceFrozenP0TenControls))
      dA (0 : Row33))
    (hF : HasFDerivAt
      (localReducedPrefixLogResidualVector .binding
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
        (sourceLogLinearContinuation
          ProposedStationaryRealScale.stateSix
          ProposedStationaryRealScale.controls
          sourceFrozenP0TenControls))
      J (0 : Row33)) :
    HasFDerivAt
      (targetizedLogPrefix33 .binding
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
        (sourceLogLinearContinuation
          ProposedStationaryRealScale.stateSix
          ProposedStationaryRealScale.controls
          sourceFrozenP0TenControls))
      ((economicLogShearCLM
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
        (sourceLogLinearContinuation
          ProposedStationaryRealScale.stateSix
          ProposedStationaryRealScale.controls
          sourceFrozenP0TenControls) (0 : Row33)).comp J)
      (0 : Row33) := by
  apply targetizedLogPrefix33_hasFDerivAt_at_source_root
    .binding (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    (0 : Row33) J dA
  · rfl
  · simpa only [pinnedDateZero, pinnedDateOne] using
      pinned_banking_admissible_eventually G
  · exact hA
  · exact hF
  · exact CurrentPinnedStationaryRoot.pinned_stationary_binding_prefix33_root G

#print axioms pinned_targetized_hasFDerivAt_stationary_root

end CurrentPinnedLocalNeighborhood
end Ventura26LiquidityAllocation
