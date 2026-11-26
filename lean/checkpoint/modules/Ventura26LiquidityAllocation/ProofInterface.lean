import Ventura26LiquidityAllocation.PaperInterface

/-!
# Proof Interface: Monetary Policy, Bank Liquidity and Capital Allocation

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace Ventura26LiquidityAllocation

lemma repayment : repaymentSpec := by sorry
lemma noSimultaneousSavingBorrowing : noSimultaneousSavingBorrowingSpec := by sorry
theorem financingCapacityComparative : financingCapacityComparativeSpec := by sorry
lemma signedFundingEquivalenceEndpoint : signedFundingEquivalenceSpec := by sorry
lemma fundingSupergradient : fundingSupergradientSpec := by sorry
lemma financialKKTEquivalence : financialKKTEquivalenceSpec := by sorry
lemma otcCorridorMonotonicity : otcCorridorMonotonicitySpec := by sorry
theorem bankSpreadNonnegative : bankSpreadNonnegativeSpec := by
  intro S J _instS _decidableS _instJ P X candidatePlan t h
    mass retainedEquityByType loansByType reservesByType depositsByType
    depositCapByType loanCapByType paymentSupportByType
    paymentProbabilityByType paymentShockByType candidateType bankValue
    deficitSupply surplusSupply tightness hreserveRate hcorridor _hrhoLowerBound
    _hrhoUpperBound hxi hregime
  rcases hregime with
    ⟨_hpopulation, _hretainedIdentity, _hloansIdentity, _hreservesIdentity,
      _hdepositsIdentity, _hdeficitIdentity, _hsurplusIdentity, hactivity,
      _htightnessIdentity, hmatching, hinterbankRate, _hflows,
      _hpopulationFeasible, hcandidateFeasible, hretainedPositive,
      hloansPositive, hreservesPositive, hdepositsPositive,
      _hprobabilityPositive, hinflation, hstrictSolvency, hhomogeneous,
      henvironment⟩
  have htightnessPositive : 0 < tightness := by
    rcases hactivity with ⟨hdeficitPositive, hsurplusPositive, htightness⟩
    rw [htightness]
    exact div_pos hdeficitPositive hsurplusPositive
  have hslopeOrderRaw := otcSlopes_ordered
    (X.reserveRate t h) (X.facilityRate t h) P.matchingIntensity tightness
    hcorridor hmatching htightnessPositive
  have hslopeOrder :
      0 ≤ bankOTCSurplusSlopeAt P X t h tightness ∧
        bankOTCSurplusSlopeAt P X t h tightness ≤
          bankOTCDeficitSlopeAt P X t h tightness := by
    simpa [bankOTCSurplusSlopeAt, bankOTCDeficitSlopeAt, hinterbankRate] using
      hslopeOrderRaw
  have hoptimal := bankStaticPortfolioOptimal_of_dynamicBellman
    P X candidatePlan t h tightness bankValue hhomogeneous henvironment
  obtain ⟨marginalLiquidity, loanCapDual, depositCapDual, hsupport⟩ :=
    bankSpreadKKTSupport_of_interior P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      (candidatePlan.retainedEquity t h) (candidatePlan.loans t h)
      (candidatePlan.reservesPre t h) (candidatePlan.deposits t h)
      hreserveRate hslopeOrder.1 hslopeOrder.2 hxi hcandidateFeasible
      hretainedPositive ⟨hloansPositive, hreservesPositive, hdepositsPositive⟩
      hinflation hstrictSolvency hoptimal
  rcases hsupport with
    ⟨hkkt, _hcovarianceIdentity, _hcovarianceNonpositive,
      hcrossMomentNonpositive, hspreadIdentity⟩
  rcases hkkt with ⟨hfoc, _hmarginalAntitone⟩
  dsimp [BankStaticFOCConditionsAt] at hfoc
  rcases hfoc with
    ⟨hloanDualNonnegative, hdepositDualNonnegative, hsupergradient,
      _hloanFOC, _hdepositFOC, hloanComplementarity,
      hdepositComplementarity⟩
  have hmarginalNonnegative :
      ∀ ω ∈ P.paymentSupport, 0 ≤ marginalLiquidity ω := by
    intro ω hω
    have hcases :=
      (isOTCLiquiditySupergradient_iff_cases hslopeOrder.2).mp
        (hsupergradient ω hω)
    rcases hcases with hnegative | hzero | hpositive
    · rcases hnegative with ⟨_, hmarginal⟩
      rw [hmarginal]
      exact le_trans hslopeOrder.1 hslopeOrder.2
    · rcases hzero with ⟨_, hmarginalLower, _⟩
      exact le_trans hslopeOrder.1 hmarginalLower
    · rcases hpositive with ⟨_, hmarginal⟩
      rw [hmarginal]
      exact hslopeOrder.1
  have hexpectationNonnegative :
      0 ≤ finiteSupportExpectation P.paymentSupport P.paymentProbability
        marginalLiquidity := by
    unfold finiteSupportExpectation
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (P.payment_probability_pos_on_support ω hω).le
      (hmarginalNonnegative ω hω)
  have hxiGapNonnegative :
      0 ≤ X.depositRate t h / X.reserveRate t h -
        P.reserveRequirementPath t h := sub_nonneg.mpr hxi.le
  have hnegativeCrossNonnegative :
      0 ≤ - ((X.depositRate t h / X.reserveRate t h -
          P.reserveRequirementPath t h) *
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω ↦ marginalLiquidity ω * P.paymentShock ω)) :=
    neg_nonneg.mpr
      (mul_nonpos_of_nonneg_of_nonpos hxiGapNonnegative
        hcrossMomentNonpositive)
  have hspreadNonnegative : 0 ≤ X.loanRate t h - X.depositRate t h := by
    rw [hspreadIdentity]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (mul_nonneg _hrhoLowerBound hexpectationNonnegative)
          hnegativeCrossNonnegative)
        hloanDualNonnegative)
      hdepositDualNonnegative
  refine ⟨marginalLiquidity, loanCapDual, depositCapDual, ?_,
    hloanDualNonnegative, hdepositDualNonnegative, hloanComplementarity,
    hdepositComplementarity, hspreadIdentity, hspreadNonnegative⟩
  exact hsupergradient
theorem aggregateFlowConsistency : aggregateFlowConsistencySpec := by sorry
theorem boundaryEquilibrium : boundaryEquilibriumSpec := by sorry
theorem localMacroMultiplicity : localMacroMultiplicitySpec := by sorry
lemma allocationLossIdentity : allocationLossIdentitySpec := by sorry
theorem oppositeBranchAllocation : oppositeBranchAllocationSpec := by sorry
theorem riskyBranchPersistence : riskyBranchPersistenceSpec := by sorry
lemma steadyStatePositive : steadyStatePositiveSpec := by sorry
theorem realClosure : realClosureSpec := by sorry
theorem bankRetention : bankRetentionSpec := by sorry
theorem stationaryExistence : stationaryExistenceSpec := by sorry
theorem steadyStateEfficiencyFactor : steadyStateEfficiencyFactorSpec := by sorry
theorem negativeComparative : negativeComparativeSpec := by sorry
lemma pledgeOrderingEfficiency : pledgeOrderingEfficiencySpec := by sorry
theorem dynamicCreditSupply : dynamicCreditSupplySpec := by sorry
lemma finiteMinimumDirectionalDerivative : finiteMinimumDirectionalDerivativeSpec := by sorry
theorem slackCreditSupply : slackCreditSupplySpec := by sorry
theorem slackDepositPriceRegularity : slackDepositPriceRegularitySpec := by sorry
lemma statewiseCollateral : statewiseCollateralSpec := by sorry
theorem stochasticPartialH : stochasticPartialHSpec := by sorry
theorem boundedBankContinuation : boundedBankContinuationSpec := by sorry
theorem noPermanentSaver : noPermanentSaverSpec := by sorry
lemma nominalFaceIdentity : nominalFaceIdentitySpec := by sorry
theorem householdBudgetReconstruction : householdBudgetReconstructionSpec := by sorry
lemma commonPledgeState : commonPledgeStateSpec := by sorry
theorem stableProjection : stableProjectionSpec := by sorry
lemma boundedBoundaryInverse : boundedBoundaryInverseSpec := by sorry
theorem nonlinearLocalPath : nonlinearLocalPathSpec := by sorry
theorem firmSufficiencyInfinite : firmSufficiencyInfiniteSpec := by sorry
theorem retailLocalSufficiency : retailLocalSufficiencySpec := by sorry
theorem affineRiskCandidate : affineRiskCandidateSpec := by sorry
lemma treeComparisonBound : treeComparisonBoundSpec := by sorry
theorem stochasticSelectedInverse : stochasticSelectedInverseSpec := by sorry
theorem selectedNonlinearFamily : selectedNonlinearFamilySpec := by sorry
theorem globalStochasticPriceOptimality : globalStochasticPriceOptimalitySpec := by sorry
theorem validatedTreeInverse : validatedTreeInverseSpec := by sorry
theorem certifiedSmallRiskEquilibrium : certifiedSmallRiskEquilibriumSpec := by sorry
lemma minimumUniformInverse : minimumUniformInverseSpec := by sorry
theorem certifiedEndogenousMinimum : certifiedEndogenousMinimumSpec := by sorry
theorem regimeTube : regimeTubeSpec := by sorry
theorem generalRegimeSufficiency : generalRegimeSufficiencySpec := by sorry
theorem finitePrefixEquilibrium : finitePrefixEquilibriumSpec := by sorry
theorem finiteSlackSpell : finiteSlackSpellSpec := by sorry
theorem pledgeSelectionComparative : pledgeSelectionComparativeSpec := by sorry
theorem positiveMixedChannel : positiveMixedChannelSpec := by sorry
theorem capitalCreationChannel : capitalCreationChannelSpec := by sorry
lemma crraHDemand : crraHDemandSpec := by sorry
theorem crraPositiveMixed : crraPositiveMixedSpec := by sorry
lemma twoRateImplementation : twoRateImplementationSpec := by sorry
theorem closedTwoDateEquilibrium : closedTwoDateEquilibriumSpec := by sorry

end Ventura26LiquidityAllocation
