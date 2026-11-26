import Ventura26LiquidityAllocation.PaperInterface
import Ventura26LiquidityAllocation.ContinuationContractAuditCandidate

/-!
Formal interface diagnostic for Proposition 4.2.

This proposed theorem refutes the CURRENT Lean specification, not the
economic source proposition. The issue is the literal allocation uniqueness
in LocalExactContinuationAround: CompetitiveEquilibrium does not constrain
collateralDual, but AllocationFullNear and literal structure equality do.
The underlying obstruction was proved in ContinuationContractAuditCandidate.

No edits to PaperInterface, upstream modules or pinned checkpoint.
No sorry/admit/custom axioms.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedProposition42Audit

theorem localMacroMultiplicitySpec_false : ¬ localMacroMultiplicitySpec := by
  intro hspec
  rcases hspec with
    ⟨S, hfin, hdec, P, I, X0, dateOne, recurrent, Z0, tail, solutionLog,
      hStar, r, _hboundary, _htransient, _hcalendar, _hregime,
      _hcoords, _hcontrols, hcontinuation, _hrest⟩
  letI : Fintype S := hfin
  letI : DecidableEq S := hdec
  exact (ProposedContinuationContractAudit.not_localExactContinuationAround
    P recurrent Z0.stateTwo tail) hcontinuation

end ProposedProposition42Audit
end Ventura26LiquidityAllocation
