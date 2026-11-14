import Ventura26LiquidityAllocation.InterbankCancellationCandidate

/-!
Isolated CI import and axiom-inspection gate for previously compiled
interbank cancellation proofs. This is not a source-facing result and does
not modify the pinned checkpoint, base library, or any theorem statement.
The output of the following Lean commands must be inspected for sorryAx.
-/

#print axioms Ventura26LiquidityAllocation.proposed_otcBinaryPair_cancel
#print axioms Ventura26LiquidityAllocation.proposed_localSlackExpectedInterbank_eq_zero_of_binarySymmetric
#print axioms Ventura26LiquidityAllocation.proposed_localSlackLiteralAllocation_settlementClears_of_binarySymmetric
#print axioms Ventura26LiquidityAllocation.proposed_localSlackExactDateData_settlementClears
