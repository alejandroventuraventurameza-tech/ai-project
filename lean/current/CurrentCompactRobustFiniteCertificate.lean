import Ventura26LiquidityAllocation.CurrentCompactBlock48Tail

/-!
# Exact finite robustness majorants for the current Lemma 5.2

Source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8
and code/irf/inputs/rational_preconditioners.json, SHA256
d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94.

The two arrays contain OUTWARD rational upper bounds with unit 10^-12.
Each norm bound M_n is STRICTLY GREATER than the source's exact
rational induced infinity norm ||F0^n||. The second sequence B_n
obeys B_0=1 and for n=1,...,48:
  B_n >= M_n + 10^-4 sum_{j<n} M_j B_(n-1-j)
(all in the same rational units). This is checked by decide +kernel.

These 49 finite bounds must be combined with a mathematical induction
and the rational-to-real norm bridge to claim full source-specific
uniform decay. No identification with the SOURCE DSGE Jacobian.
-/

open scoped NNReal Matrix Matrix.Norms.Operator

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

private def normScale : ℚ := 1000000000000

-- BEGIN NORM_UPPER_49
private def sharpNormUpperInt : Fin 49 → ℕ := ![
    1000000000001, 2356707835249, 2876827084900, 3417266940354, 4226213585358, 
    5330396015315, 5989885496253, 6097821698407, 5737515407899, 5052575073810, 
    4019893465919, 3041300974937, 2136274317830, 1561946942193, 1253843531567, 
    1454652895787, 1623770126124, 1698064043386, 2045867901772, 2343902582530, 
    2527711124064, 2565218594823, 2458047367072, 2236154397782, 1947806442099, 
    1647517313883, 1384574578531, 1194279427237, 1093185264364, 1104336767296, 
    1145475560034, 1225369878803, 1326656823505, 1408046649880, 1449849262759, 
    1443243996375, 1390346982588, 1302161768038, 1195122339203, 1087103753626, 
    993748274031, 925768223563, 887600366639, 877470481837, 888646278373, 
    911460695860, 935601188615, 952184210205, 955246892194
  ]
-- END NORM_UPPER_49

-- BEGIN ROBUST_UPPER_49
private def robustUpperInt : Fin 49 → ℕ := ![
    1000000000000, 2356807835250, 2877298436468, 3418397783656, 4228253259869, 
    5333680211641, 5994911080580, 6105134003467, 5747517946273, 5065479371765, 
    4035727038203, 3059875514079, 2157168180700, 1584542553814, 1277392155958, 
    1478373468327, 1646977764086, 1720252528749, 2066690399930, 2363291377325, 
    2545926021341, 2582744418318, 2475445098379, 2253945466785, 1966401913477, 
    1667152752784, 1405264549731, 1215837102309, 1115270400989, 1126525088941, 
    1167348095650, 1246584409996, 1346991838588, 1427432980415, 1468389880414, 
    1461170480181, 1407949940105, 1319735429415, 1212909778573, 1105255558955, 
    1012301637194, 944652171830, 906659145554, 896502010190, 907444650735, 
    929856798843, 953488451424, 969532560572, 972103438404
  ]
-- END ROBUST_UPPER_49

/-- Uniformly zero outside the certified range, to simplify finite sums. -/
private def sharpUpperRat (n : ℕ) : ℚ :=
  if h : n < 49 then (sharpNormUpperInt ⟨n, h⟩ : ℚ) / normScale else 0

private def robustUpperRat (n : ℕ) : ℚ :=
  if h : n < 49 then (robustUpperInt ⟨n, h⟩ : ℚ) / normScale else 0

/-! The following are finite decidable propositions: 49×6 exact
rational row checks, 48 rational convolution checks, and strict thresholds.
The constructor uses no floating-point operations or native_decide. -/

private theorem finiteSourceRowsVerified :
    ∀ n : Fin 49, ∀ i : Fin 6,
      (∑ j : Fin 6, |((exactDecimalF0Rat ^ n.val) i j)|) <
        sharpUpperRat n.val := by
  decide +kernel

private theorem finiteSharpPositive :
    ∀ n : Fin 49, 0 < sharpUpperRat n.val := by
  decide +kernel

private theorem finiteRobustStepVerified :
    ∀ n : Fin 49, 0 < n.val →
      sharpUpperRat n.val +
        ∑ j ∈ Finset.range n.val,
          (sharpUpperRat j * (1 / 10000 : ℚ)) *
            robustUpperRat (n.val - 1 - j)
        ≤ robustUpperRat n.val := by
  decide +kernel

private theorem finiteRobustBaseVerified :
    (1 : ℚ) ≤ robustUpperRat 0 := by
  decide +kernel

private theorem finiteRobust48Verified :
    robustUpperRat 48 < (49 / 50 : ℚ) := by
  decide +kernel

private theorem finiteRobustTransientVerified :
    ∀ n : Fin 48, robustUpperRat n.val < (7 : ℚ) := by
  decide +kernel

#print axioms finiteSourceRowsVerified
#print axioms finiteRobustStepVerified
#print axioms finiteRobust48Verified
#print axioms finiteRobustTransientVerified

end CurrentCompact
end Ventura26LiquidityAllocation
