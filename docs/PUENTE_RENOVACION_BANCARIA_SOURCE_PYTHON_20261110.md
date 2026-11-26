# Bank renewal factor: a necessary SOURCE/Python parameter witness

## Exact SOURCE equation and illustrative Python reference

Original SOURCE (EconomicModel.lean): a_B=1-eta+eta*omega_B, where eta=bankExit, omega_B=bankSeedShare and both are constrained in [0,1]. Python (finite_irf.py): a_B=1/R_star^L and bankExit=eta=.1. Their identification at the **benchmark** requires

omega_B = (1/R_star^L - (1-eta))/eta, eta>0, R_star^L>0.

The additional feasibility condition omega_B in [0,1] is equivalent to 1-eta <= 1/R_star^L <= 1. For 0<eta<1, it implies 1<=R_star^L<=1/(1-eta). At an interior value of R_star^L strictly between those endpoints, the implied bankSeedShare is strictly inside (0,1). This identifies a **candidate parameter** consistent with SOURCE restrictions; it does not construct the full Primitives object nor prove bank optimality.

## Exact bank face source-row / Python-row relation

SOURCE's date-zero/date-one bank nominal face row is

F_t = FB_(t+1) - a_B * RL_t * FB_t / Pi_t.

Python's corresponding row is G_t=log(FB_(t+1) / D_t), D_t=a_B*RL_t*FB_t/Pi_t. On the **positive** bank-face chart,

F_t = D_t * expm1(G_t).

At a common root G_t=0 this yields dF_t=D_t*dG_t. Outside the root the full derivative is dF_t=(dD_t)expm1(G_t)+D_t*exp(G_t)*dG_t. These identities explain the candidate nonzero row normalization, but require identifying the same a_B and nominal faces in the SOURCE and Python data charts.

The numerical auditor code/irf/audit_source_bank_renewal_face_bridge.py tests SOURCE syntax, seed-share admissibility, negative/over-one seed share counterexamples beyond the allowed gross-rate interval, positive off-root bank rows at dates zero and one in both S/B branches, and 33-column derivatives. It records hashes, numerical error and explicit NO flags for complete economic/source certificates. A green result is a *conditional source-transcription* check, not a Lean theorem or a SOURCE Jacobian-invertibility proof.

## Remaining obligations

Construct a SOURCE Primitives instance with exit, seed, matchingIntensity, productivity, payments and endogenous policies all matching the Python case; identify the bank per-type contracts and nominal faces; prove bank objective, matching/settlement, shareholder flow and transversality. Prove all 33 row correspondences under a shared chart on an open domain and then carry a justified inverse bound. The two branch-specific frozen-predecessor roots are not established by this parameter witness. Keep PR #2 draft.
