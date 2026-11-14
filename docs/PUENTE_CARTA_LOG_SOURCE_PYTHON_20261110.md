# SOURCE log chart and Python decoder (10-XI-2026)

The SOURCE checkpoint \`EconomicModel.lean\` defines \`localPrefixCoordinatesVector\` and \`localPrefixCoordinatesOfVector\` on 33 coordinates. The ordering is \`stateOne (7), controlsZero (10), stateTwo (6), controlsOne (10)\`. The Python \`decode_prefix\` code indexes \`X1,U0,X2,U1\` with the same offsets. This is an **index-order claim**, not automatic equivalence of economic levels.

The SOURCE positive chart is \`psi(Z0,z)_j=Z0_j*exp(z_j)\`. Conditional on identifying the baseline source \`Z0\` with Python's \`base.X1,U0,X2,U1\`, it has derivative \`diag(Z0_j*exp(z_j))\`, inverse \`diag(1/(Z0_j*exp(z_j)))\` and inverse chart \`log(x_j/Z0_j)\`, provided all \`Z0_j>0\`. These are exact identities of the mathematical chart; numerical checks below test the decoded implementation.

\`code/irf/audit_source_log_coordinate_chart.py\` parses both SOURCE selectors and reconstruction fields, checking 33 exact matching positions; guards the literal \`localPrefixLogChart\` definition; and compares the actual Python decoder against the proposed source chart at three points. It checks the inverse log transform and all 33x33 directional differences. Output JSON includes source hashes, numerical deviations and flags for still-unproved correspondence.

**What this does NOT establish:** the source and Python baselines represent the same \`Primitives\`, \`InheritedState\`, bank plan or supported history; source \`LocalPrefixDateData\` equals Python \`auxiliary\` as functions; the policy controls, four shocks, or terminal continuation coincide; or the economic Jacobians are equivalent. Therefore \`Dpsi\` is a proven-in-mathematics candidate coordinate transformation but the full \`DG=P*T*DF*Dpsi\` remains open. Keep PR draft.
