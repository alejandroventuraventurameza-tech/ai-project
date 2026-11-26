# Proposición 3.1: prueba escalar C1 y frontera con SOURCE

**Fecha:** 26 de noviembre de 2026. **Fuente:** `paper/paper.tex`, etiqueta `prop:local_macro_multiplicity`, commit `bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Entorno:** Lean 4.30.0-rc2 y AppliedModelingLib@194edcc95.

## Resultado matemático

El enunciado escalar supone M(s,h) de clase C1 cerca del origen, M(0,0)=0 y derivadas parciales b=∂s M(0,0)<0 y a_R=∂h M(0,0)<0. La complementariedad exige s≥0, M(s,h)≥0 y s*M(s,h)=0. Para h<0 pequeño, la dirección transversal s=-K*h con K>0 proporciona signos opuestos en los extremos; continuidad e IVT producen una raíz interior positiva. La continuidad del diferencial implica antitonicidad estricta en un entorno común, excluyendo otras raíces locales. Para h>0 pequeño no hay solución complementaria local.

`CurrentCompactProp31LocalBridge.lean` y `CurrentCompactProp31C1Bridge.lean` implementan el razonamiento. Los endpoints `prop31_local_two_signs_of_joint_derivative_and_slices`, `c1_at_origin_implies_uniform_local_slack_antitonicity` y `prop31_scalar_current_C1_exact` compilaron en [Actions #45874098260](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45874098260): 2,146 trabajos, solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Se añade `prop31_scalar_from_only_C1_hypotheses`, que fija el operador de derivada al `fderiv` efectivo; su aprobación depende de una ejecución posterior del mismo CI.

## Obligación económica abierta

`EconomicModel.lean` define `localScalarReducedMap` como dual de financiación L normalizado, evaluado sobre las 33 coordenadas recuperadas por `solutionLog`. `LocalScalarImplicitReduction` asume, no demuestra, resolución diferenciable de las 33 ecuaciones, unicidad local y las cotas `-2.376742673 < b < -2.376742670` y `a_R<0`. La prueba escalar no certifica esas premisas.

Sea F(z;y)=0 el sistema residual, y=(s,h,...). Una vez certificadas la correspondencia literal y la invertibilidad de Jz=D_zF, el teorema de función implícita da D_y z=-(D_zF)^(-1)D_yF. Si el dual normalizado depende de y solo mediante z, entonces D_yM=D_zμ_L·D_yz. Esos dos componentes deben quedar certificados con intervalos rigurosos y prueba de procedencia, no suponerse desde `LocalScalarImplicitReduction`.

Quedan abiertas recuperación de todas las restricciones originales S/B sobre un mismo estado heredado, óptimos dinámicos, TVC, equilibrios infinitos y chequeo oficial `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast`. El paper, las IRF y las figuras permanecen inalterados. Se mantienen 0/8 manuscritos auténticos.
