# Certificado SOURCE: estado de prueba, alcance y trabajo pendiente

**Revisión matemática verificada:** `3c881026632f78122566f21abd30aff4391ee04b`.  
**Rama:** `work/lean-ci-validation-otc-20261106`; **PR:** [#2](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/2), en borrador.  
**Compilación y auditoría exacta:** [Lean boundary proof gate #42902110667](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42902110667): **success**. El job de frontera compila `FirmFaceUniformGapCandidate` y audita los lemas transitivos sin `sorryAx`.

## 1. Lo demostrado en el candidato SOURCE literal

Sea `F_SOURCE(R) = boundaryResourceResidual R`, definido a partir de los componentes económicos de SOURCE, y sea el intervalo racional

`I = [1029135/1000000, 1029136/1000000]`.

| Resultado | Declaración Lean | Archivo |
| --- | --- | --- |
| `F_SOURCE(1.029135) < 0` | `source_narrow_left_resource_residual_negative` | `candidates/Ventura26LiquidityAllocation/BoundaryNarrowLeftResidualSignCandidate.lean` |
| `F_SOURCE(1.029136) > 0` | `source_narrow_right_resource_residual_positive` | `candidates/Ventura26LiquidityAllocation/BoundaryNarrowRightResidualSignCandidate.lean` |
| `1.029135 < boundarySourceRate < 1.029136` | `source_reduced_prefix_rate_in_narrow_interval` | `candidates/Ventura26LiquidityAllocation/BoundaryNarrowRightResidualSignCandidate.lean` |
| Para todo `G,R` en `I`, el término bancario supera `-0.03` | `source_narrow_bank_face_contribution_gt_neg_three_percent` | `candidates/Ventura26LiquidityAllocation/BoundaryBankFaceUniformLowerCandidate.lean` |
| Para todo `G,R` en `I`, la caída de obligaciones empresariales supera `0.11` | `source_uniform_firm_face_decline_gt_11_percent` | `candidates/Ventura26LiquidityAllocation/FirmFaceUniformGapCandidate.lean` |
| Para todo `G,R` en `I`, `inheritedNominalFaceGap > 0.08` | `source_uniform_inherited_nominal_face_gap_gt_eight_percent` | `candidates/Ventura26LiquidityAllocation/FirmFaceUniformGapCandidate.lean` |
| No existe asignación competitiva para la instancia de SOURCE construida | `source_boundary_candidate_not_competitive_equilibrium` | `candidates/Ventura26LiquidityAllocation/FirmFaceUniformGapCandidate.lean` |

La cota de la brecha conserva **ambos términos** de la descomposición:
`D_F > 0.11` y `D_B > -0.03` implican `D_F+D_B > 0.08`. El término bancario es negativo: eliminarlo falsearía la contabilidad.

Las cotas del residual original se obtienen mediante funciones SOURCE y multiplicación por `wage^5>0`: no se reemplazan los objetos económicos por ajustes numéricos ni se importan como axiomas las salidas de Python.

## 2. Cuantificadores y limitación decisiva

El último teorema prueba, en la notación Lean de este repositorio:

```lean
(G : ℝ) (X : Allocation LocalBridgePhase) :
  ¬ CompetitiveEquilibrium
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X
```

La afirmación **descarta esa instancia** de primitivas y ese estado inicial, no una familia universal de economías ni todas las soluciones dinámicas.

En particular, `boundaryInitialState G R` **depende de la tasa R** en componentes heredados que deberían ser predeterminados ante una sorpresa monetaria. Esto ya se distingue en:

- `BoundaryFrozenInheritanceCandidate.lean`: `boundaryInitialState_capital_strictMono`;
- `BoundaryPredeterminedStateCandidate.lean`: `boundary_initial_state_ne_stationary_for_all_boundary_rates` y `frozen_stationary_gap_zero_after_intervention`.

Por tanto, **no puede afirmarse** que se ha demostrado inexistencia de equilibrio para todas las intervenciones con el estado estacionario heredado congelado `inheritedState G`. Tampoco se demuestra existencia de un equilibrio alternativo de horizonte infinito.

## 3. Jerarquía de evidencia

- **DEMOSTRADO (Lean kernel y gate específico):** teoremas expresamente listados en la sección 1, para la fuente y revisión indicadas.
- **NUMÉRICO:** auditorías independientes de intervalos y evaluaciones de residuales. Son comprobaciones de consistencia, no premisas del kernel.
- **PENDIENTE:** reconstruir un equilibrio con estado heredado fijo, condiciones de optimalidad intertemporal, terminalidad y restricciones activas; ejecutar IRF estructurales bajo el conjunto de instrumentos (tasa de política, corredor, balance, encaje) con contabilidad de stocks predeterminados; conectar estos objetos con los efectos dinámicos de mala asignación y crecimiento de largo plazo.

No transferir automáticamente estas pruebas del **candidato reducido** a los resultados generales de multiplicidad, transmisión monetaria ni bienestar del manuscrito. Un workflow de compilación del artículo o de figuras tampoco garantiza por sí solo esas afirmaciones económicas.

## 4. Reproducción y auditoría

El workflow `.github/workflows/lean-boundary-proof-gate.yml` compila `Ventura26LiquidityAllocation.FirmFaceUniformGapCandidate` con el entorno fijado y ejecuta `#print axioms` en la cadena de teoremas. El gate rechaza referencias a `sorryAx`; los axiomas básicos de Mathlib/Lean, como `propext`, `Classical.choice` o `Quot.sound`, son distintos de un agujero de prueba.

**Criterio para citar el resultado:** fijar commit de código, nombre completo del teorema, definición del estado heredado y ID del run exitoso. No usar únicamente un enlace a un PDF regenerado como evidencia de la prueba formal.
