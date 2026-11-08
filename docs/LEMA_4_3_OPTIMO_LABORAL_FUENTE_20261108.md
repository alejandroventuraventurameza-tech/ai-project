# Lema 4.3 — puente desde la tecnología micro hasta el óptimo laboral global

**Fecha de revisión:** 8 de noviembre de 2026. **Rama:** `work/lean-ci-validation-otc-20261106`.
**Estado de compilación comprobado:** los cinco teoremas de producción microagregada y cuatro del óptimo laboral normalizado superaron compilación y auditoría de axiomas sin `sorryAx` en [CI focalizada #42500091118](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42500091118), commit `e9ec2024da991768115ecb70e39acdfb647f8b9a`. El nuevo puente de **toda asignación laboral física** en `PaperOriginalLaborGlobalCandidate.lean` sigue **pendiente de validación CI**; no contabilizarlo aún.

## 1. Primitivas económicas

Para dos tipos `i=H,L`, masas `v_i>0`, productividades `A_i>0`, capitales `k_i>0`, trabajo total `L>0` y exponentes **comunes** `alpha>0`, `0<beta<1`, `alpha+beta<1`, defina

```text
y_i = A_i k_i^alpha ell_i^beta
G = sum_i v_i g_i > 0
g_i = A_i^(1/(1-beta)) k_i^(alpha/(1-beta))
ell_i* = L g_i/G
```

La asignación propuesta satisface `ell_i*>0` y `sum_i v_i ell_i*=L`.
No se impone ni supone que el empleo de las empresas sea igual.

## 2. Puente exacto entre producción individual y agregada

Para cada empresa,

```text
A_i k_i^alpha = g_i^(1-beta)
A_i k_i^alpha (L g_i/G)^beta = (L/G)^beta g_i.
```

La segunda expresión se deriva de la primera usando las leyes de potencia para cantidades positivas. Al agregar con las masas originales,

```text
Y(ell*) = sum_i v_i A_i k_i^alpha (L g_i/G)^beta
        = (L/G)^beta sum_i v_i g_i
        = L^beta G^(1-beta).
```

Este cálculo **no** debe sustituirse por la definición tautológica `Y := L^beta G^(1-beta)` del contrato `allocationLossIdentitySpec` original. El módulo `PaperAllocationSourceAlgebraBridgeCandidate.lean` introduce teoremas para obtenerlo desde la tecnología física.

## 3. Suficiencia global, no solo FOC

Para cualquier `ell_H,ell_L>=0` con `sum_i v_i ell_i=L`, construya

```text
x_i = ell_i / ell_i* >= 0,
w_i = v_i g_i > 0,
sum_i w_i x_i = G.
```

Para `0<beta<1`, la concavidad de `x^beta` se demuestra por la desigualdad de Young/AM–GM con pesos `beta,1-beta`:

```text
x_i^beta <= beta*x_i + (1-beta).
```

Al multiplicar por `w_i` y sumar,

```text
sum_i w_i x_i^beta
  <= beta*sum_i w_i x_i + (1-beta)*sum_i w_i
   = G.
```

Además, por la identidad de producción individual,

```text
Y(ell) = (L/G)^beta sum_i w_i x_i^beta
       <= (L/G)^beta G
        = Y(ell*).
```

El candidato `x_H=x_L=1` alcanza igualdad: **óptimo global en trabajo a capital fijo**. La restricción laboral se cumple sin una hipótesis de interioridad para las *alternativas*; `ell_i>=0` es suficiente. La unicidad estricta puede probarse adicionalmente usando `0<beta<1` y `w_i>0`.

## 4. Cobertura formal que se está auditando

- `PaperAllocationSourceAlgebraBridgeCandidate.lean`: `source_weight_pow_identity`, `source_output_at_weighted_labor`, `positive_labor_aggregate_power`, `source_two_type_output_at_optimal_labor`, `source_labor_candidate_clears_resources`.
- `PaperOptimalLaborCandidate.lean`: `normalized_labor_global_bound`, `source_output_with_scaled_labor`, `source_two_type_global_labor_optimality`, `source_labor_global_bound_attained`.
- `.github/workflows/lean-focused-paper-claims.yml`: copiado, compilación, `#print axioms` y rechazo de `sorryAx` para los módulos.

**Advertencia sobre la verificación:** [focalizada #42499827416](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42499827416) **falló** porque un `ring` se ejecutó tras `field_simp` ya terminal (línea 208 del módulo fuente). Se corrigió con `<;> ring` en commit `e9ec2024`; la [ejecución focalizada #42500091118](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42500091118) **aprobó compilación y revisión de axiomas**. Los 9 teoremas auxiliares nuevos quedaron así verificados en ese commit. La primera falla dejó un `sorryAx` en un teorema: no puede contarse como demostración.


## 4 bis. Eliminación de la hipótesis de presupuesto normalizado

En el módulo candidato `PaperOriginalLaborGlobalCandidate.lean` se parte
de cualquier `ell_H,ell_L >= 0` con `v_H ell_H+v_L ell_L=L`.
Con `g_i>0`, `G>0` y `L>0` se define
`x_i=ell_i G/(L g_i)`. Entonces

```text
(L g_i/G) x_i = ell_i,
sum_i v_i g_i x_i = (G/L) sum_i v_i ell_i = G.
```

El teorema fuente `original_two_type_labor_global_bound` intenta
transportar el resultado ya verificado sobre coordenadas normalizadas
a producción física para todas las alternativas no negativas:

```text
sum_i v_i A_i k_i^alpha ell_i^beta <= L^beta G^(1-beta).
```

También se registra `original_labor_candidate_attains_global_bound`,
que proporciona igualdad en `ell_i*=L g_i/G`. **Estado:** los
nuevos objetivos de este módulo NO se promocionan hasta que
la CI focalizada del commit que los contiene y la auditoría
de axiomas resulten exitosas. La demostración sigue siendo de
óptimo laboral **con capital fijo**.

## 5. Brechas restantes para el lema académico completo

1. Auditar el nuevo candidato `original_two_type_labor_global_bound` que transporta cualquier alternativa física `ell_i>=0` a `x_i` y el presupuesto normalizado, y distinguir su cota global (capital fijo) de la prueba eficiente de capital **y** trabajo. No se promueve hasta compilación y `#print axioms` verdes.
2. Conectar la cota global de capital y trabajo (AM–GM ya verificada en módulo separado) con `Yeff = K^alpha L^beta ZA^(1-alpha-beta)` desde producción física y presupuestos originales.
3. Derivar formalmente `d log G` y `d log K` desde sus funciones reales diferenciables para llegar a `dLoss = alpha(kappaH-omegaH)d log(kH/kL)`. El álgebra **condicional** de coeficientes ya está verificada.
4. Corregir la interfaz `allocationLossIdentitySpec` en un módulo nuevo (no mutar el checkpoint), haciendo explícitos los exponentes comunes y la producción `sum_i v_i y_i` que actualmente falta.
5. Separar el lema de producción condicional de existencia de equilibrio dinámico, selección de ramas S/B, causalidad de un shock monetario y **crecimiento sostenido**: nada de ello se deduce de la desigualdad laboral.

## 6. Reglas de promoción al paper

Solo después de CI verde para el **SHA exacto**, `#print axioms` sin `sorryAx` y cotejo semántico de hipótesis, registrar cada declaración como auxiliar probada. No cambiar `paper_proof_equivalent_in_lean = not_established` ni `source_ledger_formalization_status = not_run` únicamente por disponer de nueve pruebas nuevas. Las cuatro brechas anteriores siguen impidiendo equivalencia integral del Lema 4.3.
