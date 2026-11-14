# Lema 4.3 — frontera eficiente conjunta de capital y trabajo desde la tecnología fuente

**Fecha:** 8 de noviembre de 2026. **Rama de revisión:** `work/lean-ci-validation-otc-20261106`.  
**Estado verificado:** cuatro puentes auxiliares de normalización y cota AM–GM pasaron compilación y `#print axioms` sin `sorryAx`: [CI #42501665345](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42501665345), commit `c578e398`, y [CI #42501725491](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42501725491), commit `f8e1125b`. Los teoremas originales de frontera conjunta y log-loss también quedaron **verificados** por [CI #42502060253](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42502060253), commit `5ea744a5`, sin `sorryAx`. Total de esta campaña conjunta: **ocho nuevos teoremas kernel-checked**.

## 1. Problema exactamente demostrado

Sea `i ∈ {H,L}`, con `v_i>0`, `A_i>0` y `a,b,d>0`, `a+b+d=1`. Dada una dotación agregada positiva `K,L>0`, considere todas las asignaciones físicas `k_i,ell_i>=0` tales que

```text
sum_i v_i k_i = K
sum_i v_i ell_i = L
Y(k,ell) = sum_i v_i A_i k_i^a ell_i^b .
```

Esta es la **tecnología microeconómica fuente**, no una función agregada impuesta como definición. El objetivo es probar

```text
Y(k,ell) <= Yeff = K^a L^b Z^d,      Z = sum_i v_i A_i^(1/d)
```

y la existencia de un candidato factible que alcance igualdad.

## 2. Cambio de variables y presupuestos originales

Defina `z_i=A_i^(1/d)>0`, `w_i=v_i z_i>0` y `Z=sum_i w_i>0`. Para cada asignación admisible,

```text
x_i = k_i Z/(K z_i) >= 0
t_i = ell_i Z/(L z_i) >= 0.
```

Las identidades de recuperación son exactas:

```text
k_i = (K z_i/Z) x_i
ell_i = (L z_i/Z) t_i.
```

Al sustituir las restricciones **originales** de agregados, sin imponer un supuesto adicional sobre `x_i,t_i`,

```text
sum_i w_i x_i = (Z/K) sum_i v_i k_i = Z,
sum_i w_i t_i = (Z/L) sum_i v_i ell_i = Z.
```

Se conservan las alternativas de esquina `k_i=0` o `ell_i=0`. La positividad se requiere de `K,L,z_i,Z` como denominadores, no de cada factor instalado.

## 3. Producción de cada firma recuperada de la tecnología original

Como `z_i^d=A_i`, `a+b+d=1` y los cocientes `K/Z,L/Z` son positivos,

```text
A_i k_i^a ell_i^b
= z_i^d ((K z_i/Z) x_i)^a ((L z_i/Z) t_i)^b
= (K/Z)^a (L/Z)^b z_i x_i^a t_i^b .
```

**Este paso no está implícito en AM–GM.** Depende de las leyes de potencia real y de la tecnología Cobb–Douglas con exponentes **comunes** a ambas empresas; es una obligación independiente en Lean.

Al sumar por las masas originales,

```text
Y(k,ell)=(K/Z)^a (L/Z)^b sum_i w_i x_i^a t_i^b.
```

## 4. Cota global y candidato que alcanza igualdad

Por la desigualdad AM–GM ponderada con pesos `a,b,d` y argumento tercero igual a uno,

```text
x_i^a t_i^b <= a*x_i + b*t_i + d.
```

Multiplicando por `w_i`, sumando y usando los presupuestos normalizados obtenidos en el paso 2,

```text
sum_i w_i x_i^a t_i^b
 <= a sum_i w_i x_i + b sum_i w_i t_i + d sum_i w_i
 = (a+b+d)Z = Z.
```

Por tanto,

```text
Y(k,ell) <= (K/Z)^a (L/Z)^b Z
          = K^a L^b Z^d.
```

La igualdad es alcanzable con `x_H=x_L=t_H=t_L=1`, equivalente a

```text
k_i* = K z_i/Z,
ell_i* = L z_i/Z.
```

La candidata respeta ambas dotaciones porque `sum_i v_i z_i=Z`; además, al evaluar **su producción original** se obtiene exactamente `Yeff`. El argumento prueba una **máxima producción global a factores totales dados**, no solo igualdades de productos marginales ni condiciones KKT necesarias.

## 5. Mapa de obligaciones Lean y evidencia

La infraestructura verificada previamente incluye:

- `PaperAllocationEfficiencySupportCandidate.normalized_two_type_output_le_benchmark`: cota global AM–GM de tres pesos.
- `PaperAllocationEfficiencySupportCandidate.efficient_candidate_clears_resources`: factibilidad del candidato.
- `PaperAllocationSourceAlgebraBridgeCandidate.productivity_weight_recovers_A`: recuperación de productividad.
- `PaperAllocationSourceAlgebraBridgeCandidate.positive_aggregate_loss_log_formula`: identidad de logaritmos positivos.
- `PaperOriginalLaborGlobalCandidate.original_two_type_labor_global_bound`: trabajo óptimo desde asignaciones originales con capital fijo.

Las nuevas declaraciones candidatas se dividen en tres módulos:

- `PaperJointEfficiencySourceCandidate.lean`: `normalized_source_firm_output` y `normalized_joint_scale_identity`.
- `PaperJointEfficiencyBoundCandidate.lean`: `normalized_two_type_source_output_le_efficient` y `source_resource_budget_normalizes`.
- `PaperJointEfficiencyPhysicalCandidate.lean`: `original_physical_two_type_joint_output_bound` y `original_physical_joint_candidate_attains_frontier`.

**Nota de estado:** las cuatro declaraciones de normalización/AM–GM y las dos declaraciones físicas end-to-end del óptimo conjunto de K/L están verificadas en sus tres corridas focalizadas, incluidas las de [CI #42502060253](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42502060253). Además, los dos teoremas de `PaperOriginalLogLossCandidate.lean` superaron esa última corrida. El enlace diferenciable completo de Loss permanece pendiente.

## 6. Qué faltará incluso después de CI verde

Primero, establecer en Lean la no negatividad de la pérdida **original** usando `0<Y<=Yeff` y la identidad logarítmica, para derivar `Loss=log(Yeff/Y)>=0` en un mismo enunciado que no suponga `Yeff` como definición tautológica.

Segundo, derivar efectivamente las derivadas de las funciones `K(k)` y `G(k)` para llegar a

```text
dLoss = a (kappa_H - omega_H) dlog(k_H/k_L)
```

en una trayectoria diferenciable de capital positivo con masas y tecnologías fijas. Ya está verificada el álgebra de los coeficientes, **no** todavía la diferenciación fuente completa.

Tercero, distinguir el lema productivo condicional de las proposiciones del paper sobre restricciones de colateral, solución dinámica, selección de ramas S/B y crecimiento permanente. Una mejora de la asignación productiva en un periodo no demuestra por sí sola un efecto causal de largo plazo.

**Regla de promoción:** no modificar `allocationLossIdentitySpec` en el checkpoint, no declarar `same_statement_proved` para el Lema 4.3 sin completar todas sus hipótesis y conclusiones, y no extrapolar CI verde de un SHA a otro.
