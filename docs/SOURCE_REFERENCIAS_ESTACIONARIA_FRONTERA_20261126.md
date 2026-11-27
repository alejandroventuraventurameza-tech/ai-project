# Auditoría de referencias: SOURCE estacionario exacto frente a la frontera numérica heredada

**Objeto.** Evitar identificar sin prueba dos centros distintos del problema financiero monetario. Esta nota establece una discrepancia de tasas que puede auditarse en el código y en Lean; no presenta una nueva calibración, una nueva IRF ni un equilibrio adicional.

## A. Referencia SOURCE fijada y demostrada en Lean

Los módulos `CurrentPinnedStationaryPrefix33Root.lean`, `CurrentPinnedFiscalFiberWitness.lean`, `CurrentPinnedJointQuantitativeBall.lean` y `CurrentPinnedRationalBall.lean` trabajan con el testigo estacionario SOURCE fijado en la carta de 33 coordenadas logarítmicas, bajo el mismo operador y continuación P0, y demuestran: raíz vinculante de 33 filas en `z=0`; fibra fiscal `G*=2 Mpre` con dominio monetario y cierre contable; dual de la firma L estrictamente positivo y obstrucción de raíz aumentada dual-cero para todo `G,h` en la bola `||z||∞<r_joint`. La cota certificada del PR #45 es

```text
R_L < 81/80 = 1.0125,       1/200 < r_joint.
```

Estas conclusiones son **sobre el testigo estacionario exacto**, no sobre cualquier punto que otra simulación denomine “estacionario” o “frontera”. No suponen invertibilidad económica del Jacobiano de 33 filas.

## B. Referencia numérica de frontera heredada

El productor `code/v0m/cierre_interno_2026_10_17/finite_bridge.py`, función `make_boundary()`, define una búsqueda escalar:

```python
lo, hi = D("1.025"), D("1.032")
assert scalar_boundary(s, I(lo))[0].x.hi < 0
assert scalar_boundary(s, I(hi))[0].x.lo > 0
```

La variable `R` allí es una **tasa bruta de préstamo**: `scalar_boundary(s,R)` la transmite al préstamo, y la construcción resultante utiliza `U0[8]=z["R"]`. La búsqueda parte de `R ∈ [41/40,129/125]`, esto es `[1.025,1.032]`. Se trata de un **candidato generado mediante aritmética de intervalos** y una ecuación escalar de frontera. No es, por ese hecho, el mismo objeto que `ProposedStationaryBank.loanRate` en la referencia Lean exacta.

En `code/v0m/certified_ift/audit_augmented_34.py`, la auditoría aumenta las 33 relaciones numéricas con la condición de dual cero y libera `h=v_R` como incógnita adicional. Su contrato reconoce expresamente:
```text
source_Lean_semantic_identity_proved = False
uniform_box_contains_Lean_actual_derivatives_proved = False
exact_zero_center_proved = False
formal_Lean_IFT_witness_established = False
```
El control de contracción es **aritmético y condicional a la validez semántica** de las cajas. No acredita igualdad con el SOURCE estacionario fijado ni un equilibrio dinámico completo.

## C. Prueba de separación y consecuencia lógica

Dado que `41/40 > 81/80`, un valor `R` que satisface `R≥41/40` no puede coincidir con la tasa fijada `R_L<81/80`. En unidades brutas la separación entre las cotas es al menos `41/40 - 81/80 = 1/80`, aunque no es una distancia entre todos los estados de los dos modelos.

El módulo `CurrentPinnedReferenceSeparation.lean` formaliza exactamente la desigualdad y la incompatibilidad **condicional al intervalo del productor heredado**. No formaliza el productor Python ni su encierro.

**Conclusión:** no existe contradicción entre (i) excluir toda frontera dual-cero en `||z||∞<1/200` alrededor del testigo Lean y (ii) tener un *candidato condicional* de frontera casi centrado en su propia referencia numérica. Son dos referencias que no deben identificarse. Si se pretende trasladar el antiguo candidato al testigo exacto SOURCE, debe probarse un mapa económico/paramétrico explícito; bajo la identificación directa de la tasa de préstamo, las cotas anteriores ya muestran que esa identificación es imposible.

## D. Obligaciones de cierre

- Fijar en los productores y JSON el identificador de la referencia, operador exacto, unidades de `R`, `G`, estado heredado, ley de pagos, continuación P0 y SHA del código.
- Comparar fila por fila el operador aumentado de 34 ecuaciones en el mismo centro, antes de reutilizar cualquier caja Jacobiana, norma o derivada de política.
- No trasladar `1/200` al candidato numérico ni transferir los signos del Schur del candidato antiguo al testigo Lean sin la prueba de igualdad semántica.
- Si el objetivo es probar existencia de una frontera de régimen, construirla **fuera** de la bola SOURCE certificada y justificar su economía y su continuación; el PR #43 impone solamente una condición necesaria de desplazamiento.
- Mantener separadas la comprobación de un sistema de ecuaciones finito, la suficiencia de KKT y la existencia de equilibrio competitivo infinito.

**Estatus:** separación algebraica Lean propuesta en revisión; evidencia numérica histórica condicional; puente SOURCE–Python pendiente. Actualizar esta última etiqueta únicamente tras compilación especializada y auditoría de axiomas.
