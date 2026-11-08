# Guía de comprobación manuscrita — Proposición principal y mecanismo de inversión

**Estado:** guía tipografiada de trabajo; **NO** constituye la evidencia
manuscrita del autor solicitada en el curso. No añadir un veredicto como
si ya se hubiera escrito o comprobado personalmente.

**Fuentes fijadas:** `paper/paper.tex`,
`paper/body_compact_intro.tex`,
`paper/body_compact_after.tex`, proposición
`prop:local_macro_multiplicity`;
`lean/candidates/Ventura26LiquidityAllocation/ScalarComplementarityMultiplicityCandidate.lean`.
El material técnico original permanece en el anexo del paper.

## 1. Hipótesis que hay que escribir antes de derivar

Sea M(s,h) una función real de clase C¹ en un entorno abierto del
origen. Exigir, literalmente:

1. M(0,0) = 0.
2. b := ∂M/∂s(0,0) < 0.
3. a_R := ∂M/∂h(0,0) < 0.
4. La holgura s está restringida a s ≥ 0.
5. Complementariedad: s ≥ 0, M(s,h) ≥ 0, s·M(s,h) = 0.
6. Se estudian solo soluciones locales, con h suficientemente pequeño.

La condición **M(0,0)=0** y la regularidad C¹ no pueden omitirse.
La demostración no dice que el mapa M concreto del equilibrio completo
exista con todas estas propiedades: esa identificación es otra obligación.

## 2. Paso A — Monotonía local, con la continuidad explícita

Por continuidad de ∂M/∂s y b<0, existe ε>0 tal que
∂M/∂s(s,h) < b/2 < 0 para |s|,|h|<ε (escoger una cota
estrictamente negativa correcta para b/2). Por continuidad
de ∂M/∂h y a_R<0, al reducir ε también
∂M/∂h(s,h) < a_R/2 < 0.

Aplicar el teorema del valor medio sobre segmentos del rectángulo
local. Para h fijo y 0 ≤ s1 < s2 < ε:

    M(s2,h) - M(s1,h)
       = ∂s M(ξ,h)·(s2-s1) < 0.

Por tanto M(·,h) es estrictamente decreciente **localmente**.
No afirmar monotonicidad en todo [0,+∞) sin una hipótesis adicional.

## 3. Paso B — Signo en la frontera para h<0

Para h<0 pequeño:

    M(0,h) - M(0,0)
       = ∂h M(0,η)·h > 0,

pues h<0 y ∂h M(0,η)<0. Como M(0,0)=0, resulta
M(0,h)>0. Entonces s=0 satisface las tres condiciones:

    s=0 ≥ 0;
    M(0,h)>0 ≥ 0;
    s·M(0,h)=0.

Este es el candidato de garantía activa (rama B);
no implica automáticamente dual estrictamente positivo
en el problema empresarial original sin el puente correspondiente.

## 4. Paso C — Raíz interior mediante la función implícita

Dado ∂s M(0,0)=b≠0, el teorema de la función implícita
produce una única función local diferenciable r(h) con:

    r(0)=0,   M(r(h),h)=0.

Diferenciar esta identidad con la regla de la cadena:

    ∂s M(r(h),h)·r'(h) + ∂h M(r(h),h) = 0.

Evaluar en h=0:

    b·r'(0) + a_R = 0,

por tanto

    r'(0) = -a_R/b < 0.

Verificar cuidadosamente el signo: a_R<0 y b<0,
de modo que -a_R>0 y -a_R/b<0.
Por definición de derivada, para h<0 pequeño
r(h)=r'(0)h+o(|h|)>0. Se debe justificar la
desigualdad eligiendo un entorno donde el término
o(|h|) sea menor en valor absoluto que
|r'(0)|·|h|/2.

La raíz r(h)>0 satisface
M(r(h),h)=0, r(h)≥0 y r(h)·M(r(h),h)=0;
es el candidato de garantía holgada (rama S).

## 5. Paso D — Exclusión de una tercera raíz

Por complementariedad, cualquier s≥0 debe satisfacer
s=0 **o** M(s,h)=0.
Por el Paso A, M(·,h) es estrictamente decreciente en
el intervalo local [0,ε), de modo que tiene a lo
sumo una raíz interior. El Paso C ya construyó esa
raíz. Hay exactamente dos **soluciones escalares locales**:
{0,r(h)} para h<0 suficientemente pequeño.

La prueba no cubre soluciones fuera del entorno.
La unicidad de la recuperación de las demás variables del
prefijo requiere otra aplicación de regularidad de su Jacobiano.

## 6. Paso E — Ausencia de raíces para h>0

El teorema del valor medio da M(0,h)<0 cuando h>0 pequeño.
Como M es decreciente en s en el intervalo local,
M(s,h)≤M(0,h)<0 para s≥0 cercano.
No puede cumplirse M(s,h)≥0; por tanto no hay
solución complementaria no negativa local para h>0.

## 7. Paso F — Diferencia exacta con Lean

El teorema Lean `scalar_complementarity_exactly_two` prueba,
con el kernel, que el conjunto de soluciones escalares es
{0,r} bajo:

- `StrictAntiOn M (Set.Ici 0)`, monotonicidad en el dominio no negativo;
- `r>0`, `M 0>0` y `M r=0` como **hipótesis explícitas**.

El lema NO construye r(h) por un teorema de función implícita,
NO demuestra b<0 y a_R<0 para el Schur complement financiero
real y NO prueba que existan asignaciones competitivas completas.
La prueba tipografiada del paper es más específica respecto al
parámetro h, mientras que el lema Lean tiene una hipótesis de
monotonía más fuerte sobre todo el semieje. No son
enunciados literalmente equivalentes.

**Veredicto que debe completar el autor, después de escribir a mano:**
indicar qué pasos aceptó, cuál requirió corrección, por qué las
hipótesis bastan para las raíces escalares, y por qué
no bastan para el equilibrio infinito.

## 8. Comprobación complementaria: crédito frente a capital

Escribir presupuesto sin depósitos de H y garantía activa:

    c + q k' = N + b,
    R^L b = H k'.

Sustituir b=Hk'/R^L:

    c + q k' = N + H k'/R^L
    (q-H/R^L) k' = N-c.

Definir n=N-c>0, p_eff=q-H/R^L>0; despejar:

    k'=n/p_eff;
    b=H n/(R^L·p_eff).

Aplicar logaritmos y tomar diferencias entre la trayectoria
perturbada y la referencia:

    Δlog k' = Δlog n - Δlog p_eff;
    Δlog b = Δlog H + Δlog k' - Δlog R^L.

Verificar manualmente los signos de las dos ramas con
`paper/irf_mechanism_table.tex`:
S: 0.00002735 + 0.00013674 = 0.00016409 (log %);
B: -0.00174198 + 0.00066934 = -0.00107264 (log %).

Los términos son identidades **sobre soluciones conjuntas**:
no son mecanismos causales aislados. La comparativa
de crédito y capital requiere precios y recursos endógenos.

## 9. Entrega manuscrita por completar

En hojas numeradas a mano, incluir definición, hipótesis,
Pasos A--F, las dos derivaciones de crédito/capital,
notación y fecha; adjuntar escaneo legible al directorio `hand/`.
Escribir además un párrafo de juicio personal sobre las
coincidencias y diferencias con el lema Lean. No presentar
esta guía tipografiada como el escaneo solicitado por el curso.
