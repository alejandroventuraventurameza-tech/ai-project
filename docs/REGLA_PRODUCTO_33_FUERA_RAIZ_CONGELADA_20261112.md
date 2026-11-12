# IE Project 18 — derivadas fuera de la raiz y terminos omitidos del puente 33×33 (12-XI-2026)

## Punto de partida

El run `43269336216` del commit `0231e48c503e92199eed645fb1692e133079677a` valido numericamente el candidato `J_py(0) = T0 J_SOURCE-shaped(0)`: el error maximo en las 1089 entradas fue `6.01e-10` a paso `2e-5`, `1.33e-9` a `2e-6` y `4.44e-9` a `2e-7`. No es un teorema de SOURCE Lean.

## Transformacion funcional no lineal candidata

El modulo `audit_frozen_33_offroot_nonlinear_transform.py` construye las 33 filas candidatas de SOURCE en una base `frozen_stationary_seed(steady_case())`, con rama `binding` o `slack`, y las lleva a los residuos originales de `finite_irf.prefix_residual` mediante una transformacion **no lineal**.

Para nueve filas escalares, con `s_i(z)=epsilon_i*d_i(z)*(exp(g_i(z))-1)` y `d_i(z)>0`, la reconstruccion logaritmica es `g_i(z)=log1p(epsilon_i*s_i(z)/d_i(z))`.

Para dos Euler de fecha uno, `p_E,i(z)=s_E,i(z)-a_i(z)*s_P(z)/d_P(z)` donde `s_P(z)` es el residuo SOURCE-shaped de pignoracion nominal comun y `d_P(z)` su factor positivo. El coeficiente `a_i(z)` cambia con el punto del estado.

Las restantes filas se reconstruyen bajo una permutacion fija, sin transformar su nivel.

## Por que no podemos transportar el Jacobiano con una matriz constante fuera de la raiz

En filas escalares, con `u(z)=epsilon*s(z)/d(z)`, se tiene

`Dg(z)[v] = [epsilon*Ds(z)[v]/d(z) - epsilon*s(z)*Dd(z)[v]/d(z)^2] / (1+u(z))`.

El termino proporcional a `s(z)*Dd(z)[v]` solo desaparece cuando el residuo en niveles es cero.

Para filas Euler:

`Dp_E(z)[v] = Ds_E(z)[v] - Da(z)[v]*s_P(z)/d_P(z) - a(z)*{Ds_P(z)[v]/d_P(z) - s_P(z)*Dd_P(z)[v]/d_P(z)^2}`.

El termino proporcional a `Da(z)` y el que incluye `Dd_P(z)` desaparecen en una raiz comun de pignoracion, pero son necesarios para interpretar diferencias finitas fuera de ella.

El script `audit_frozen_33_offroot_product_rule.py` implementa **estas derivadas completas** a nivel de transcripciones candidatas. Compara sus 33 entradas por cada direccion coordinada con las derivadas centrales de los residuos originales Python en dos perturbaciones no triviales, tres configuraciones de politica y ambas ramas. Los hashes de SOURCE, Python y P0 quedan registrados. El test falla si la discrepancia maxima supera `5e-7`.

## Estado epistemico

La compuerta transversal `build` verificara el script y archivara el JSON `frozen_33_offroot_explicit_product_rule.json`. Al momento de este commit su resultado es PENDIENTE; no debe declararse NUMERICO VERIFICADO sin observar `success`.

Incluso un exito numerico completo **no** demuestra que `F_SOURCE` original en Lean sea igual a `F_source_transcrito` en un abierto. Tampoco certifica la identificacion de historia y calendario, la regla de continuacion `tail`, la invertibilidad del Jacobiano economico, KKT, cierre fiscal, equilibrio infinito o consecuencias de crecimiento permanente.

## Siguiente puerta matematica

Probar una igualdad definicional o por lemas SOURCE entre los campos `Primitives`, `InheritedState`, `LocalPrefixDateData` y las reconstrucciones Python, seguidas por una identidad fuente de las 33 funciones en la misma carta y la misma regla terminal. Solo despues se debe construir el certificado de Jacobiano por desigualdades rigurosas, no por productos float64.

PR #2 permanece draft y `main` sin fusionar.
