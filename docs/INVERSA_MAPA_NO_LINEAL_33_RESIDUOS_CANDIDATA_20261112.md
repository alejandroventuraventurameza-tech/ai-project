# IE Project 18 — inversa no lineal del mapa de 33 residuos SOURCE-shaped (12-XI-2026)

## Evidencia previamente verificada

La ejecucion `build` del commit `f62ff80915891acaf9df69ca71135a7d086bb4c2`, run [43270594635](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43270594635), completo `code/verify.py` correctamente tras corregir el nombre de importacion del mapa escalar. En ambas ramas, la auditoria `audit_frozen_33_offroot_nonlinear_transform.py` registro discrepancias maximas de `1.7763568394002505e-15` en los 33 residuos transcritos, `1.2231155758352097e-18` en las cizallas Euler y `1.7763568394002505e-09` en diferencias direccionales. Por separado, `audit_frozen_33_offroot_product_rule.py` registro discrepancia direccional maxima de `1.7763568394002505e-09` para 6534 entradas por rama, manteniendo los terminos derivados del denominador escalar y del coeficiente de Euler.

La magnitud maxima de esos terminos adicionales fue `0.001647410297480563` y `0.0002555167098590377`, respectivamente. Por tanto, omitirlos fuera de la raiz no es un detalle inocuo.

## Nueva pregunta: ¿es reversible la transformacion de residuos?

Sea `p\in R^33` el vector residual Python, `s\in R^33` el candidato SOURCE-shaped en orden SOURCE, `d_i(z)>0` los denominadores escalares y `a_i(z)` los coeficientes de cizalla Euler. El nuevo auditor `audit_frozen_33_offroot_rowmap_inverse.py` implementa el mapeo inverso para **z fijo**:

- En nueve filas escalares: `s_i=epsilon_i*d_i(z)*expm1(p_{j(i)})`.
- En dos Euler de fecha uno: `s_i=p_{j(i)}+a_i(z)*expm1(p_{j(21)})`.
- En las restantes veintidos filas: `s_i=p_{j(i)}`.

La inversa funcional se obtiene con las formulas logaritmicas y de cizalla del auditor no lineal anterior. Se comprueba la ida y vuelta `s -> p -> s` y `p -> s -> p` en 30 evaluaciones (15 por rama), manteniendo el mismo estado congelado, `P0`, intervenciones y carta.

El Jacobiano **con respecto a los residuos p** del mapa inverso tiene una unica entrada diagonal no nula por fila, con las dos entradas extra de cizalla. En filas escalares la diagonal es `epsilon_i*d_i(z)*exp(p_{j(i)})`, distinta de cero en la carta positiva. En las filas Euler la entrada adicional en la columna de pignoracion es `a_i(z)*exp(p_{j(21)})`. El auditor construye tanto esa matriz 33×33 como su inversa exacta a nivel de formulas candidatas y comprueba ambos productos numericos.

Este resultado, si pasa CI, demostrara **por algebra del mapa candidato** que la transformacion residual es localmente invertible siempre que los denominadores escalares sean positivos. El test se realiza en float64, por lo que sus residuales de inversa siguen siendo numericos.

## Distincion fundamental

La matriz residual `D_p S_z(p)` NO es la derivada economica `D_z F_SOURCE(z)`. Para la composicion total de funciones se debe incluir la variacion de `d_i(z)`, `a_i(z)` y cualquier otra dependencia explicita de z. Ademas, las filas `s_i` siguen siendo transcripciones SOURCE-shaped en Python, no valores de las definiciones SOURCE Lean originales.

Es incorrecto afirmar invertibilidad del Jacobiano economico, existencia de raiz para la rama holgada, validez de `tail=P0` en el modelo infinito o crecimiento permanente a partir de la invertibilidad de un cambio de residuos.

## Estado de compuerta

El nuevo test se agrego a `code/verify.py` y se archiva como `frozen-33-source-shaped-offroot-rowmap-inverse` desde `build.yml`. **Pendiente de nuevo resultado CI del SHA de esta integracion.** PR #2 permanece draft, sin fusionar `main`.
