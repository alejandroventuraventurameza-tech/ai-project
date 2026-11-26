# IE Project 18 — candidato matricial completo 33×33 en raiz estacionaria congelada (12-XI-2026)

## Insumos verificados

En el commit `8021359bb30a7d1f543136ecd8d4b4f61ece6668`, el workflow `build` [43268907008](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43268907008) termino `success` y ejecuto la auditoria de nueve filas escalares en la misma raiz estacionaria vinculante congelada. Sus errores maximos de normalizacion por diferencias centrales fueron `6.010898445651947e-10` (`2e-5`), `3.495692624255753e-11` (`2e-6`) y `3.151526817291028e-10` (`2e-7`). El residuo Python de referencia fue `3.552713678800501e-15`.

Los diagnosticos anteriores incluyen particion exacta de 8 filas de firmas, 16 filas adicionales y 9 filas escalares, siempre sobre `frozen_stationary_seed(steady_case())` y con el mismo `P0`. Todos son *transcripciones SOURCE-shaped en Python*, no evaluaciones ejecutadas del operador SOURCE real en Lean.

## Nueva compuerta matricial

Se creo `code/irf/audit_frozen_33_root_candidate_matrix_bridge.py`. En lugar de cotejar por separado los tres grupos, reconstruye un vector completo de **33 residuos candidatos en orden SOURCE**, a partir de los tres transcriptores ya auditados:

- ocho residuos de firmas, incluidos los dos Euler con cizalla;
- dieciseis filas adicionales que coinciden con la forma residual Python bajo la transcripcion;
- nueve filas en niveles, con residuos positivos/logaritmicos.

Se usa la rama `binding` y el punto `z=0`, que es un cero numerico de ambos vectores candidatos. No se afirma que ese punto sea raiz de la rama `slack`, ni se utiliza `make_boundary(s)`.

## Forma de la matriz de transformacion

Sean `F_src_candidate(z)` los 33 residuos transcritos en orden SOURCE y `F_py(z)` los residuos originales de `finite_irf.prefix_residual`. La matriz `T0` es una matriz 33×33 con la permutacion SOURCE–Python:

1. Las nueve filas escalares contienen el factor `epsilon_i / d_i(0)` de la identidad `s_i(z)=epsilon_i d_i(z) expm1(g_i(z))`.
2. Las dieciseis filas restantes y las seis firmas directas tienen multiplicador unitario.
3. En las dos filas de Euler de fecha uno se incorpora la cizalla de pignoracion `T0[pythonEuler_i,sourcePledge] = -a_i * T0[pythonPledge,sourcePledge]`, donde `a_i` es el coeficiente calculado en la misma raiz.

Con los parametros de la transcripcion, la inversa algebraica candidata tiene factores reciprocos en los pares de indices y coeficientes `+a_i` sobre las correspondientes filas Euler. El script construye `T0` y su inversa, comprueba ambos productos contra la identidad y estima mediante diferencias centrales:

`J_py(0) ?= T0 * J_src_candidate(0)`.

Se contrastan las **1089 entradas** de ambas matrices y se repite la prueba a los pasos `2e-5`, `2e-6` y `2e-7`, manteniendo la misma carta. El umbral de discrepancia maxima de Jacobiano candidato es `5e-6`; el de productos matriciales es `1e-12`. Estos son umbrales float64 para regresion, **no** cotas de redondeo rigurosas.

## Advertencia conceptual decisiva

El producto `T0*J_src_candidate` solo es valido en la raiz comun, por lo que los terminos de regla del producto proporcionales a los residuos se anulan. El transformador completo en una vecindad es dependiente del estado y debe incluir escalas no lineales `expm1` y cizallas Euler variables.

Una eventual identidad de matrices entre **transcripciones** no demuestra por si misma la igualdad del operador Lean SOURCE con Python. El script conserva banderas explicitas en `false`: `original_SOURCE_Lean_operator_executed`, `original_SOURCE_fderiv_equal_to_transcription_proved`, `full_SOURCE_Python_functional_identity_proved` y `original_SOURCE_Jacobian_invertibility_certified`.

## Siguientes obligaciones

Primero comprobar el nuevo `build` del SHA con el script. Despues auditar identidad funcional en una vecindad del operador original Lean SOURCE con la transcripcion, incluidas las reglas de terminalidad `tail` y carta `psi`; finalmente construir una cota certificada de inversa del Jacobiano economico real. Permanecen pendientes cierre fiscal, KKT, equilibrio infinito y crecimiento permanente.

PR #2 continua en borrador; no fusionar `main`.
