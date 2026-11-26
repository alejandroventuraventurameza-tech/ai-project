# IE Project 18 — transferencia funcional no lineal de 33 filas fuera de la raiz (12-XI-2026)

## Resultado numerico anterior confirmado

El workflow `build` del commit `0231e48c503e92199eed645fb1692e133079677a`, ejecucion [43269336216](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43269336216), concluyo correctamente. En la raiz congelada vinculante se compararon las 1089 entradas de dos matrices 33×33 derivadas por diferencias centrales. Los errores maximos de la igualdad candidata `J_py ≈ T0 J_src_transcrito` fueron `6.010898445651947e-10`, `1.3322676295501878e-09` y `4.440892098500626e-09` para los pasos `2e-5`, `2e-6` y `2e-7`. Los dos productos de la matriz candidata `T0` y su inversa difirieron de la identidad a lo sumo `8.673617379884035e-19` y `0`, respectivamente.

El Jacobiano SOURCE en ese diagnostico se define **por transcripcion SOURCE-shaped ejecutada en Python**. No es la derivada original del operador Lean.

## Nuevo contrato funcional fuera de la raiz

Se anadio `code/irf/audit_frozen_33_offroot_nonlinear_transform.py`. En una base estacionaria congelada unica, con dos ramas (`binding`, `slack`), cinco anuncios de politica (ninguno y los cuatro instrumentos separados) y tres puntos logaritmicos, se construye un vector de 33 filas candidatas en el orden SOURCE mediante las tres familias de transcriptores ya auditadas.

La transformacion `R(z)` que reconstruye los 33 residuos Python **no** emplea `prefix_residual`; solo toma el vector SOURCE transcrito, los denominadores positivos de la carta y los coeficientes de cizalla de los empresarios. El contraste final se hace contra el motor original Python `prefix_residual`.

Para cada una de las nueve filas escalares, si el residuo en niveles es `s_i(z)=epsilon_i*d_i(z)*(exp(g_i(z))-1)`, entonces se reconstruye

`g_i(z)=log1p(epsilon_i*s_i(z)/d_i(z))`.

Es una transformacion *no lineal exacta en dominio positivo*. No se sustituye por el multiplicador `epsilon_i/d_i(0)` salvo para derivadas **en la raiz**.

Para las dos filas Euler de las firmas en fecha uno, la transcripcion da

`s_E,i(z)=p_E,i(z)+a_i(z)*(J(z)/A(z)-1)`,

donde `J(z)` es la promesa nominal comun y `A(z)` el valor de pignoracion fisica. Por tanto,

`p_E,i(z)=s_E,i(z)-a_i(z)*[s_pledge(z)/A(z)]`.

La cizalla incluye los coeficientes **dependientes de la posicion z** y reproduce el efecto de `expm1` sin utilizar una matriz constante fuera de la raiz. Las otras 22 filas candidatas son identidades bajo la permutacion SOURCE/Python.

El auditor calcula discrepancias de las 33 filas en 15 combinaciones (choque, estado) por rama y diferencias centrales sobre las 33 direcciones para tres intervenciones seleccionadas, incluyendo encaje y tasa monetaria. Exige tolerancias maximas `2e-10` para filas y cizallas, y `5e-7` para las comparaciones direccionales. Guarda SHA256 de la fuente Lean, del motor Python, de P0 y de los tres transcriptores.

## Limites de la evidencia

La etiqueta del informe JSON es `NUMERICAL_NONLINEAR_33_SOURCE_SHAPED_OFFROOT_TRANSFORM_ONLY`. Los cuatro campos `original_lean_source_operator_executed`, `original_source_to_python_functional_equivalence_proved`, `original_lean_source_jacobian_certified` y `branch_slack_equilibrium_root_proved` deben mantenerse `false`.

Este trabajo no constituye una identidad funcional demostrada del SOURCE original. Una transcripcion basada en codigo Python puede reproducir formulas Python con precision de maquina sin garantizar que una definicion fuente Lean sea economicamente identica. En particular falta identificar formalmente `Primitives`, `InheritedState`, historia inicial, calendario de anuncios, coordenadas positivas, funciones auxiliares y continuacion terminal `tail` con la grafica racional `P0`.

El objetivo posterior es demostrar —en Lean y bajo condiciones de dominio— la igualdad de funciones economicas originales, no solamente las transcripciones. Solo entonces podremos trasladar la derivada de Frechet y certificar su inversa mediante cotas estrictas.

## Estado

Se incorporo el nuevo script a `code/verify.py` y su JSON se archiva desde `build.yml`. **PENDIENTE de verificar el resultado de CI del SHA que incluye el auditor**. PR #2 continua en borrador, sin fusionar `main`.
