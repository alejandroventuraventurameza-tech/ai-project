# IE Project 18 — compuerta de la regla de la cadena de 33 filas (11-XI-2026)

## Identidad matemática que corresponde verificar

Sean `F:U→R^33`, `psi:V→U`, `T:V→R^{33×33}` y `P` una matriz de permutación fija. Se plantea `H(z)=P T(z) F(psi(z))`. Para toda dirección `h∈R^33`, la derivada general es

`DH(z)[h]=P(DT(z)[h] F(psi(z)) + T(z) DF(psi(z)) Dpsi(z)[h])`.

**Solo si** `F(psi(z_*))=0`, el primer término desaparece, y queda

`DH(z_*)=P T(z_*) DF(psi(z_*)) Dpsi(z_*)`.

La identificación `G(z)=H(z)` para el operador económico Python `G` es una obligación distinta que exige igualdad de las 33 funciones, el calendario y los datos SOURCE. Una permutación y una transformación invertible construidas desde fórmulas candidatas no prueban por sí mismas esa igualdad.

## Prueba de regresión incorporada

El archivo `code/irf/test_operator_transport_chain_rule.py` contiene un ejemplo analítico **sintético**, de dimensión 33, con:

- una permutación no trivial de las filas;
- una carta positiva exponencial `psi_i(z)=B_i exp(z_i)`;
- funciones `F_i` afines acopladas entre coordenadas;
- factores diagonales dependientes del estado y dos shear Euler/garantía en posiciones `(19,21)` y `(20,21)`.

Compara las 1089 entradas del Jacobiano por diferencias centrales en tres puntos (3267 comparaciones). Impone una raíz común en `z=0`; fuera de ella construye un contraejemplo explícito a la eliminación incorrecta de `DT(z)[h]F(psi(z))`.

Ejecución aislada en entorno de cálculo, antes de registrar el archivo: **PASS**; máximo error central `1.96e-10`, testigo de error por omitir el producto `0.00643`. Esos números pertenecen al experimento sintético, no a la economía.

El workflow `editorial-qa.yml` ahora ejecuta ese test automáticamente. La ejecución GitHub del SHA nuevo debe cotejarse por separado.

## Brechas científicas abiertas

1. Definir funciones `F` de los 33 residuos literales SOURCE bajo la misma instancia `Primitives`, el mismo estado heredado y el mismo registro `LocalPrefixDateData`.
2. Definir la carta positiva `psi`, su dominio abierto, su inversa local y el orden literal de 33 coordenadas de Python.
3. Derivar `T(z)` a partir de las equivalencias funcionales verificadas: nueve filas escalares, dieciséis identidades y ocho empresariales, incluyendo los dos shears variables.
4. Comprobar `G(z)=P T(z)F(psi(z))` en una vecindad, no solo en un conjunto finito de puntos. Si queda un resto, se requiere `R(z_*)=0` y `DR(z_*)=0` para transportar el Jacobiano en la raíz.
5. Recién entonces estudiar regularidad de `DF`, las 34 relaciones KKT y las condiciones de optimalidad, terminalidad y equilibrio infinito.

**Estado:** el nuevo test certifica un mecanismo matemático general bajo sus propias funciones, no la equivalencia económica SOURCE/Python ni la invertibilidad del Jacobiano económico. Mantener PR #2 en borrador y no fusionar `main`.
