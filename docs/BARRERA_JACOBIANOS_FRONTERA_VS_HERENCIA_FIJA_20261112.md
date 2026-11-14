# IE Project 18 — barrera de procedencia del Jacobiano: frontera S/B versus predecesor fijo (12-XI-2026)

## Diagnóstico de una diferencia irreductible entre las evidencias disponibles

Se utilizan dos problemas numéricos con bases distintas:

**A. El transformador candidato de las filas SOURCE (`audit_source_full_transform_candidate.py`).** Las clases de filas se dividen en nueve factores de escala, dieciséis filas candidatas identidad y ocho filas de firmas, incluidas dos cizallas de Euler. El script construye su transformación con las sendas por rama y las soluciones que derivan de `make_boundary(s)`, una frontera de conmutación entre los regímenes S y B. El informe declara explícitamente `distinct_frozen_same_predecessor_roots_studied_here=false`. El candidato T invertible **no** demuestra un puente funcional SOURCE/Python ni identifica la derivada SOURCE.

**B. El Jacobiano Python numérico congelado (`audit_frozen_python_jacobian_float_diagnostic.py`).** Se usa `frozen_stationary_seed(steady_case())`, rama `binding`, innovaciones directas nulas de fecha cero y fecha uno, cuatro intervenciones iguales a cero y la regla terminal lineal `P0`. El jacobiano `A_py` de 33×33 se estima por diferencias centrales con tres pasos y se calcula una inversa flotante aproximada. Ni la derivada exacta ni la identificación SOURCE están certificadas.

Por ello, aunque cada reporte individual pase su compuerta, **no es legítimo multiplicar la matriz inversa de B por el transformador T de A para anunciar una inversa del Jacobiano económico SOURCE**. Falta identificar la misma base, el mismo calendario, la misma rama y una misma regla `tail` en una carta positiva común.

## Nueva compuerta transversal ejecutable

Se añadió `code/irf/audit_jacobian_cross_baseline_firewall.py`, ejecutado desde `code/verify.py`, que:

1. exige las procedencias de las tres evidencias, incluido el nombre del estado estacionario congelado Python y la anotación explícita del transformador candidato de frontera;
2. coteja hashes SHA-256 del SOURCE, Python y matriz de continuación;
3. asegura que las banderas `source_jacobian_equality_proved`, `source_functional_identity_proved`, `interval_inverse_enclosure_proved` y las certificaciones del informe de preparación siguen en `false`;
4. exige que los productos de inversa flotantes del diagnóstico se mantengan bajo el umbral publicado, sin reinterpretar ese umbral como error certificado;
5. produce `code/irf/output/jacobian_provenance_cross_baseline_firewall.json`, adjuntado por GitHub Actions como `source-python-jacobian-cross-baseline-firewall`.

La barrera es deliberadamente **fail-closed**: una nueva afirmación de certificación en los reportes requerirá cambiar explícitamente el contrato de prueba y aportar evidencia sustantiva. No confiere ninguna igualdad ni inversibilidad al Jacobiano SOURCE.

## Ecuación de transporte todavía abierta

Para que la transformación de filas permita trasladar una inversa, necesitamos demostrar en una vecindad abierta y alrededor del MISMO punto base

`F_py(z)=T(z) F_source(psi(z))`,

donde la carta `psi` identifica las 33 coordenadas, y T incorpora correctamente las escalas de raíz y las cizallas Euler. La regla de la cadena general es

`D F_py(z0)=D T(z0)[·] F_source(psi(z0))+T(z0) D F_source(psi(z0)) D psi(z0)`.

Solo **si** `F_source(psi(z0))=0`, desaparece el término de la derivada de T. Esta condición es especialmente importante para las filas con coeficientes de cizalla dependientes del estado. Una multiplicación matricial sin ese término fuera de la raíz sería incorrecta.

Si se demuestra además que T(z0) y D psi(z0) son invertibles y A_py es el Jacobiano **exacto**, entonces se podría inferir algebraicamente la inversibilidad de D F_source. En nuestro estado actual, ni esas igualdades económicas ni las cotas de inversa y el error de diferencias finitas han sido certificados.

## Estado de evidencia

- **DEMOSTRADO:** invariancia fiscal del operador reducido SOURCE, sus Jacobianos y lugares de ceros en las hipótesis del módulo Lean revisado.
- **NUMERICO/PENDIENTE DE CI:** diagnóstico del Jacobiano Python congelado.
- **AUDITORIA DE PROCEDENCIA/PENDIENTE DE CI:** nueva compuerta contra la combinación de bases distintas.
- **PENDIENTE:** identidad funcional SOURCE/Python a misma base, regla terminal exacta, cota rigurosa de inversa, KKT y equilibrio infinito.

PR #2 sigue borrador; no fusionar `main`.
