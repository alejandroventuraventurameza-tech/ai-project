# IE Project 18 — igualdad exacta fuera de raíz para la obligación bancaria

Fecha: 11 de noviembre de 2026. Estado: **identidad analítica demostrable por cálculo elemental, prueba numérica agregada pero CI pendiente de corroborar**.

## Objeto económico y su límite

El expediente `docs/PUENTE_RENOVACION_BANCARIA_SOURCE_PYTHON_20261110.md` recoge dos expresiones de la obligación nominal bancaria:

- nivel: `F(z)=A(z)-D(z)`;
- logaritmo: `G(z)=log(A(z)/D(z))`, con `A,D>0`.

La equivalencia funcional exacta en la carta positiva es

`F(z)=D(z)*expm1(G(z))`.

Así, `F(z)=0` si y solo si `G(z)=0`. Diferenciando en una dirección `h`:

`DF(z)[h]=expm1(G(z))*DD(z)[h]+D(z)*exp(G(z))*DG(z)[h]`.

En la raíz común, `G(z*)=0` y `DF(z*)=D(z*)*DG(z*)`. **Fuera de la raíz NO es lícito sustituir `DF=D*DG`**: falta el término en `DD` y el factor `exp(G)`.

La transformación funcional precisa de la fila, en la orientación `G` como función de `F`, también puede expresarse como

`G(z)=c(z)*F(z)`, con `c(z)=log1p(F(z)/D(z))/F(z)` cuando `F(z)!=0` y `c(z)=1/D(z)` cuando `F(z)=0`.

El cociente `log1p(u)/u` posee una extensión suave en `u=0`, y `c(z)>0` en toda la carta `A,D>0`. Por tanto, la transformación de fila escalar es invertible sobre esa carta, sin suponer que `D` sea constante.

## Prueba independiente agregada

`code/irf/test_bank_face_offroot_log_level.py` introduce funciones afines sintéticas `A(z),D(z)` sobre `R^33`, con dominios positivos. Para 24 configuraciones y 33 direcciones (792 combinaciones), compara la identidad exacta, las derivadas analíticas y diferencias centrales, y exige un testigo donde la omisión del término fuera de raíz produzca una discrepancia estricta. El workflow `editorial-qa.yml` ejecuta ese script junto con el regresor de la matriz `T`.

La prueba *sintética* no identifica automáticamente `A,D` con los operadores originales de `EconomicModel.lean` y `finite_irf.py`, ni demuestra la igualdad de todas las 33 filas. Deben cotejarse las expresiones originales, el registro `LocalPrefixDateData`, las coordenadas, el calendario y el factor bancario `a_B` en el **mismo estado heredado y rama**.

## Próximo paso

Construir una comparación del lado SOURCE y del lado Python que evalúe explícitamente `A(z)`, `D(z)` y sus derivadas bajo la misma carta positiva; repetir luego con cada una de las otras 32 filas. La equivalencia funcional de todas las filas y un certificado de invertibilidad del Jacobiano del SOURCE siguen pendientes. Un test numérico verde tampoco demuestra globalidad ni equilibrio infinito.

PR #2 permanece borrador y `main` intacta.
