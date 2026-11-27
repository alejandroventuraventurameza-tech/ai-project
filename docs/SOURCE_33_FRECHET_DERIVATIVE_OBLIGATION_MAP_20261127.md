# SOURCE-33 — mapa de obligaciones para la derivada Fréchet económica original

**Corte técnico:** 26 de noviembre de 2026, horario de Lima.  
**Objeto:** prefijo vinculante de 33 ecuaciones originales y continuación P0 estacionaria.  
**No se atribuye** a este mapa la construcción de un equilibrio dinámico infinito, una IRF certificada o la igualdad funcional con finite_irf.py.

## 1. Problema matemático exacto

Para la carta logarítmica de estados y controles de dimensión 33, el objeto por demostrar es

\[
F_G(z)=
\operatorname{localReducedPrefixLogResidualVector}
(\mathrm{binding},P(G),I(G),Z_*,\mathrm{dateOne},
\mathrm{recurrent},\mathrm{tail}_{P0})(z).
\]

Se cuenta con una raíz exacta \(F_G(0)=0\) para el testigo estacionario y la fibra fiscal certificada. Falta demostrar en Lean

\[
\mathrm{HasFDerivAt}\,F_G\,J_G\,0,
\qquad
J_G\in\mathcal L(\mathbb R^{33},\mathbb R^{33}),
\]

y, adicionalmente, la regularidad C1 en una vecindad abierta del origen (o las hipótesis precisas del IFT que se invoque). Solo después corresponde proporcionar la identidad de dos lados y la cota de norma de su inversa.

Ningún lema de continuidad de una fila, ni la invertibilidad del shear bancario, demuestra la existencia o invertibilidad del Jacobiano económico original.

## 2. Inventario de las 33 filas SOURCE

Los índices son los índices reales cero-basados de Fin 33 en EconomicModel.lean, en el orden de localPrefixEquationOfIndex.

| Índices | Ecuaciones económicas | Compuerta de derivabilidad |
|---|---|---|
| 0–1 | Presupuestos de firmas H y L, fecha 0 | Precios, caras nominales, préstamos y riqueza de firmas |
| 2–3 | Euler de capital H y L vinculantes, fecha 0 | Potencias reales, productividad marginal, colateral y descuento |
| 4–5 | Régimen de colateral H y L, fecha 0 | Pignorabilidad, capital, cara prometida y multiplicadores implícitos |
| 6 | Patrimonio bancario, fecha 0 | Precios brutos, inflación y financiación |
| 7 | Oferta de capital, fecha 0 | Capital agregado, inversión y coste de ajuste |
| 8 | Recursos agregados, fecha 0 | Producción y trabajo endógenos, costes Rotemberg y capital |
| 9 | Oferta laboral del hogar, fecha 0 | Potencias positivas de trabajo y consumo |
| 10 | Euler de depósitos del hogar, fecha 0 | Consumo positivo y factor de descuento estocástico |
| 11 | Curva de Phillips neokeynesiana, fecha 0 | Producto y producto siguiente, cocientes e inflación |
| 12–13 | Reglas monetarias de tasa y cantidad, fecha 0 | Logaritmos de variables positivas y metas monetarias |
| 14–15 | Fijación de tasas de préstamo y depósito, fecha 0 | Pendientes OTC, reservas y corredor |
| 16 | Balance bancario, fecha 0 | Razones depósitos/reservas y financiación monetaria |
| 17–18 | Presupuestos de firmas H y L, fecha 1 | Continuación P0 y fechas/estados heredados |
| 19–20 | Euler de capital H y L vinculantes, fecha 1 | Potencias reales, próxima productividad, colateral |
| 21 | Valor de prenda común, fecha 1 | Depreciación, inflación y precio del capital |
| 22 | Patrimonio bancario, fecha 1 | Capital bancario, tasa de préstamo y roll-over |
| 23 | Oferta de capital, fecha 1 | Tecnología de creación y stock heredado |
| 24 | Recursos agregados, fecha 1 | Producción original, oferta endógena de trabajo |
| 25 | Oferta laboral del hogar, fecha 1 | Utilidad marginal, salario real y trabajo |
| 26 | Euler de depósitos del hogar, fecha 1 | Consumo siguiente y descuento |
| 27 | Curva de Phillips, fecha 1 | Rotemberg y periodo siguiente P0 |
| 28–29 | Reglas monetarias de tasa y cantidad, fecha 1 | Metas y rezagos exactos SOURCE |
| 30–31 | Tasas de préstamo y depósito, fecha 1 | OTC y ratios bancarios |
| 32 | Balance bancario, fecha 1 | Razones realizadas/objetivo y cantidad de reservas |

## 3. Dominio de suavidad y operaciones críticas

La carta \(Z_j(z)=Z_{*,j}\exp(z_j)\) es estrictamente positiva en las 33 coordenadas con bases económicas positivas. Esto resuelve las no anulaciones de muchas tasas y denominadores, pero deben certificarse independientemente las razones bancarias y las funciones compuestas.

- **Potencias y Cobb–Douglas.** La demanda de trabajo usa \(K_i^\alpha\) y \(1/(1-\beta)\), con \(\alpha=2/5,\beta=1/2\). Los márgenes de salarios, capital y precios son positivos en la carta.
- **Logaritmos monetarios.** Las tasas y cantidades realizadas/objetivo son estrictamente positivas; las metas son funciones exponenciales. La continuidad de los cuatro residuos monetarios está siendo tratada separadamente, pero la diferenciabilidad requiere una prueba más fuerte.
- **OTC.** Las fórmulas de pendientes contienen \(\sqrt{2-\vartheta}\). En la vecindad estricta \(\vartheta<1\) se verifica \(2-\vartheta>1\), condición suficiente para derivar expresiones de raíz cuadrada con reglas estándar de Mathlib.
- **Balances bancarios.** Las razones realizadas y objetivo admiten en la región certificada cotas estrictas superiores a \(2/25\); sus inversos pueden tratarse sin singularidad local.
- **Expectativas y sumas.** La ley de pagos de soporte binario y los dos tipos de firmas permiten sustituir expectativas por sumas finitas, siempre preservando las masas originales.
- **Continuación.** Debe probarse que el operador P0 congelado es C1 respecto de las seis variables de estado y sus controles logarítmicos, no suponerse porque la continuación sea estacionaria en el punto cero.

## 4. Estrategia de prueba incremental

**G1 — Atlas de coordenadas y dominio.** Probar positividad y continuidad diferenciable de todas las variables reales originales que entran en cada una de las 33 filas; identificar por separado las derivadas de las seis variables de continuación.

**G2 — Funciones de firmas y hogar.** Construir las derivadas Fréchet de trabajo, producción, salarios, recursos y condiciones de Euler. Evitar confundir condiciones necesarias de optimalidad con existencia de un equilibrio.

**G3 — Módulos monetarios y bancarios.** Probar las derivadas de los logaritmos de metas, el factor OTC y las cuatro razones bancarias. La continuidad y la raíz monetaria no bastan por sí solas para dar una derivada.

**G4 — Ensamblaje de las 33 filas.** Usar la igualdad de vectores en Fin 33 para construir un operador lineal continuo J_G y demostrar HasFDerivAt F_G J_G 0, fila por fila. Además, demostrar diferenciabilidad en una vecindad abierta y continuidad local de la derivada, o directamente ContDiffAt de orden 1; la derivada puntual aislada NO basta para el teorema estándar de función implícita. Registrar cada fórmula, signo y unidad.

**G5 — Inversa y validación.** Obtener una matriz explícita exacta o intervalar con producto izquierdo/derecho igual a la identidad, junto con una cota de norma rigurosa. La matriz numérica de un centro de frontera histórico no puede atribuirse sin identificación al testigo estacionario SOURCE actual.

**G6 — IFT, política y cierre.** Solo después de G4 con regularidad C1 local y G5 aplicar un teorema de función implícita y derivar sensibilidades respecto de choques monetarios. Las IRF necesitan un problema dinámico, historia heredada, horizonte, condición terminal y trayectoria de shocks consistentes; el prefijo de dos fechas no sustituye la economía infinita.

## 5. Trazabilidad y estatus

**Kernel previamente certificado:** raíz vinculante de 33 filas, vecindad bancaria abierta, positividad del dual en la región racional, salida fiscal G*=2 Mpre, equivalencia de ceros de SOURCE original/targetizado, invertibilidad del shear bancario, transporte condicional de Fréchet. Los nuevos lemas de continuidad de las funciones productivas, metas y coeficientes bancarios deben constar con sus números de PR y ejecución especializada antes de incorporarlos como premisas descargadas.

**PENDIENTE:** HasFDerivAt del vector F_SOURCE económico original, inversa y norma de J_G, igualación funcional SOURCE–Python, cualquier raíz 34 alejada, rama S y equilibrio infinito. Los cuatro primeros bloques de código recién integrados no autorizan alterar este estatus.

**Referencia operativa:** leer las ecuaciones reales en lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean y las pruebas económicas de lean/current; no inferir pruebas por similitud de nombres con módulos candidate.
