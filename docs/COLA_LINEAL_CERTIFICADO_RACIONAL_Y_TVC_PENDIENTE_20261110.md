# Cola lineal de IE: contraccion por bloques y frontera con la TVC economica

**Fecha:** 10 de noviembre de 2026. **Objeto exacto:** matriz F0 de 6 por 6 almacenada como decimales en code/irf/inputs/rational_preconditioners.json. **Alcance:** prueba aritmetica exacta sobre esos decimales fijos, seguida de un teorema matematico condicional sobre cualquier extension C1. No constituye una prueba Lean del operador SOURCE ni de un equilibrio infinito.

**Codigo reproducible:** python code/irf/exact_linear_tail_power_certificate.py. El codigo utiliza Fraction sobre los textos decimales; la aceptacion no depende de coma flotante. SHA256 fijado: d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94. **Evidencia inicial:** [GitHub Actions #42913907336](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42913907336), paso Exact rational block-power certificate aprobado y artefacto exact-linear-tail-power-certificate ID 13807229974. La revision siguiente anade la verificacion obligatoria del hash; cotejar el CI del SHA final por separado.

## 1. Datos, estados y contraejemplo a contraccion por periodo

La cola lineal actual emplea seis estados compactos en desviaciones logaritmicas, x_t, y la transicion

\[
 x_{t+1}=F_0x_t,\qquad F_0\in\mathbb Q^{6\times6}.
\]

Cada entrada de F0 es el valor RACIONAL exacto del literal decimal almacenado, no una identidad economica entre F0 y el Jacobiano original de EconomicModel.lean.

El calculo exacto devuelve los siguientes intervalos decimales externos:

| n | Norma infinito de F0 elevado a n |
|---:|---|
| 1 | [2.356707835248, 2.356707835249] |
| 7 | [6.097821698406, 6.097821698407] |
| 16 | [1.623770126123, 1.623770126124] |
| 40 | [0.993748274030, 0.993748274031] |
| 48 | [0.955246892193, 0.955246892194] |

Se ha probado por fracciones enteras que

\[
 \|F_0^{48}\|_\infty<q:=\frac{24}{25}<1,\qquad
 \max_{0\leq r<48}\|F_0^r\|_\infty<M:=\frac{61}{10}.
\]

La amplificacion maxima dentro del bloque se produce en n=7. Por ello no se debe postular una contraccion por periodo ni suponer monotonia de la sensibilidad a las condiciones terminales a horizontes cortos.

## 2. Proposicion L: decaimiento y suma de la cola lineal

Para todo x en R^6 y todo entero k no negativo:

\[
  \|F_0^k x\|_\infty \leq
  \frac{61}{10}
  \left(\frac{24}{25}\right)^{\lfloor k/48\rfloor}
  \|x\|_\infty.
\]

En particular, F0^k x converge a cero y

\[
 \sum_{k=0}^\infty \|F_0^k\|_\infty
 \leq
 \frac{\sum_{r=0}^{47}\|F_0^r\|_\infty}
      {1-\|F_0^{48}\|_\infty}<7320.
\]

**Demostracion.** Escriba k=48m+r con 0<=r<48. Por asociatividad y submultiplicatividad, ||F0^k|| <= ||F0^48||^m||F0^r|| <= q^m M. La convergencia y sumabilidad son consecuencia de una serie geometrica, tras sumar los 48 residuos posibles r. Fin.

La aritmetica exacta produce una cota mas ajustada sobre la fraccion de la suma de los 48 primeros terminos y uno menos la norma exacta del bloque: es estrictamente menor que 2274.018921091477. Es una cota sobre la serie de normas de esta MATRIZ DECIMAL; no es una cota posterior del error de una solucion finita del DSGE.

## 3. Proposicion N: implicacion no lineal CONDICIONAL

**Supuestos.** Existe una ley local \(\Phi:U\to\mathbb R^6\) de clase C1 en un entorno abierto U de cero, con \(\Phi(0)=0\) y \(D\Phi(0)=F_0\) **exactamente**.

**Conclusion.** Hay un radio r>0 (desconocido cuantitativamente) y constantes M'>0, q' en (0,1) tales que, para estados iniciales suficientemente cercanos a cero,

\[
 \|\Phi^k(x)\|_\infty
 \leq M'(q')^{\lfloor k/48\rfloor}\|x\|_\infty
 \quad(k\ge0).
\]

**Demostracion.** La regla de la cadena da D(Phi^48)(0)=F0^48, cuya norma infinito es menor que 24/25. Por continuidad de la derivada, existe una bola donde los 48 primeros iterados estan definidos y ||D(Phi^48)(x)||<97/100. El teorema del valor medio en esa bola convexa implica ||Phi^48(x)|| <=(97/100)||x|| y, por tanto, invariancia del mapa de 48 pasos. Al iterar y acotar las 47 aplicaciones intermedias por sus constantes locales de Lipschitz se obtiene el resultado. Fin.

**Obligaciones esenciales pendientes:** construir Phi como ley ORIGINAL del equilibrio con una grafica de controles compatible, demostrar que es C1 en el conjunto activo, que su derivada es exactamente el F0 fijado, que los estados de fecha dos de S/B estan dentro del radio valido y que las KKT se cumplen a lo largo de la trayectoria. La proposicion N no establece existencia ni unicidad de equilibrios a partir de los datos disponibles.

## 4. Por que la cola lineal no cierra la TVC economica

La contraccion de seis estados no prueba por si sola la sumabilidad de beneficios o dividendos descontados en todo el arbol de pagos; tampoco la propiedad de optimalidad dinamica BankContinuationOptimalAt, la factibilidad bancaria robusta o la correspondencia de 34 filas de SOURCE con el prefijo reducido de 33 ecuaciones. La continuidad bajo dos cierres terminales finitos T=8,20,40,80,160 es evidencia NUMERICA; su diferencia puede ser no monotona y no se controla con una cota aislada sobre F0.

Tampoco se infiere seleccion endogena de rama, causalidad ni una mayor tasa de crecimiento tendencial. Un crecimiento persistente requiere un mecanismo de acumulacion no estacionario y sus propias condiciones de equilibrio.

## 5. Siguiente compuerta rigurosa

(1) Construir la ley no lineal y la grafica de controles satisfaciendo las 16 ecuaciones originales de recurrencia en un dominio de estados positivo. (2) Demostrar igualdad de Jacobianos en el modelo fuente y obtener un radio explicito mediante aritmetica intervalar, no asumirlo. (3) Acotar la norma de la derivada del mapa de 48 pasos en el dominio, controlando las restricciones de garantia y las esquinas OTC. (4) Verificar optimalidad global, TVC y mercados en todas las historias soportadas. (5) Solo entonces identificar el mecanismo causal y el crecimiento con contrafactuales admisibles.

**Semaforo:** DEMOSTRADO aritmeticamente para la matriz DECIMAL fijada; CONDICIONAL matematico para la implicacion no lineal; PENDIENTE para EconomicModel.lean, el equilibrio estocastico y la TVC. El PR sigue draft y main no se modifica.
