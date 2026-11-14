# Interacciones locales de cuatro herramientas monetarias: auditoria de alcance exacto

**Fecha:** 10 de noviembre de 2026. **Estado:** NUMERICO, sistema reducido, rama de colateral activa; no resultado de equilibrio completo. **Fuente primaria:** code/irf/finite_irf.py, funcion prefix_residual; verificadores frozen_stationary_prefix_audit.py, frozen_four_tool_impact_audit.py, frozen_four_tool_local_derivative_audit.py y frozen_four_tool_joint_interaction_audit.py. **Evidencia de partida:** commit 35b08dd6fcee9c9a7f2e35e265287beba0adfabd, [GitHub Actions 42911083498](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42911083498), job Run code/verify.py aprobado. Las modificaciones posteriores que guardan JSON y exigen escala cuadratica requieren su propio CI.

## 1. Pregunta, calendario y unidades

Se pregunta si, desde un mismo antecesor estacionario heredado, el impacto de dos cambios monetarios simultaneos coincide exactamente con la suma de sus soluciones aisladas. La intervencion inicial es:

\[
 \nu=(v_R,v_M,v_\rho,v_\Delta).
\]

Las coordenadas son (i) innovacion **logaritmica** de la regla de remuneracion de reservas, (ii) innovacion **logaritmica** de la cantidad de reservas prepagos, (iii) cambio **en nivel** del coeficiente de encaje y (iv) cambio **en nivel** de la amplitud del corredor. No hay una tasa de politica de referencia independiente ni un modulo de compras de activos del banco central: son extensiones diferentes, pendientes de contabilidad propia. No se debe confundir remuneracion con tasa de politica separada, ni encaje con cantidad de reservas.

El estado heredado X0, las innovaciones anunciadas de fecha uno y la matriz local P0 de 16 por 6 permanecen identicos en los experimentos. Se resuelve un prefijo de dos fechas de **33 ecuaciones originales**, con garantias de H y L activas y topes bancarios holgados. La condicion de fecha dos es una aproximacion **lineal** mediante P0, no una solucion completa de horizonte infinito.

## 2. Diferencia conjunta y proposicion matematica

Sea F:R^33 x R^4 -> R^33 el vector de residuos de prefix_residual, en el dominio donde logaritmos y denominadores estan definidos, y sea z(0)=0 la raiz estacionaria. Para i distinto de j definase:

\[
 D_{ij}(h)=z(he_i+he_j)-z(he_i)-z(he_j)+z(0).
\]

Es una diferencia cruzada de soluciones, **no** una medida causal de complementariedad politica. Para una metrica positiva m, tambien se evalua

\[
 C_{ij}^{m}(h)=\log\frac{m(he_i+he_j)}{m(0)}
 -\log\frac{m(he_i)}{m(0)}
 -\log\frac{m(he_j)}{m(0)}.
\]

**Proposicion condicional (funcion implicita).** Si F es C^2 cerca de (0,0), F(0,0)=0 y J=F_z(0,0) es invertible, entonces existe una solucion local z de clase C^2 y, definiendo d_i=partial_i z(0),

\[
 Jd_i=-F_{\nu_i},\qquad
 Jd_{ij}=-\left[F_{zz}[d_i,d_j]+F_{z\nu_i}d_j+
 F_{z\nu_j}d_i+F_{\nu_i\nu_j}\right].
\]

En particular, para h hacia cero,

\[
 D_{ij}(h)=h^2d_{ij}+o(h^2).
\]

**Prueba.** Derivar F(z(nu),nu)=0 respecto de nu_i da J d_i + F_i=0. Derivarla respecto de nu_j, aplicar la regla de cadena y despejar con la inversa de J da la segunda igualdad. Al restar las expansiones de Taylor de segundo orden de las cuatro soluciones se cancelan los terminos constantes y lineales y permanece h^2 d_ij. Fin.

**Limite de validacion:** esta proposicion analitica es correcta bajo sus supuestos; el codigo realiza hasta ahora un chequeo **numerico** de la matriz J y sus pivotes, no una prueba intervalar de invertibilidad ni una demostracion de equivalencia con el equilibrio estructural fuente.

## 3. Resultados del run original

Las seis parejas se probaron para h=1e-5 y h/2=5e-6, manteniendo las 33 filas y el mismo estado heredado. Se verificaron las dos duales de colateral estrictamente positivas, garantias saturadas, topes bancarios holgados y metricas finitas.

| Pareja | Norma de D(h/2) dividida por norma de D(h) |
|---|---:|
| Remuneracion + cantidad de reservas | 0.24997502 |
| Remuneracion + coeficiente de encaje | 0.24999058 |
| Remuneracion + amplitud de corredor | 0.24999386 |
| Cantidad de reservas + coeficiente de encaje | 0.25001362 |
| Cantidad de reservas + amplitud de corredor | 0.24998426 |
| Coeficiente de encaje + amplitud de corredor | 0.25000908 |

**Maximos en los doce experimentos:** residuo no lineal de 33 filas 2.14744e-14; error relativo de aproximacion lineal 3.04995e-4; interaccion relativa en coordenadas logaritmicas 1.05063e-4; termino cruzado directo del vector residual en coordenadas fijas 2.01403e-9.

Que el cociente ronde 1/4 es compatible con D(h)=h^2 d_ij + o(h^2) cuando d_ij es no nulo. **No** prueba diferenciabilidad C^2, unicidad global, ni ausencia de una rama alternativa. Los cambios cruzados de log Y en esta vecindad son de orden 1e-11 a 1e-9, y no deben presentarse como multiplicadores de politica calibrados.

El signo mixto no tiene restriccion universal por el teorema implicito. En el ejemplo escalar F(z,nu_i,nu_j)=z-a nu_i-b nu_j-c nu_i nu_j, la raiz es z=a nu_i+b nu_j+c nu_i nu_j y la diferencia cruzada es c h^2; c puede tener cualquier signo. La existencia de efectos mixtos no demuestra complementariedad positiva ni justifica por si sola una recomendacion de politica.

## 4. Reproducibilidad y compuertas pendientes

La cadena auditable es: (a) fuente finite_irf.py; (b) referencia de estado congelado; (c) auditoria independiente de forzamiento y derivadas locales; (d) parejas no lineales en frozen_four_tool_joint_interaction_audit.py; (e) ejecucion de code/verify.py en GitHub Actions; (f) JSON reproducible code/irf/output/four_tool_pairwise_audit.json y artefacto adjunto al run una vez confirmado por CI; (g) tablas y manuscrito despues de cotejar ese JSON. Comando focalizado: python code/irf/frozen_four_tool_joint_interaction_audit.py.

**PENDIENTE, sin promocion automatica a teorema:** cota intervalar de J^-1 y un radio de regularidad; correspondencia semantica exacta del operador economico fuente de 34 filas; cola dinamica infinita no lineal; testigos KKT y optimalidad del banco, empresa y hogar en cada historia soportada; comparacion de ambas ramas S/B bajo el mismo shock; identificacion causal, eficiencia, bienestar y tasa de crecimiento permanente. El analisis bancario de continuidad y terminalidad debe seguir las obligaciones BK1-BK6 de docs/IE_BANK_DYNAMIC_OPTIMALITY_GATE_20261108.md.

**Veredicto:** evidencia NUMERICA de interacciones de segundo orden en una rama reducida, sin prueba de equilibrio competitivo dinamico ni crecimiento sostenido. Conservar PR #2 en draft y main sin fusionar.
