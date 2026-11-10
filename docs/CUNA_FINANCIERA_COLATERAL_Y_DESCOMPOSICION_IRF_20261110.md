# Cuna de financiamiento H-L: identidad fuente, prueba Lean y descomposicion de IRF

**Corte:** 10 de noviembre de 2026. **Alcance:** precio efectivo de inversion en el modelo fuente bajo colateral vinculante; prueba formal de su diferencia entre empresas y comprobacion numerica sobre IRF FINITAS. No es una demostracion de equilibrio infinito, bienestar o crecimiento tendencial.

## 1. Definicion y teoremas fuente

Defina el valor nominal pignorable unitario comun como

\[
J_{t+1}=(1-\delta)\Pi_{t+1}q_{t+1},
\qquad
p^{eff}_{i,t}=q_t-\frac{\theta_iJ_{t+1}}{R_t^L}.
\]

Cuando la garantia vincula, el presupuesto de la firma puede escribirse en forma equivalente como c_(i,t)+p^eff_(i,t) K_(i,t+1)-N_(i,t)=0. Bajo theta_H<theta_L, delta<1, Pi_(t+1)>0, q_(t+1)>0 y R_t^L>0:

\[
W_t=p^{eff}_{H,t}-p^{eff}_{L,t}
=(\theta_L-\theta_H)\frac{J_{t+1}}{R_t^L}>0.
\tag{F}
\]

**Prueba:** restar los precios efectivos elimina q_t; la conclusion se sigue del orden de theta y de la positividad de J/R. Fin.

La existencia y la positividad de (F) se demostraron contra las DEFINICIONES LITERALES de EconomicModel.lean en los teoremas Lean source_effective_price_wedge_H_minus_L y source_less_pledgeable_H_higher_effective_price. [GitHub Actions #42919617934](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42919617934), commit 8d11d6dcab402765fcfe82673cf562c545749c2d, chequea el kernel sin sorryAx (solo propext, Classical.choice y Quot.sound).

El modelo Primitives contiene productividad_H>productividad_L como supuesto estructural, pero **NO** presupone theta_H<theta_L para toda posible economia. El orden de pignorabilidad es una hipotesis ADICIONAL, satisfecha por el ejemplo de Python: theta_H=0.15, theta_L=0.40 y productividades 1.01>1.00. La prueba no implica una comparacion de inversiones optimas, bienestar, ni dos equilibrios.

## 2. Comparativa de tasa y canal conjunto

Manteniendo J y theta constantes:

\[
\left.\frac{\partial W_t}{\partial R_t^L}\right|_{J,\theta}
=-\frac{(\theta_L-\theta_H)J_{t+1}}{(R_t^L)^2}<0.
\]

Una tasa crediticia bruta mas baja reduce ambos precios efectivos, pero amplia su diferencia positiva cuando theta_L>theta_H, **a precio de garantia fijo**. Es una derivada parcial, no la reaccion de equilibrio al mover un instrumento monetario.

En cualquier comparacion positiva entre una trayectoria shock y su base, con theta y delta fijos:

\[
\underbrace{\log(W_t^{shock}/W_t^{base})}_{\Delta\log W_t}
=
\underbrace{\log(J_{t+1}^{shock}/J_{t+1}^{base})}_{\Delta\log J_{t+1}}
-
\underbrace{\log((R_t^L)^{shock}/(R_t^L)^{base})}_{\Delta\log R_t^L}.
\tag{D}
\]

La identidad (D) es contable; no representa dos shocks estructurales independientes, pues la tasa crediticia y el valor de la garantia se determinan conjuntamente.

## 3. Experimento reproducido

La fuente es el CSV code/irf/output/main/finite_irf_paths.csv y su manifiesto code/irf/output/main/finite_irf_validation.json, producidos por finite_irf.py. El experimento es **innovacion logaritmica de fecha cero v_R=-1e-5 en la regla de remuneracion de reservas**, aproximadamente -0.1 puntos basicos, con futuras innovaciones nulas; NO es un shock al encaje ni al ancho del corredor. Los parametros son ilustrativos y no provienen de estimacion externa. Se resuelve un prefijo no lineal de dos fechas y una continuacion lineal local, sin regla de seleccion global de ramas.

El auditor code/irf/audit_effective_price_wedge_irf.py reconstruye J futuro usando columnas de fecha t+1 e identifica W_t independientemente de los precios efectivos reportados. Valida 160 transiciones por rama y archiva huellas de fuentes y tolerancias. Ejecucion verificada: [build #42920163078](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42920163078), paso Run code/verify.py exitoso; artefacto finite-irf-collateral-wedge-decomposition, ID 13811018344.

| Impacto, 100 por cambio logaritmico (log %) | Rama S | Rama B |
|---|---:|---:|
| Cuña W | +0.000931145 | +0.001913377 |
| Garantia futura J | +0.000312840 | +0.001030034 |
| Menos variacion de tasa crediticia | +0.000618305 | +0.000883343 |
| Tasa crediticia, cambio en puntos basicos | -0.063632 | -0.090908 |

La identidad en NIVELES tiene error maximo 1.942890293094024e-16; la identidad LOGARITMICA sin multiplicar por cien presenta error maximo 1.0393263669399716e-15. Son redondeos, no errores estadisticos.

**Advertencia decisiva sobre S:** en fecha t=0 la firma L tiene colateral holgado, de modo que effective_price_L es una expresion de precio pignorable HIPOTETICA y NO su precio marginal KKT. El resultado S en t=0 es una cuña contable; solo en B ambas firmas aplican el precio efectivo vinculante al impacto. Desde t=1 el camino construido utiliza la rama vinculante, sin demostracion de su suficiencia dinamica completa.

**Signo no permanente:** en t=3 la respuesta numerica de W es negativa (S: -0.000190938 y B: -0.000448797, unidades de 100 por log). No extrapolar el resultado al impacto como misallocation de signo constante, ni como evidencia de crecimiento de largo plazo.

## 4. Ledger de compuertas

- **DEMOSTRADO EN LEAN:** identidad F y orden positivo de cuña bajo hipotesis explicitas (2 teoremas), ademas de los 7 ya aprobados del bloque Euler-garantia-presupuesto.
- **COMPROBADO NUMERICAMENTE:** identidad D sobre los CSV internos; 160 periodos por rama y errores reproducibles, sin identificar causas independientes.
- **PENDIENTE:** equivalencia funcional de todas las 34 filas Python vs SOURCE, grafo no lineal C1 y radio invariante, globalidad de los problemas bancario y empresarial, pagos OTC, transversalidad, existencia del equilibrio infinito y un mecanismo endogeno para una variacion permanente de la tasa de crecimiento.

La consecuencia metodologica es que no se puede deducir de una reduccion de tasas, aisladamente, que la empresa mas productiva y menos pignorable aumentara su inversion relativa ni que la asignacion de factores mejorara.
