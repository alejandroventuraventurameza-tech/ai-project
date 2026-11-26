# Canal de capital empresarial en la rama de colateral activo: recursos y precio efectivo

**Corte cientifico:** 10 de noviembre de 2026. **Estado:** NUMERICO, prefijo determinista de 33 ecuaciones con estado heredado constante. **Fuente primaria:** code/irf/finite_irf.py (auxiliary, prefix_residual, period_metrics). **Auditoria independiente de identidades:** code/irf/frozen_four_tool_impact_audit.py, commit [37cea46e](https://github.com/alejandroventuraventurameza-tech/ai-project/commit/37cea46ed6b28fb39aa0ea215eb79b907709dfa0), [GitHub Actions build #42911656479](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42911656479), job Run code/verify.py satisfactorio en ese SHA.

## I. Condicion de financiamiento, sin confundir principal y valor facial

La firma i pertenece a H o L. Para una restriccion de colateral activa en fecha cero, defina la riqueza corriente fuente

\[
 N_{i0}=\pi^{op}_{i0}+(1-\delta)q_0 k_{i0}
  -F^{\mathrm{heredado}}_{i0}/\Pi_0.
\]

El rostro nominal de garantia del nuevo prestamo por unidad de capital es

\[
 J_{i0}=\theta_i(1-\delta)\Pi_1 q_1,\qquad
 F_{i1}=J_{i0}k_{i1}.
\]

El principal del prestamo nuevo es \(b_{i0}=F_{i1}/R^L_0\), no \(F_{i1}\). El presupuesto estructural es:

\[
 c_{i0}+q_0 k_{i1}-\frac{F_{i1}}{R^L_0}=N_{i0}.
\]

En la rama activa y donde el precio efectivo y los recursos invertibles son positivos, esto equivale exactamente a

\[
 k_{i1}=\frac{N_{i0}-c_{i0}}{p^{ef}_{i0}},
 \qquad p^{ef}_{i0}=q_0-\frac{J_{i0}}{R^L_0}>0.
\]

Para dos soluciones de igual antecesor pero distinta politica, la diferencia de logaritmos cumple

\[
 \Delta\ln k_{i1}=\Delta\ln(N_{i0}-c_{i0})
                   -\Delta\ln p^{ef}_{i0},
\]

y la identidad de credito satisface

\[
 \Delta\ln b_{i0}=
  \Delta\ln J_{i0}+\Delta\ln k_{i1}-\Delta\ln R^L_0.
\]

**Estas igualdades son descomposiciones contables de soluciones conjuntas.** Ni recursos disponibles ni precio efectivo se mantienen exogenos; por ello no se identifican efectos causales parciales sin construir contrafactuales adicionales.

## II. Cuatro shocks separados: valores reproducidos

Se aplico a cada coordenada una perturbacion numerica de -1e-5, manteniendo X0 constante. Las innovaciones de remuneracion de reservas y cantidad de reservas son logaritmicas; el encaje y la amplitud de corredor cambian en unidades de **nivel**. Las magnitudes no son directamente comparables entre instrumentos.

Las entradas son cambios logaritmicos porcentuales desde la misma base (por tanto 0.001 corresponde a 0.001 por ciento, NO a un punto porcentual).

| Instrumento perturbado | Recursos invertibles H (%) | Precio efectivo H (%) | Capital siguiente H (%) | Credito H (%) | Log capital H/L (%) |
|---|---:|---:|---:|---:|---:|
| Remuneracion de reservas | -0.001778072 | -0.000682976 | -0.001095096 | +0.000819107 | -0.000756252 |
| Cantidad de reservas | +0.000004289 | +0.000001649 | +0.000002641 | -0.000001930 | +0.000001797 |
| Coeficiente de encaje | -0.000025004 | -0.000009844 | -0.000015160 | +0.000015502 | -0.000011340 |
| Amplitud del corredor | -0.000661483 | -0.000260817 | -0.000400666 | +0.000380594 | -0.000284271 |

Para el shock negativo de remuneracion, la tasa bruta de prestamo disminuye -0.000879612% en logaritmos. Sin embargo, la caida de recursos propios invertibles H (-0.001778072%) domina la reduccion del precio efectivo (-0.000682976%); por eso k_H1 cae -0.001095096%. Simultaneamente el valor facial de garantia por unidad de capital H sube +0.001034591%, y el principal del credito H sube +0.000819107%. Un aumento de credito registrado y una contraccion de capital pueden coexistir en esta configuracion sin contradiccion contable.

La firma H tiene productividad tecnologica ilustrativa superior y menor pignorabilidad que L; ese orden **no** basta para afirmar que cualquier politica que favorezca H mejore el bienestar. En el shock de remuneracion, el capital relativo H/L cae. Su identidad exacta es

\[
 \Delta\ln(k_{H1}/k_{L1})=
 [\Delta\ln S_H-\Delta\ln S_L]
 -[\Delta\ln p_H^{ef}-\Delta\ln p_L^{ef}],
 \quad S_i=N_{i0}-c_{i0}.
\]

El primer corchete vale +0.000261473% y el segundo +0.001017725%; su diferencia es -0.000756252%. Esto identifica **contablemente** el termino dominante en esta rama; no constituye una atribucion causal al parametro de encaje o a un instrumento separado.

## III. Verificacion y limites

El script recompone directamente las riquezas N de la funcion SOURCE auxiliary a partir del estado inicial realmente heredado, los controles resueltos y la regla de politica exacta. Por separado recupera las promesas faciales, precios efectivos, capital siguiente y principal de credito. Rechaza estados no positivos, residuos presupuestarios y de garantia mayores que 1e-9, y errores de las dos identidades logaritmicas mayores que 1e-8 puntos porcentuales. Los errores logaritmicos maximos observados en esta auditoria de los cuatro shocks son inferiores a 1e-13 puntos porcentuales. El maximo residuo del sistema reducido de 33 filas fue 3.02e-14.

Las duales de ambas firmas son positivas y las garantias activas en las raices ensayadas, mientras los topes bancarios son holgados. La solucion de fecha uno usa el cierre lineal local P0, no un operador no lineal infinito certificado. El producto contemporaneo Y0 no es identico al capital elegido K1; ademas, la perdida asignativa eficiente no se infiere solo del signo de K_H/K_L.

**Frontera pendiente:** resultados S y B comparables bajo las mismas innovaciones y el mismo antecesor, suficiencia KKT de empresas y bancos, correspondencia de 34 ecuaciones SOURCE, condiciones terminales, prueba del equilibrio completo, descomposicion de producto con trabajo endogeno, bienestar y crecimiento permanente. En particular, el nucleo actual no contiene una ley de acumulacion endogena de conocimiento: una transicion a mayor nivel productivo no demuestra una mayor tasa de crecimiento de largo plazo.

**Etiqueta final:** NUMERICO - rama binding con estado fijo. No llamar a este ejercicio IRF estructural plenamente certificada, multiplicador de politica causal o teorema de crecimiento.
