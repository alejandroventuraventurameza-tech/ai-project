# Estado del diagnóstico de producción inicial

Fecha: 2 de noviembre de 2026. Rama de trabajo: `work/irf-delivery`.

## Qué se hizo
Se resolvieron conjuntamente las ecuaciones reducidas no lineales del prefijo y de los períodos interiores, manteniendo parámetros, estados heredados y anuncios. Se usaron horizontes de 20 a 640 períodos, con referencia resuelta bajo el mismo cierre terminal.
La gráfica lineal se usa solo en la frontera terminal en el primer cierre. El segundo fija las desviaciones de los controles a cero en T, dejando endógenos los estados. No se imponen valores nulos de consumo o tasas.

| Rama | IRF original | No lineal T=640, gráfica terminal | No lineal T=640, controles de referencia |
|---|---:|---:|---:|
| slack | -3.579757199e-05 | -3.559159239e-05 | -3.567631947e-05 |
| binding | -0.004142551019 | -0.004142220876 | -0.004142189601 |

Unidades: respuesta inicial de producción en log %. La pequeñez del efecto en S exige cuidar redondeos y comparaciones relativas.

## Evidencia obtenida
- La caída inicial persiste en los 20 casos calculados; todos pasan los márgenes de régimen comprobados.
- Las respuestas con gráfica terminal se estabilizan pronto; el cierre alternativo converge más lentamente y puede contaminar fuertemente horizontes cortos.
- Se conservan la reducción de pérdida asignativa en S y su aumento en B, bajo los casos calculados.
- El Jacobiano disperso por bloques se contrastó contra diferencias direccionales del residuo completo; el prefijo ensamblado coincide con el original al imponerle su cierre lineal.

## Interpretación provisional
La evidencia no respalda atribuir exclusivamente la contracción inicial a la propagación lineal de la cola o a los pasos de Jacobiano ensayados. El diagnóstico laboral y de Phillips identifica una respuesta conjunta del precio del insumo y el consumo del hogar; el componente futuro de fijación de precios es importante en esa identidad.
Esto no es una descomposición causal independiente. Tampoco descarta errores en bloques no auditados, ni establece optimalidad dinámica, determinación global o equilibrio completo.

## Pendiente antes de cerrar la explicación económica
1. Completar la trazabilidad de las 33 ecuaciones frente a los problemas individuales y los anuncios del experimento, más allá del bloque laboral/NKPC ya contrastado.
2. Seguir la respuesta esperada de inflación y consumo a través de Euler y reglas de política para explicar la trayectoria conjunta, distinguiendo efectos parciales y de equilibrio.
3. Mantener separado ese diagnóstico de la formalización completa y de la comparación exacta de horizonte infinito.

## Archivos y reproducción
- `output/impact_diagnosis/REPORT.md`: identidades y sensibilidad local.
- `output/nonlinear_tail_comparison/REPORT.md` y `REPORT.json`: horizontes, cierres, residuos, márgenes y CSV.
- `python code/verify.py`: reproduce todos los bloques y los diagnósticos.
- No se modificaron las ecuaciones para forzar un signo ni se sustituyeron las IRF principales por estas trayectorias finitas.
- El artículo y las diapositivas no se editaron durante este diagnóstico; siguen sujetos al rediseño acordado.


## Ensayo de frontera corta no admisible

Se conserva también el ensayo preliminar con T=6 y T=12, en
`output/nonlinear_tail_comparison/short_terminal_stress/`. Con controles
terminales en referencia a T=12, las raíces no satisfacen el signo financiero
prescrito: S viola la holgura inicial de L y B viola su dual inicial. Estas
raíces se excluyen como trayectorias admisibles de esas ramas y el comprobador
termina con código distinto de cero. Se conserva el resultado fallido; no se
presenta como una IRF económica válida. Es evidencia adicional de que un cierre
terminal impuesto demasiado cerca puede alterar incluso el conjunto activo.

Reproducción de este fallo esperado:
`python code/irf/compare_nonlinear_tail.py --horizons 6 12 --output code/irf/output/nonlinear_tail_comparison/short_terminal_stress`


## Actualización: Euler, regla monetaria y precios

Se reconstruyó la solución reducida no lineal T=640 y se verificaron por período
las identidades de formación de tasas bancarias, regla monetaria, Euler y Phillips.
El detalle y las trayectorias están en `output/transmission_trace/REPORT.md`,
`REPORT.json` y `paths.csv`. Reproduce `python code/irf/trace_transmission.py`.

La innovación reduce la remuneración inicialmente, pero la regla responde a
inflación y producto. La remuneración vuelve por encima de su referencia desde
el período 2 en S y desde el período 1 en B. No se introdujo una segunda innovación.
El rendimiento real de depósitos baja al inicio, mientras las respuestas
posteriores tienen otros signos; Euler relaciona esa trayectoria completa con
el consumo. El término de consumo terminal se conserva explícito y es diminuto
en el horizonte calculado; esto no constituye una prueba económica de terminalidad.

Usando Euler en el experimento determinista se obtiene:
`m_t = 5/6 + 25 Pi_t(Pi_t-1) - 25 (Y_(t+1)/Y_t) Pi_(t+1)^2(Pi_(t+1)-1)/RD_t`.
El término de precios futuro negativo supera al contemporáneo positivo al
impacto. Cae m, el precio del insumo pagado a las empresas productoras y costo
marginal real del minorista. Esto no equivale a caída de inflación: la inflación
inicial sube respecto de la referencia. El markup real del minorista 1/m aumenta.
Con capital instalado fijo, la demanda laboral y oferta del hogar implican
`Delta log Y_0 = (Delta log m_0 - Delta log Cw_0)/3`.

| Rama | Consumo: contribución de rendimientos reales en 0–2 | Consumo: contribución en 3–639 | Consumo inicial total |
|---|---:|---:|---:|
| slack | 0.002448903 | -0.002954069 | -0.000505167 |
| binding | 0.002467088 | -0.002950450 | -0.000483363 |

Unidades: log %. La suma incluye además el término terminal explícito del reporte.
Estas son descomposiciones exactas evaluadas en una solución conjunta, no
experimentos causales independientes. El aumento posterior de tasas es una
respuesta endógena, no una explicación aislada demostrada del output inicial.
Tampoco está demostrada aún la suficiencia de todas las condiciones marginales.

Esta actualización satisface la trazabilidad algebraica del bloque laboral,
regla monetaria, precios bancarios, Euler y Phillips. Queda revisar la derivación
y suficiencia de los otros bloques y formular comparaciones económicas
consistentes antes de atribuir causalmente la contracción a un canal separado.
La pérdida asignativa corresponde a t+1; no mide la misma producción corriente
que cae en t=0. No se editaron artículo o diapositivas ni se inició otra campaña Lean.


## Actualización: condiciones empresariales y liquidación

Se auditaron las condiciones sin eliminar el multiplicador empresarial sobre
las dos trayectorias reducidas no lineales T=640. Se reconstruyó patrimonio
independientemente del presupuesto, se verificaron caja, capital, colateral,
complementariedad, signos de duales y la esquina sin depósitos. El dual normalizado
se obtiene de la FOC del préstamo; por eso esa FOC no constituye una ecuación
independiente adicional, mientras capital y complementariedad sí la contrastan.

Para el banco se reconstruyeron los dos pagos, negociación, facilidad, reservas
posteriores, rendimiento detallado y su esperanza. Pasan balance, caps holgados,
encaje, solvencia, clearing esperado y renovación. Se comprobaron coeficientes
de una cota de concavidad para una etapa a precios dados; no se cierra el valor
ni la optimalidad de horizonte infinito. Los errores máximos de las identidades
y KKT son menores que 2e-14. Los signos no estrictos se comprueban con tolerancia
numérica explícita: no son certificados de intervalos.

| Rama | Crédito H (log %) | Capital elegido H (log %) | Cambio del dual normalizado H |
|---|---:|---:|---:|
| slack | 0.001095171 | 0.000164091 | -1.2167441e-06 |
| binding | 0.000840645 | -0.001072639 | 2.30813599e-05 |

La identidad de H restringida es `k_next=(N-c)/(q-h/RL)`. En B, la caída de los
recursos propios disponibles para invertir supera la mejora del costo efectivo,
por lo que k_next cae. La descomposición de N-c muestra menores beneficios
operativos y menor valor de reventa del capital; alivio del repago real heredado
y menor consumo compensan solo parcialmente. En S, en cambio, los recursos
propios aumentan ligeramente y mejora el costo efectivo: H elige más capital.

También `b=h*k_next/RL`: el principal puede subir aun cuando k_next cae si el
valor pignorable por unidad de capital sube y baja la tasa de repago. Esto ocurre
en B. Por tanto, crédito positivo y creciente no equivale a más inversión ni a
un multiplicador menor. Los cambios de dual en unidades de utilidad también
conservan los signos opuestos; se reportan separados del dual normalizado.

El inventario de las 33 filas y etiquetas del manuscrito se conserva en
`output/financial_blocks_audit/REPORT.json`; es trazabilidad, no auditoría de
cada prueba escrita ni cobertura Lean. El reporte legible está en `REPORT.md`.

La reproducción completa pasó y el bloque ampliado con descomposición de
patrimonio se comprobó nuevamente. Quedan suficiencia dinámica, condiciones
terminales económicas completas y correspondencia con equilibrio, además de la
revisión de literatura y el guion expositivo acordados. No se modificaron los
parámetros, las curvas principales, el artículo ni las diapositivas.
