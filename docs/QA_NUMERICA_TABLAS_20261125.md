# Cotejo numérico de tablas publicadas — 25/11/2026

**Datos fijados:** \`paper/irf_impact_table.tex\`, \`paper/irf_mechanism_table.tex\` y \`code/irf/output/delivery_audit.json\` de la rama de precierre. No se ejecutó una simulación nueva para este cotejo: se compararon los resultados previamente calculados con la tabla publicada.

## Tabla principal: 12 cifras, 12 coincidencias de redondeo

Se mapearon las seis filas a los seis campos del JSON para cada rama S/B. En las doce celdas, la diferencia absoluta entre el texto publicado y el dato exacto fue inferior a \`5.001e-9\`, la tolerancia teórica de redondear a ocho decimales.

| Fila publicada | S: valor fuente | B: valor fuente | Estado |
|---|---:|---:|---|
| Tasa interbancaria (pb) | −0.0636325360 | −0.0911714505 | Coincide |
| Tasa de crédito (pb) | −0.0636317548 | −0.0909076027 | Coincide |
| Producción (log %) | −0.0000357976 | −0.0041425510 | Coincide |
| Crédito H (log %) | +0.0010951823 | +0.0008406476 | Coincide |
| Crédito L (log %) | −0.0004738979 | +0.0015781081 | Coincide |
| Pérdida condicional (100 Δlog) | −0.0000024807 | +0.0000085199 | Coincide |

El archivo JSON conserva \`status=passed_internal_numerical_checks\` y \`full_equilibrium_validated=false\`; la coincidencia de 12 números **no** significa que se haya demostrado el equilibrio competitivo.

## Tabla de mecanismo

La tabla \`irf_mechanism_table.tex\` se genera con \`render_mechanism_table.py\` desde soluciones reducidas no lineales de horizonte finito \`T=640\`. Las identidades redondeadas publicadas se cumplen:

- Rama S: \`0.00002735 + 0.00013674 = 0.00016409\` para el capital.
- Rama B: \`-0.00174198 + 0.00066934 = -0.00107264\` para el capital.
- Rama S: \`0.00031268 + 0.00016409 + 0.00061840 = 0.00109517\` para el crédito.
- Rama B: \`0.00102984 - 0.00107264 + 0.00088344 = 0.00084064\` para el crédito.

Las pequeñas diferencias de la última cifra entre la tabla de mecanismo y la tabla principal no deben declararse un fallo: las tablas tienen distinta procedencia (sistema reducido finito no lineal vs. IRF principal con continuación local lineal) y ambas muestran valores redondeados. No se ha demostrado identidad exacta entre las dos corridas.

**Límites:** esto verifica la correspondencia de números ya calculados con dos tablas, sin recalcular todas las trayectorias ni revisar visualmente cada curva. La ejecución oficial completa de \`code/verify.py\` en el último commit entregado sigue pendiente.
