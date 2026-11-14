# IE project — compuerta racional 33+1 en la frontera Python congelada (14-XI-2026)

## Evidencia ejecutada y revisión

- Rama: `work/lean-ci-validation-source-33-row-20261114`, **sin fusionar a main**.
- Workflow `build`: **success**, [Actions #43586662671](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43586662671), SHA de código `4945ead884cb7bbd8f38e6a8a8d8163f0c51f8ba`.
- Entrada reproducida: `code/irf/search_frozen_python_augmented34_boundary.py`; salida: `code/irf/output/frozen_python_augmented34_boundary_search.json`.
- Auditoría añadida: `code/irf/audit_frozen_python_34_rational_preconditioner.py`; salida: `code/irf/output/frozen_python_augmented34_rational_preconditioner.json`. Los cuatro informes de frontera y signo se conservan como artefacto `frozen-python-34-boundary-and-rational-sign` del workflow.
- El control de correspondencias de **57 proposiciones** pasó en el job editorial `Python syntax` del run [#43586662779](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43586662779), después de verificar que cada una de las 57 huellas de proposición coincide con el ledger; no se promovió cobertura formal.

## Misma herencia, punto base de frontera numérica

Se conserva el único estado heredado original `frozen_stationary_seed(steady_case())`, con las tres restantes innovaciones de política iguales a cero y una continuación local P0 de dimensión 16 x 6. El modelo Python condicionado a la rama B arroja:

- Punto de frontera numérico: innovación logarítmica de remuneración de reservas `h*=0.007616947889328002`.
- Error máximo de las 34 ecuaciones: `8.767064851866735e-11`.
- Las comprobaciones locales de los regímenes empresariales y bancarios se satisfacen al nivel de precisión numérica implementado.
- Contracción SOURCE-shaped de multiplicador `s=-c' A^{-1}b` por sistema lineal flotante: `-4.212023216790536`; diferencia central no lineal: `-4.2120232193187945`.
- El punto estacionario de partida **no** era una raíz de la ecuación 34: su multiplicador L está en el intervalo racional exacto cuyos extremos, mostrados decimalmente, son `[0.028095195241253843,0.028095195241744166]`. Esta afirmación estricta corresponde a la **fórmula de parámetros Python**, no automáticamente a SOURCE.

## Teorema de Neumann comprobado con fracciones exactas para matrices racionalizadas

Sea `Ahat` la matriz 33 x 33 de diferencias centrales Python evaluada en el candidato; `bhat` la columna de forcing respecto a h y `chat` la fila de la fórmula de dual con cuatro coordenadas `8,15,24,28`. Se construye

`Jhat = [[Ahat,bhat],[chat,0]]`.

Cada entrada de `Ahat,bhat,chat` se redondea a 12 posiciones decimales y **se convierte exactamente a fracción racional**. Se hace igual con precondicionadores aproximados obtenidos mediante Gauss-Jordan. Para estos objetos *racionalizados* se verificaron con `fractions.Fraction` las desigualdades estrictas

`q33 = ||I-C33 Ahat||_inf < 1` y `q34 = ||I-C34 Jhat||_inf < 1`.

Las representaciones decimales de los defectos racionales son:

- `q33 = 2.93994579973599e-10`.
- `q34 = 2.64257672124373e-10`.

Por consiguiente, **las matrices racionalizadas 33 x 33 y 34 x 34 son invertibles exactamente**. Además, un vector tangente racionalizado y el residuo `Ahat*u+bhat` producen la cota racional estricta

`-4.212023227923145 < s_rational < -4.212023205660193 < 0`.

Los intervalos citados son redondeos para lectura; los extremos y desigualdades efectivos se almacenan como fracciones exactas en JSON. No se ha certificado la matriz real de derivadas económicas.

## Verificación independiente por diferenciación automática (código posterior)

El commit `ba85f5f4a20a6239365caca0bcaa4c7e6ad8ab41` superó por completo
[GitHub Actions build #43587365649](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43587365649),
incluidos ambos jobs de Python y PDF. Se archivó el artefacto
`frozen-python-34-boundary-and-rational-sign`, ID `14110574662`,
SHA256 del ZIP `625c8c725472725504e560581deeca07133682006168b823907ab6ece22ae3cc`.

- `audit_frozen_python_34_forward_ad.py`: deriva de forma automática, en float64, las **33 filas originales de `finite_irf.prefix_residual` sin transcribirlas**, y agrega por separado la fórmula SOURCE-shaped de financiación de L en las cuatro coordenadas `8,15,24,28`.
- Diferencia máxima del bloque `A` frente al Jacobiano de diferencias centrales: `4.2561794089124305e-09`. Diferencia máxima de la columna `b`: `1.44771306054281e-10`. Error de la fila `c` frente a la fórmula analítica dispersa: `1.1102230246251565e-16`.
- Derivada automática de la fila 34 respecto de `h`: `0.0`. Schur automático: `-4.212023217372646`.
- `audit_frozen_python_34_ad_rational_gate.py`: redondea la matriz derivada automáticamente a 12 decimales y verifica con **fracciones exactas** la invertibilidad de esa matriz racionalizada. Defectos `q33 = 2.79684733361678e-10` y `q34 = 2.8881849479728e-10`.
- Intervalo racionalizado de Schur mostrado decimalmente: `[-4.212023236694934,-4.212023198052517]`, completamente negativo. Presupuesto condicional por entrada `7.957357478193563e-05`.
- La diferencia exacta de entradas entre las DOS matrices redondeadas (forward AD y diferencias centrales) está acotada por `4.257e-09`, muy por debajo del presupuesto condicional de la primera.

Esta es una **doble validación NUMÉRICA/ALGEBRAICA de Python**; la autodiferenciación elimina el error de truncamiento de diferencias centrales, **no** la aritmética de punto flotante ni la falta de equivalencia SOURCE. Ninguna de las matrices racionalizadas contiene por sí sola una caja de derivadas de SOURCE.

## Transporte de las 33 filas SOURCE-shaped en la misma frontera

El código `audit_frozen_34_boundary_source_shaped_row_transport.py` fue
ejecutado en [GitHub Actions build #43587698801](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43587698801) y pasó los trabajos de Python y PDF.

- Punto idéntico `h*=0.007616947889328002`, misma `X0`, misma continuación `P0`, y **33 ecuaciones originales Python** frente a las 33 transcripciones condicionadas SOURCE-shaped.
- Partición verificable: **8 filas empresariales** con cizallamientos de Euler; **16 filas adicionales**; **9 filas escalares de cocientes logarítmicos y niveles**.
- El residuo bruto máximo de las transcripciones en niveles es `32` unidades originales; el residuo reconstruido y normalizado máximo es `3.681499549657019e-13`. **Ambos se preservan**; no se debe usar el valor 32 sin identificar su escala económica.
- Error máximo al reconstruir los 33 residuos originales Python: `1.7763568394002505e-15`.
- El `T` numérico de filas posee pivote mínimo `0.13148182680592024` e inversas flotantes con defecto máximo `1.1102230246251565e-16`.
- Diferencia máxima entre `T*D(filas_SOURCE-shaped)` (diferencias centrales) y `D(filas_Python)` (diferenciación automática): `4.2561794089124305e-09`; la columna de innovación monetaria tiene error máximo `1.44771306054281e-10`.

**Interpretación controlada:** queda comprobada numéricamente la composición del operador de transformación de filas *entre implementaciones Python*. No se ha llamado al kernel Lean para evaluar las 33 derivadas de `EconomicModel.lean`, ni se ha demostrado que las transcripciones Python correspondan funcionalmente a ellas. Las identificaciones de invariancia de Schur bajo `T` se proponen por separado en `SourceAugmented34RowTransportSchurCandidate.lean`, compilado exitosamente sin `sorryAx` en [#43587381916](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43587381916).

## Presupuesto condicional de error SOURCE

El nuevo programa define el presupuesto racional

`epsilon = min( (1-q33)/(4*33*||C33||_inf), (1-q34)/(4*34*||C34||_inf) )`.

Su representación decimal es `epsilon = 7.957357483780976e-05` **para el Jacobiano obtenido por diferencias centrales Python**, no para una matriz SOURCE arbitrariamente normalizada.

### Corrección fundamental: transportar las filas SOURCE ANTES de comparar las matrices

Las 33 filas originales SOURCE y las 33 filas Python pueden diferir por una permutación, escalados y cizallamientos de Euler. Por tanto, la obligación correcta NO es verificar `||J_SOURCE-Jhat_Python||_max<epsilon` directamente.

Sea la matriz SOURCE económica exacta `J_SOURCE = [[A_S,b_S],[c_S,0]]`, con las **mismas** coordenadas logarítmicas, instrumento h, herencia y punto. Se debe construir y demostrar invertible el operador de filas `T` en la raíz económica SOURCE. El objeto comparable es

`J_SOURCE_transportado = diag(T,1) J_SOURCE = [[T A_S,T b_S],[c_S,0]]`.

**Solo si** las 1156 entradas del `J_SOURCE_transportado` están encerradas con error absoluto individual `< epsilon` respecto de `Jhat_Python` racionalizado, entonces el defecto de Neumann sigue siendo menor que 1 y los bloques económico-físicos son invertibles, porque `T` también es invertible. Además, el escalar de Schur se conserva exactamente:

`-c_S (T A_S)^(-1) (T b_S) = -c_S A_S^(-1) b_S`.

La igualdad anterior es un hecho algebraico independiente de las cifras. La invariancia abstracta se DEMOSTRÓ en Lean en `SourceAugmented34RowTransportSchurCandidate.lean`, commit `110e72f3fa07877eb740face3df05f7847e96af6`, [CI #43587381916](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43587381916) **success**, módulo `COMPILED` y auditoría de axiomas sin `sorryAx`. La identificación de `T` con la transformación económica SOURCE/Python sigue PENDIENTE.

Para el segmento que conecta la matriz racionalizada con la matriz SOURCE **transportada**, ambos bloques permanecen invertibles, siempre que la misma cota de perturbación rija a lo largo de ese segmento. Si además permanece la estructura de bloques de esquina inferior derecha cero, el complemento de Schur es continuo y no puede cambiar de signo sin anularse.

**Esto es una implicación condicional, no un certificado SOURCE.** Ninguna rutina actual produce cotas de redondeo dirigidas de todas las entradas de `diag(T,1) D SOURCE`, ni demuestra que difieren menos del presupuesto. La igualdad funcional de las 33 filas tras la transformación, la invertibilidad real de `T` en un punto común, la diferenciabilidad de la continuación `tail`, la existencia exacta de la raíz (Newton–Kantorovich o equivalente), KKT global, equilibrio infinito y crecimiento permanecen abiertos.

## Obligaciones siguientes

1. Instanciar el mismo `Primitives`, `InheritedState`, carta logarítmica, reglas de continuidad y rama activa en SOURCE y Python, con pruebas de igualdad funcional (no solo transcripción de filas).
2. Diferenciar rigurosamente las 33 ecuaciones SOURCE con su `tail` real y la fila `nu_L`, manteniendo fijada la herencia. Construir cajas de derivadas con redondeo dirigido alrededor de una caja de raíz.
3. Verificar que la caja económica del Jacobiano pertenece estrictamente al presupuesto racional y que `F(z,h)=0` tiene una raíz en esa caja. La no singularidad por sí sola no establece existencia.
4. Pasar de regularidad local a las condiciones KKT completas, selección de rama, terminalidad, shocks monetarios diferenciados y efectos agregados verificables.

**Estatutos:** `DEMOSTRADO` únicamente para los defectos, invertibilidad y signo de las matrices *racionalizadas*; `NUMERICO` para la búsqueda de raíz, valores de pendiente y régimen Python; `PENDIENTE` para la derivada, raíz, invertibilidad y equilibrio del operador económico SOURCE.
