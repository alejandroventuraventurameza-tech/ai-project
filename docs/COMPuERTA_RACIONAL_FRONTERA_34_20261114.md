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

## Presupuesto condicional de error SOURCE

El nuevo programa define el presupuesto racional

`epsilon = min( (1-q33)/(4*33*||C33||_inf), (1-q34)/(4*34*||C34||_inf) )`.

Su representación decimal es `epsilon = 7.957357483780976e-05`. **Si** todas las 1156 entradas del Jacobiano SOURCE real de dimensión 34 (y por ende de su bloque 33) están encerradas en la misma carta económica, idéntica herencia y el mismo punto, con error absoluto individual `< epsilon` frente a las matrices racionalizadas, entonces por la desigualdad submultiplicativa los defectos SOURCE de ambos bloques siguen estrictamente menores que 1.

Para el segmento que conecta la matriz racionalizada con la SOURCE, ambos bloques permanecen invertibles; suponiendo además la auténtica estructura de bloques SOURCE (esquina inferior derecha cero), la continuidad del complemento de Schur y la imposibilidad de cruzar cero conservan su signo estrictamente negativo.

**Esto es una implicación condicional, no un certificado SOURCE.** Ninguna rutina actual produce cotas de redondeo dirigidas de todas las entradas de `D SOURCE`, ni demuestra que difieren menos del presupuesto. La identidad semántica completa SOURCE/Python, diferenciabilidad de una continuación `tail` económicamente admisible, existencia exacta de la raíz (Newton–Kantorovich o equivalente), KKT global, equilibrio infinito y crecimiento de largo plazo permanecen abiertos.

## Obligaciones siguientes

1. Instanciar el mismo `Primitives`, `InheritedState`, carta logarítmica, reglas de continuidad y rama activa en SOURCE y Python, con pruebas de igualdad funcional (no solo transcripción de filas).
2. Diferenciar rigurosamente las 33 ecuaciones SOURCE con su `tail` real y la fila `nu_L`, manteniendo fijada la herencia. Construir cajas de derivadas con redondeo dirigido alrededor de una caja de raíz.
3. Verificar que la caja económica del Jacobiano pertenece estrictamente al presupuesto racional y que `F(z,h)=0` tiene una raíz en esa caja. La no singularidad por sí sola no establece existencia.
4. Pasar de regularidad local a las condiciones KKT completas, selección de rama, terminalidad, shocks monetarios diferenciados y efectos agregados verificables.

**Estatutos:** `DEMOSTRADO` únicamente para los defectos, invertibilidad y signo de las matrices *racionalizadas*; `NUMERICO` para la búsqueda de raíz, valores de pendiente y régimen Python; `PENDIENTE` para la derivada, raíz, invertibilidad y equilibrio del operador económico SOURCE.
