# Mapa maestro de refinamiento: IE Project

> **Fecha de auditoría:** 7 de noviembre de 2026 · **Punto de partida:** `66c308ec6e0bbf2aa5d6e292282fb1da2100c7c1`  
> **Rama de trabajo:** `work/lean-ci-validation-otc-20261106` · **Integración propuesta:** [PR #2](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/2) (borrador, no fusionar sin pasar compuertas).  
> **Norma vinculante:** [issue #7](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7), entrega final 26 de noviembre de 2026, 22:00, Lima. Cuerpo del paper 8–20 páginas, referencias y anexos excluidos; 11 pt y márgenes de 1 pulgada. Presentación final originalmente programada el 30 de octubre (30 minutos de exposición + 15 de discusión); esa fecha ya pasó.

## Requisitos recuperados del trabajo en Desktop

El autor aportó sus observaciones originales en [docs/OBSERVACIONES_DESKTOP_2026-11-07.md](docs/OBSERVACIONES_DESKTOP_2026-11-07.md), conservadas como transcripción proporcionada en el chat, sin atribuirles una fecha original no recuperada. Su traducción a pruebas verificables está en [docs/PROTOCOLO_CIENTIFICO_DESKTOP_2026-11-07.md](docs/PROTOCOLO_CIENTIFICO_DESKTOP_2026-11-07.md).

**Corrección de alcance:** el proyecto pretende estudiar el conjunto de instrumentos monetarios y su interacción con el colateral y la asignación dinámica, no únicamente la IRF vigente de remuneración. Dicho conjunto debe separarse entre controles implementados, precios endógenos, derivadas locales y experimentos dinámicos realmente calculados. El vínculo entre mala asignación y crecimiento endógeno sostenido está por demostrar; no lo inferiremos de una transición de niveles.

**Corrección metodológica:** las IRF actuales se basan en Newton para un prefijo no lineal de 33 incógnitas, continuación lineal local y validación adicional con Newton disperso hasta T=640. No se generaron por stochastic gradient descent ni por value function iteration. Estos métodos, las tolerancias y los archivos del solver deben explicarse en la exposición.

**Corrección de diseño:** construir **sin tope predeterminado de diapositivas** una presentación maestra con todos los paradigmas de optimización, ecuaciones, timing, diagramas, código y pruebas. Solo al finalizar se derivará una versión oral para el turno de aproximadamente 30 minutos más 15 de discusión. No se fija la estructura de la investigación por conveniencia estética.

**Corrección editorial:** la skill de disección de voces se aplicará mediante reescritura efectiva, controlando concordancia, lógica interparrafal, conectores, definiciones y transición entre secciones; su instalación sola no cuenta como revisión.

## Diagnóstico documentado

| Material actual | Evidencia y brecha |
|---|---|
| Manuscrito | `paper/paper.tex`; PDF ~132 páginas. La bibliografía antecede a los apéndices y estos comienzan aproximadamente en p. 46. Debe reescribirse y dejarse un cuerpo entre 8 y 20 páginas; las demostraciones técnicas completas se trasladan a anexos, no se eliminan. |
| Figuras | `paper/figures/irf_transmission.{png,pdf}` y `irf_real_allocation.{png,pdf}` son las dos IRF reales. `.github/assets/ie-transmission.svg` es esquema lineal del README; no se localizan tres diagramas circulares de agentes versionados en esta rama ni en las ramas históricas inspeccionadas. |
| Beamer | `slides/final.tex`: 24 cuadros, dos al final en anexo; solamente **una** diapositiva de literatura y dos figuras IRF; sin figura circular del sistema económico. Contiene una comparación Lean de alcance, pero no es todavía una correspondencia uno-a-uno del enunciado central. |
| Literatura | `paper/paper.tex` § Literatura relacionada: cuatro antecedentes nucleares y cuadro de nueve trabajos; `paper/references.bib`: 17 entradas. Hace falta reconstrucción argumentativa y auditoría externa de versiones, ecuaciones y prioridad científica. |
| Lean | 71 candidatos compilados en campaña aislada y sin `sorryAx` en declaraciones auditadas. `paper/result_ledger.json` inventaría 57 resultados sin correspondencia integral exacta con Lean. |
| Simulaciones | `python code/verify.py` y `code/irf/` reproducen IRF y contrastes del sistema reducido; comparación no lineal finita T=640 y trazabilidad OTC/empresa/Phillips. Experimento: innovación en remuneración `v_R=-1e-5`, **no shock de encaje** (`rho=0.10` fijo). |
| Alcance científico | `prop:local_macro_multiplicity` afirma dos equilibrios locales completos en la prueba escrita; los reportes separados registran la correspondencia con el equilibrio dinámico completo como obligación pendiente. Hay que reconciliar este alcance ANTES de escribir la conclusión. |
| Evidencia humana | `hand/README.md` sigue marcando apéndice manuscrito pendiente; no presentar un texto tipografiado como revisión manual del autor. |

## Decisión editorial central

El paper y las diapositivas deben contar la MISMA historia: **remuneración de reservas → liquidación OTC → tasas bancarias → crédito, patrimonio y colateral por empresa → elección de capital → producción y pérdida asignativa, distinguiendo S/B**. Una flecha siempre lleva una etiqueta de ecuación, una condición de validez, un signo (si se verificó) y un dato/figura de contraste.

No elevar una identidad contable a descomposición causal; no elevar una solución del sistema reducido a equilibrio dinámico pleno; no llamar evidencia peruana a parámetros ilustrativos; no confundir capital elegido para t+1 con producto corriente en t; no usar la palabra «encaje» para el shock a remuneración.

## Fases y compuertas

### F0 · Verdad económica y arquitectura de resultados (CRÍTICA)

- [ ] Revisar `prop:local_macro_multiplicity` y cada afirmación del cuerpo: objeto exacto, supuestos, demostración en papel, verificación en código, existencia de prueba Lean exacta, límites.
- [ ] Resolver de modo explícito «teorema del sistema reducido» frente a «equilibrio dinámico completo»; cuando falta el puente, reducir el enunciado o demostrarlo, no encubrirlo.
- [ ] Revisar duales KKT originales frente a multiplicadores normalizados; condición activa no implica dual estrictamente positivo.
- [ ] Fijar un **result ledger editorial**: `ID → fuente → supuestos → conclusión → ecuaciones → código/figura → Lean exacto → estado`. Conciliar 57 resultados del artículo con los 71 módulos Lean candidatos.
- **Salida:** `docs/RESULTADOS_Y_ALCANCE.md`, tabla de teoremas de igual alcance y decisiones de redacción firmadas para revisión del autor.
- **Aceptación:** ningún resultado central se presenta más fuerte que sus pruebas.

### F1 · Tres figuras de arquitectura del modelo (CRÍTICA)

1. **Flujo circular de la economía:** hogar (depósitos/propiedad/consumo/trabajo); empresas H y L (empleo, capital, préstamo); productores de capital y bienes; bancos comerciales; mercado OTC; banco central/Tesoro. Distinguir bienes, flujos financieros, stocks heredados, promesas nominales, pagos y remuneración de reservas, con flechas dobles cuando correspondan. Fuente: § Modelo y `eq:firmbudget`, `eq:bankbalance`, `eq:resources`.
2. **Cronología de contratos y liquidación dentro de t:** realización de s_t, producción y repago heredado, patrimonio, contratos nuevos y cartera bancaria, pagos idiosincráticos, matching OTC/facilidad, renovación para t+1. Basarse en la enumeración literal § Modelo, «Orden de acontecimientos».
3. **Diagrama de transmisión IRF ramificada:** shock `v_R<0` → tasas `R^R,R^F,R^L,R^D` → préstamos/multiplicadores → `N-c`, `q-H/R^L` → capital H y pérdida asignativa S/B; canal paralelo Euler–Phillips–salarios–producto corriente. Etiquetar cada flecha con la ecuación y signo condicionado.
- [ ] Implementar en fuentes vectoriales editables (TikZ/SVG/Python) y exportar `.pdf` para Beamer/paper y `.svg/.png` para README.
- [ ] Verificar legibilidad 16:9, transiciones de tiempo, unidades y rutas de archivo.
- **Salida:** carpeta `paper/figures/architecture/` (3 fuentes+exportaciones), figura circular al inicio del Modelo, cronología en la exposición y mapa de mecanismo junto a las IRF.
- **Aceptación:** figuras coherentes con las ecuaciones reales, no infografías decorativas.

### F2 · Literatura como argumento, no catálogo

- [ ] Crear dossier por trabajo central con: pregunta y resultado preciso, ecuación/hipótesis que usamos, qué NO demuestra, relación con este modelo y versión/página cotejada.
- [ ] Ejes: González–Nuño–Thaler (heterogeneidad y mala asignación); Bianchi–Bigio (reservas y gestión bancaria); Bigio–Sannikov (implementación NK); Bianchi–Bigio 2026 (liquidación/matching); Asriyan y otros (asignación del crédito, patrimonio y medición de productividad).
- [ ] Construir matriz visual «Literatura × bloques del modelo × diferencia propia» y dos párrafos de contribución: qué ya sabe la literatura y qué pregunta limitada responde el sistema reducido actual.
- [ ] Verificar cada metadato, versión, localizador y prioridad; no inflar novedad.
- **Salida:** `docs/LITERATURA_Y_CONTRIBUCION.md`, sección reescrita del paper, 2–3 diapositivas argumentativas.
- **Aceptación:** un lector puede distinguir enunciados de los autores de elecciones y conclusiones propias.

### F3 · Índice de ecuaciones y derivaciones de transmisión

| Flecha | Ecuaciones actualmente etiquetadas | Pregunta que debe responder |
|---|---|---|
| Regla monetaria → OTC | Regla de § Instrumentos monetarios y `eq:IBrate` | ¿Cómo cambian matching, reservas y tasa de préstamo tras la innovación? |
| OTC → spreads | `eq:bankFOCL`, `eq:bankFOCD`, `eq:spread` | ¿Qué es endógeno y bajo qué interioridad se obtiene el signo? |
| Spreads → firma | `eq:firmbudget`, `eq:collateral`, `eq:capitalFOC`, `eq:loanFOC` | ¿Qué limita deuda y capital? ¿Qué papel juega el dual? |
| Crédito → capital | Colateral activo + presupuesto: `k'=(N-c)/(q-H/RL)` | ¿Por qué crédito H sube y capital H baja en B? |
| Capital y empleo → mala asignación | `eq:production`, `eq:dynamic_loss_at_optimal_labor`, `eq:loss_relative_capital_derivative` | ¿Qué cambia en eficiencia asignativa frente a escala? |
| Consumo/precios → producto corriente | `eq:nkpc`, Euler y demanda laboral | ¿Por qué el producto puede caer al impacto? |

- [ ] Para cada fila: derivación matemática paso a paso, condiciones de signo, comparativo S/B, dato/CSV, prueba de identidad numérica, limitación causal.
- **Salida:** `docs/MATRIZ_ECUACIONES_MECANISMOS.md` y slides con ecuaciones encadenadas.
- **Aceptación:** toda flecha tiene soporte matemático auditado y ninguna etiqueta de ecuación es inventada.

### F4 · Simulaciones explicadas y figuras IRF con trazabilidad

- [ ] Presentar la solución numérica: 33 incógnitas, 17+16 ecuaciones del prefijo, dos conjuntos activos y continuación desde t>=2.
- [ ] Explicar por qué la referencia del prefijo no es un estado estacionario completo; el shock y las unidades (pb sin anualizar y 100 Δlog); los estados heredados; la diferencia entre elección de capital t y producción t.
- [ ] Usar las dos figuras IRF originales, pero remaquetar por narrativa: 1) instrumento→liquidez→tasas, 2) tasas→crédito→dual, 3) patrimonio→inversión→asignación, 4) Euler/Phillips→producto.
- [ ] Etiquetar S/B y el mensaje principal por panel; no exagerar efectos minúsculos mediante escalas truncadas sin explicitar.
- [ ] Adjuntar tabla con condiciones terminales, tolerancias, márgenes, errores, sensibilidad -0.1/-1pb y contraste T=640; mantener sensibilidad fallida de -1pb.
- **Salida:** `paper/figures/` actualizado únicamente desde generadores y CSV reproducibles; `docs/METODO_SIMULACION_IRF.md`, slides de diagnóstico.
- **Aceptación:** `python code/verify.py` pasa; toda cifra del texto se reproduce automáticamente; límites declarados.

### F5 · Reescritura integral del paper y aplicación de la skill

**Usar** `redaccion-academica-diseccion-de-voces` con su fuente `references/metodo-original.md`. No basta con tenerla instalada; aplicar a introducción, diálogo de literatura, puente entre modelo y resultados, narración de simulaciones y conclusiones.

- [ ] Escribir el argumento maestro por secciones; cada una abre con pregunta, deriva ecuaciones, presenta evidencia y cierra con inferencia/puente.
- [ ] Fijar convención de símbolos nominales/reales, horizonte, tasas brutas, balances y duales; mantener términos consistentes en texto, gráfico, código y Beamer.
- [ ] Limitar **cuerpo** a 8–20 páginas sin reducir fuente ni márgenes. Referencias y anexos técnicos extensos pueden conservar detalle.
- [ ] Distribución inicial orientativa (páginas del cuerpo): introducción 2, literatura 2, modelo y agentes 4, resultado y prueba 4, método 2, IRF y mecanismo 3, discusión 1, conclusión 1 = 19.
- [ ] Revisión externa de citas y paginación, sin inferir títulos ni fechas de versión.
- **Salida:** `paper/paper.tex` y PDF coherentes, anexos de pruebas, bib revisado.
- **Aceptación:** extensión oficial, teorema(s) correctos, símbolos definidos, texto dialogado, todos los gráficos motivados e interpretados.

### F6 · Beamer formal y diseño de exposición

La consigna histórica establece **aprox. 30 minutos de exposición y 15 de discusión**, pero el autor pidió explícitamente **no limitar de antemano el número de diapositivas**. El deck actual (24 cuadros) es punto de partida, no límite estético.
- [ ] Diseñar primero un atlas maestro de tantas diapositivas como requiera la exposición completa: primitivas y objetivos de cada agente, ecuaciones, timing, mercado OTC, instrumentos, pruebas, métodos numéricos, IRF, literatura y código. Después preparar una edición oral y anexos sin sacrificar legibilidad.
- [ ] Secuencia sugerida: pregunta–contribución; 2–3 slides de literatura; flujo circular; cronología; optimización y balances; OTC y tasas; definición de equilibrio; proposición y prueba; shock; IRF con mecanismo y ecuaciones por flecha; simulaciones y robustez; Lean literal; revisión manuscrita real; críticas; conclusión.
- [ ] Mantener *notación idéntica* al paper; no recrear números a mano; no reducir tamaño de letra para encajar varias pruebas en una página.
- [ ] Cotejar literalmente el enunciado del paper y el enunciado Lean, con hipótesis añadidas visiblemente distintas.
- [ ] El contenido manuscrito debe producirlo el autor; no fabricarlo. Dejar diapositiva marcada pendiente hasta existir evidencia real.
- **Salida:** `slides/final.tex`, PDF, guion de defensa, respaldo técnico.
- **Aceptación:** cada slide satisface «ecuación derivada, figura interpretada o afirmación probada», y el relato cumple la duración.

### F7 · Release reproducible

- [ ] Mantener `.github/workflows/build.yml` oficial intacto; checks extra en `editorial-qa.yml`.
- [ ] Validar en una revisión Git fija: `python code/verify.py`; Lean en versión fijada; cuatro PDFs; referencias; tipografía, recortes, colores y accesibilidad; hashes y sincronía PDF↔TeX.
- [ ] Completar `hand/` con derivaciones auténticas, cotejar `prompts.md` y veredictos, tabla exacta de formalización, atribuciones de literatura.
- [ ] Revisión de PR #2, resolver conflictos, fusionar a `main` solo cuando las compuertas críticas estén cerradas.
- **Salida:** artefactos finales y manifiesto de reproducibilidad por SHA y fecha.
- **Aceptación:** lo publicado en `main` reproduce todas las afirmaciones que declara y cumple el issue #7; vacíos no demostrables se muestran sin ambigüedad.

## Compuertas adicionales que recuperan el objetivo macroeconómico

- **Instrumentos:** no llamar «policy rate» a la tasa interbancaria endógena sin definición. Explicar la regla de remuneración R^R, facilidad R^W=R^R+Delta, cantidad de reservas, OMO, balance, encaje rho y shocks diferenciados. Exigir IRF propias antes de afirmar efectos de otros instrumentos.
- **Firmas pequeñas y productivas:** constatar escalas y patrimonios antes de dar por hecho que la firma más productiva es más pequeña; presentar la restricción de colateral y duales por rama.
- **Mala asignación y crecimiento:** seguir K_t, distribución de capital, patrimonio, Y_t, pérdida condicional y g_t en toda la trayectoria; distinguir transitorios, diferencias de nivel, bienestar y crecimiento sostenido; este último no está demostrado actualmente.
- **Mecanismos:** una flecha solo se acepta si está identificada una ecuación, sus supuestos, una derivación, una prueba o identidad numérica y un signo condicional verificable.
- **No linealidad y solver:** derivar F_r(Z,v)=0, inversión local de Jacobianos, Newton amortiguado, continuación, comprobación de residuo y robustez con horizonte T=640, vinculando el código exacto y las figuras.
- **Producto inicial negativo:** mantener el signo, contrastar Euler–Phillips–trabajo y todas las condiciones pendientes; no modificar parámetros para conseguir una IRF más agradable.
- **Prosa:** revisar primero estructura del argumento y transiciones; luego sintaxis, concordancia, conectores y estilo. No cambiar por intuición ninguna proposición o ecuación validada.

## Prioridad inmediata

1. Resolver alcance de la proposición central y de las 57 declaraciones frente a Lean.
2. Recuperar/reconstruir diagramas de agentes y mecanismos con notación y ecuaciones.
3. Reescribir literatura/contribución y estructura de resultados.
4. Integrar y explicar el algoritmo IRF, robustez y lectura S/B.
5. Compactar paper e implementar Beamer desde la misma arquitectura.
6. Completar manuscrito del autor, revisión visual y merge aprobado.

**Punto de decisión científico:** si no se cierra la correspondencia con equilibrio competitivo infinito, el aporte principal se formula rigurosamente como resultado condicional del sistema reducido con hipótesis explícitas. No se usa diseño atractivo para ocultar esa diferencia.
