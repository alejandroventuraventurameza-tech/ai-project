# Protocolo científico y editorial — IE Project, versión Desktop → nube

**Fecha de especificación:** 7 de noviembre de 2026. **Origen:** [observaciones textuales del autor](OBSERVACIONES_DESKTOP_2026-11-07.md). **Estado:** plan de investigación y entrega, no un resultado probado. Referencia normativa: [issue #7](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7). Nunca presentar como ya implementado un instrumento sin una trayectoria validada.

## 0. Pregunta central, hipótesis y resultados que no debemos presuponer

**Pregunta:** ¿A través de qué canales de implementación monetaria y liquidez bancaria pueden los instrumentos del banco central alterar la financiación de firmas heterogéneas, su inversión y la eficiencia de la asignación intertemporal de capital, especialmente cuando una firma más productiva tiene una garantía relativamente limitada?

**Hipótesis a contrastar:** una política que reduzca costos efectivos de liquidez podría expandir la financiación factible de la firma más productiva y mejorar la asignación; el efecto total, el multiplicador de colateral, la trayectoria de producción y el largo plazo dependen del régimen y del ajuste de precios, patrimonio, demanda y expectativas. La rama B ya muestra crédito H creciente con capital H decreciente y dual H creciente: es una refutación de la versión incondicional del mecanismo favorable, no un error que deba ocultarse.

**Compromisos de evidencia:** diferenciar siempre DEMOSTRADO (mismo enunciado y supuestos), NUMÉRICO (modelo reducido especificado, tolerancias y horizonte), PROPUESTA (objetivo teórico no establecido) y PENDIENTE (puente económico/formal no verificado).

## 1. Mapa del banco central: cuatro shocks, una implementación coherente

| Objeto | Papel económico | Estado al 7-11-2026 | Tarea científica |
|---|---|---|---|
| Remuneración de reservas R^R | Ancla del corredor inferior / regla monetaria de precio | IRF a v_R=-10^-5 disponible | Mantener como baseline y precisar regla y feedback |
| Tasa interbancaria R^F | Resultado OTC en función de oferta/demanda de liquidez y corredor | Determinada endógenamente | No presentarla como shock independiente |
| Facilidad R^W = R^R + Delta | Techo del corredor | Modelada; derivada local para v_Delta | Generar IRF de ancho de corredor con equilibrio y checks |
| Cantidad de reservas M^pre | Instrumento de cantidad con contrapartida de operaciones de balance | Modelada; derivada local para v_M | IRF propia y cierre de banco central/Tesoro |
| Encaje rho | Fracción de reservas requeridas / restricciones de liquidación | rho=0.10 fijo en la IRF principal; derivada local v_rho | IRF de encaje y chequeo de factibilidad |
| Tasa de política separada | Concepto institucional potencialmente distinto del piso R^R | No identificada como control independiente del código revisado | Definir implementación y cierre antes de añadir otra ecuación |
| Balance sheet CB/Tesoro | Activos públicos, reservas, facilidad, operaciones de mercado abierto y fiscalidad | Identidades en el paper; deuda bruta no calibrada | Controlar consistencia activo-pasivo y neutralidad contable |

El vector de experimentos locales del manuscrito es v=(v_R,v_M,v_rho,v_Delta). **Una derivada direccional computada no es una IRF.** Para cada instrumento: shock de tamaño y unidad explícitos, mismos estados heredados, ley de innovaciones futuras, régimen, frontera, horizonte, solver, verificaciones, tabla y gráfica propios. Si la perturbación cruza una cara de complementariedad, recalcular la región; nunca forzar una solución de régimen inadmisible.

**Pregunta obligatoria para el autor:** ¿pretendemos identificar R^R como tasa de política operacional (floor) o especificar además un objetivo independiente de tasa? Evitar introducir un segundo instrumento sin una ecuación de implementación o financiarlo como magia.

## 2. Fricción de colateral, tamaño y productividad empresarial

En la especificación existente A_H=1.01>A_L=1, theta_H=0.15<theta_L=0.40. No basta esta ordenación para probar que H es una empresa "pequeña". Construir una tabla de verificación con capital instalado, patrimonio, consumo, deuda, empleo y tamaño productivo para cada firma antes de aplicar los adjetivos pequeña/grande.

**Contrato y presupuesto:**

\[
c_{i,t}+q_t k_{i,t+1}+a_{i,t}=N_{i,t}+b_{i,t},\qquad
R_t^L b_{i,t}\le H_{i,t}k_{i,t+1},
\]
\[
H_{i,t}=\theta_i(1-\delta)
\inf_{s'}\{\Pi_{t+1}(s')q_{t+1}(s')\}.
\]

En el caso con depósito empresarial cero y garantías activas, si n=N-c>0 y q>H/R^L:

\[
k_{i,t+1}=\frac{n_{i,t}}{q_t-H_{i,t}/R_t^L},\qquad
\frac{\partial k^{max}_{i,t+1}}{\partial R_t^L}
=-\frac{nH}{(R_t^L)^2(q-H/R_t^L)^2}<0.
\]

La segunda es una **derivada parcial a recursos y precios fijos**. La dinámica de equilibrio cambia también n, q, H y R^L. Una cara activa no implica necesariamente multiplicador estrictamente positivo, y crédito creciente no equivale a menor dual. Presentar ambos regímenes S/B y sus duales, sin seleccionar solo el favorable.

**Criterio de aceptación:** ninguna diapositiva afirma que "firma más productiva = más pequeña" o "menor tasa = colateral menos vinculante" sin verificar la variable y la condición correspondientes.

## 3. Mala asignación intertemporal, acumulación y crecimiento

Separar cinco objetos: (i) distribución de capital K_H/K_L, (ii) dispersión de retornos marginales, (iii) pérdida condicional de producción, (iv) trayectoria del **nivel** de producto, (v) tasa de crecimiento y bienestar.

\[
K_{t+1}=(1-\delta)K_t+I_t,\quad
\mathcal L_t=\log\frac{Y^{ef}_{t+1}}{Y_{t+1}},\quad
g_t=\log Y_t-\log Y_{t-1}.
\]

La medida de mala asignación existente es relativa al producto condicional con factores agregados del período siguiente; **no mide bienestar intertemporal**. Para cada shock y rama, graficar k_H, k_L, N_H, N_L, b_H, b_L, K, Y, \mathcal L y g_t con el calendario correcto.

**Prueba decisiva:** un aumento transitorio de g_t o un nuevo nivel asintótico Y* no prueba crecimiento endógeno sostenido. Si la diferencia de niveles logarítmicos converge, su diferencia primera tiende a cero. Con tecnología de rendimientos decrecientes y cierre estacionario, la afirmación de un mayor crecimiento de tendencia permanece abierta. Si este efecto forma parte del aporte central pretendido, deberá añadirse y verificarse un mecanismo explícito de productividad endógena, innovación, aprendizaje o entrada. No reetiquetar la transición como crecimiento tendencial.

## 4. Flujo circular, subetapas y catálogo completo de ecuaciones

**Tres figuras propias, coherentes entre sí:**

A. **Flujo circular macrofinanciero:** hogar trabajador, empresarios H/L, minoristas, productor de capital, bancos, mercado OTC, banco central/Tesoro. Distinguir flujos de bienes, trabajo, ingresos, crédito, depósitos, reservas, impuestos y garantías. La garantía es una restricción de capacidad y **no** un pago real necesariamente ejecutado.

B. **Timing de decisiones:** realización del estado y precios; producción con k_t predeterminado; repago de pasivos heredados; patrimonio y pagos; elección de consumo y capital para t+1 y cartera bancaria; pagos idiosincráticos; matching OTC y facilidad; reservas pospago; transición a t+1. Distinguir estados, controles y realizaciones aleatorias.

C. **Mecanismo IRF, separado S/B:** shock a precio/cantidad/regulación → bancos/OTC → RL y RD → presupuestos, KKT, patrimonio y garantía → capital elegido y producción futura; por otro canal, Euler/NKPC/empleo → Y_t corriente. Cada flecha debe llevar **ecuación literal, hipótesis de validez, signo condicional y archivo de prueba numérica**.

**Atlas matemático integral para paper y Beamer:** índice maestro por agente y mercados con: ID de ecuación, enunciado LaTeX, tabla de símbolos, unidades, timing, derivación, hipótesis, condición de esquina/interioridad, función en código/filas del residuo, estado Lean y gráfico donde aparece. No omitir hogar, empresas, capital, minoristas, bancos, OTC, Tesoro, regla monetaria ni market clearing.

## 5. IRF: de un DSGE no lineal a las curvas, sin saltos

**Algoritmo efectivamente usado:**

- code/irf/finite_irf.py: sistema no lineal del prefijo (33 incógnitas, 17+16 relaciones) por rama. Newton con Jacobiano de diferencias finitas centradas, eliminación lineal con pivoteo y backtracking; desde t=2, continuación recurrente local lineal previamente auditada.
- code/irf/compare_nonlinear_tail.py: trayectoria no lineal finita apilada mediante Newton disperso y spsolve; bloques jacobianos por diferencias finitas, búsqueda amortiguada, varias condiciones terminales; hasta T=640.
- code/v0m/: cotas/operadores con aritmética por intervalos y linealización formalmente separada. Estas verificaciones no sustituyen demostraciones económicas completas.
- code/irf/reproduce.py: ejecuta shocks, tolerancias y horizontes, valida residuos, genera CSV, dos figuras del paper y tabla TeX de forma reproducible.

**No se empleó value function iteration ni stochastic gradient descent para generar la IRF principal.** La evaluación retrospectiva de una recursión de valor bancario no es una optimización global probada.

La presentación debe derivar:

\[
F_r(Z,\mathbf v)=0,\qquad
D_ZF_r\, dZ+D_{\mathbf v}F_r\, d\mathbf v=0,
\quad dZ=-(D_ZF_r)^{-1}D_{\mathbf v}F_r\,d\mathbf v
\]

bajo rango completo y **un conjunto activo fijo**. Después explicar el paso no lineal de Newton J(z_n)\Delta z=-F(z_n), z_{n+1}=z_n+\alpha_n\Delta z, las condiciones terminales y las rutas de los CSV y gráficos.

El ejemplo del código debe ser real y enlazado al commit, con el selector de rama, la preparación del shock, la resolución y la transformación de niveles en 10^4 veces diferencias de tasas brutas o 100 veces diferencias logarítmicas. No mostrar pseudo-IRF inventadas.

## 6. El output negativo inicial como objeto de investigación

**Dato auditado:** producción inicial cae en las dos ramas; S ≈ -0.0000356 log %, B ≈ -0.0041422 log %, también en soluciones reducidas no lineales con T=640. La robustez no prueba ausencia de errores en bloques fuera del test.

**Cadena algebraica verificada en la trayectoria:** regla monetaria → precios bancarios → Euler del hogar → NKPC → precio real del insumo m_t → demanda laboral con k_{t} fijo → Y_t corriente. Bajo las hipótesis del diagnóstico:

\[
\Delta\log Y_0=\frac{\Delta\log m_0-\Delta\log C^W_0}{3}.
\]

En el caso auditado, la contribución futura de fijación de precios domina a la contemporánea y reduce m_0, con caída del trabajo y producto corrientes. Una identidad evaluada en una solución conjunta **no** es una descomposición causal ceteris paribus. No modificar ecuaciones ni parámetros para fabricar el signo intuitivo. Revisar además los 33 residuos frente a las FOC de los agentes, cumplimiento fiscal, solventación y valor bancario dinámico, y estabilidad del cierre terminal.

**Criterio de aceptación:** la sección de IRF abre con el resultado incómodo, verifica el signo, muestra ecuaciones, contribuciones y explicaciones alternativas, y declara las dudas restantes. No confundir el Y_0 que cae con el capital para Y_1.

## 7. Presentación académica sin límite artificial de diapositivas

Crear primero **un atlas maestro** que exhiba todos los problemas de optimización, ecuaciones, restricciones, condiciones de equilibrio, tablas de nomenclatura, flujo circular, cronología, metodología numérica, mecanismos completos y literatura. El autor pidió expresamente **no fijar la cantidad de diapositivas durante la construcción**. Después derivar de ese atlas una versión oral para los 30 minutos de exposición del turno final (y 15 para discusión) sin sacrificar las derivaciones clave; todo el material restante permanece como anexo técnico accesible.

Crear tablas homogéneas de notación: R brutas, r netas, nominal/real, promesas heredadas, t/t+1, H productiva vs H garantía, M reservas, m precio del insumo, rho encaje, theta pignorabilidad, Gamma costo de inversión vs H garantía, y duales económicos vs normalizados. Evitar colisiones y abreviaturas sin definición.

## 8. Prosa y bibliografía: aplicación material de la skill

Aplicar la skill redaccion-academica-diseccion-de-voces al manuscrito: no basta una mención en README. Cada sección debería ordenar **problema → literatura y vacío → hipótesis y decisión de modelación → definición → ecuación y prueba → evidencia → inferencia limitada → transición al siguiente bloque**.

**Rúbrica editorial por párrafo:** tópico inequívoco; sujeto/verbo concordantes; cronología y referentes claros; conectores lógicos que realmente expresan causa, concesión, contraste o consecuencia; una inferencia por bloque; notación homogénea; fuente primaria cotejada; sin prosa telegráfica ni redundancias; el párrafo posterior se sigue argumentalmente del anterior, no solo comienza con «por otro lado». La literatura debe presentar y discutir cada voz antes de una comparación propia, sin inflar la prioridad de nuestros resultados.

## 9. Secuencia y entregas de aceptación

| Puerta | Resultado a producir | Cómo se certifica |
|---|---|---|
| G0. Alcance | Contrato de afirmaciones: instrumental, tamaño, dinámica, crecimiento, status de ramas | Tablero DEMOSTRADO / NUMÉRICO / PENDIENTE, evidencia de cada afirmación |
| G1. Agentes | Flujos, balances, catálogo total, timing e identidades de colateral | Correspondencia con paper, 33 filas y mercados; revisión algebraica |
| G2. Métodos | Sistema F, Newton, continuación, algoritmo de IRF, código y tolerancias | Reproducción de salida y tests con hashes |
| G3. Políticas | Un experimento por herramienta que esté realmente implementada | Residuo, factibilidad, selección de régimen y contrapartida fiscal |
| G4. Dinámica | Capital, patrimonio, Y, pérdida, crecimiento y duración | Trayectorias comparables y no confundir niveles con crecimiento |
| G5. Mecanismo | Cada flecha/IRF con derivación y data | Matriz ecuación → signo → CSV → figura → argumento |
| G6. Redacción | Paper de 8–20 páginas de cuerpo, anexos con pruebas y literatura dialogada | Rúbrica de estilo y revisión bibliográfica humana |
| G7. Diseño | Beamer maestro libre + edición oral adaptada | Inspección visual PDF 100%, navegación y ensayo |
| G8. Formalización | Proposiciones del paper frente a declaraciones Lean del mismo alcance | Compilación y auditoría de axiomas y correspondencia exacta |
| G9. Integración | PDF y código versionados, README, prompts y manuscritos auténticos | CI, manifiesto de hashes, PR revisado, merge a main solo al aceptar |

**Criterio decisivo de alcance:** si el equilibrio completo, otros instrumentos o crecimiento endógeno sostenido no se verifican antes del cierre, publicarlos como **objetivos y extensiones explícitas**, mientras se entrega como resultado presente la IRF de remuneración de reservas y el análisis local S/B con sus límites. Un objetivo no es automáticamente un teorema.
