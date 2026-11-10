# IE Project: contrato de correspondencia funcional de 33 + 1 filas

**Corte:** 10 de noviembre de 2026. **Status:** auditoria analitica del codigo fuente, modulo de teoremas logaritmicos *CANDIDATO* hasta obtener kernel y reporte de axiomas del SHA pertinente. Las columnas `transformacion` y `compuerta` son tareas cientificas, no certificaciones globales. Modelo original: `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`; ejecutor numérico: `code/irf/finite_irf.py`. El mapa exacto de nombres, permutacion y fila 34 ya esta automatizado en `code/irf/audit_python_lean_prefix_row_permutation.py`.

## 1. Regla matematica para no comparar erróneamente Jacobianos

Sea $F(x)$ el vector de residuos fuente en coordenadas positivas y $G(z)$ el ejecutor reducido en desviaciones logaritmicas. No basta emparejar etiquetas de ecuaciones. Para equiparar sus ceros de forma local es necesario establecer por cada fila una identidad de la forma

\[G(z)=T(x(z))F(x(z)),\qquad x(z)=x_\star\odot\exp(z),\]

con $T$ cuadrada, diferenciable e invertible en la solucion, y un mapa de estados/controles bien definido. Si $F(x_\star)=0$, entonces la regla del producto implica

\[DG(0)=T(x_\star)\,DF(x_\star)\,Dx(0).\]

Las matrices de permutacion, las operaciones de fila entre las Euler y la fila de garantia, y los factores positivos de normalizacion deben hacerse visibles dentro de $T$. El jacobiano fuente no puede ser reemplazado por el de Python solo porque coincidan los ceros del sistema o porque CI sea verde.

**Dos identidades generales con dominio positivo:**

\[ \log r=0\iff r-1=0\qquad(r>0),\]

\[ \log(F/C)=0\iff F-C=0\qquad(F>0,\;C>0).\]

En cualquier raiz $F=C>0$, la derivada de $\log(F/C)$ coincide con $D(F-C)/C$. En cualquier raiz $r=1$ la derivada de $\log r$ coincide con la de $r-1$. Estas formulas pueden demostrarse por regla de la cadena y separan ceros de derivadas; la forma **source-specific** se esta pasando al kernel en `HandStencilPledgeRowEquivalenceCandidate.lean`.

## 2. Clasificacion por filas

El orden SOURCE es 0-indexado en `Fin 33`; el orden Python es el del vector producido por `prefix_residual()`. Indicaciones: **L** = probado como identidad literal en Lean, **N** = comprobado numericamente en el ejecutor, **C** = nuevo teorema candidato no chequeado aun, **O** = obliga demostracion o auditoria.

| Fila(s) SOURCE → Python | Bloque y representacion Python frente a SOURCE | Transformacion y evidencia |
|---|---|---|
| 0→0; 1→3 | Presupuesto H/L en fecha 0 | Residuo fuente en niveles, escritura de precio efectivo **L**; coincidencia de riqueza `aux0['N']` con riqueza SOURCE **O** |
| 2→1; 3→4 | Euler H/L, fecha 0 | B: Euler simplificada por fila de garantía **L + N** (shear invertible). S, L: Euler no restringida; coincidencia parametrica **O** |
| 4→2; 5→5 | Régimen H/L fecha 0 | B: diferencia de rostro nominal vs log cociente de rostros (**C** bajo positividad). S, L: $R^Lm_L/\Pi-1$ vs log de ese cociente (**C** bajo positividad) |
| 6→6 | Transición de rostro nominal bancario | Fuente diferencia en niveles, Python log cociente: normalizacion por rostro proyectado positivo **O** |
| 7→7 | Precio del productor de capital | $q-1-\varphi_I I/K$ en niveles; comparar costos/generador de inversión **O** |
| 8→8 | Contabilidad agregada de recursos | Nivel contra nivel; igualar agregacion, Rotemberg, costos, impuestos y fechas **O** |
| 9→9 | Oferta de trabajo | Fuente diferencia $w-\chi C_W^{\sigma_W}L^\varphi$, Python log cociente $w/(\chi C_WL)$: requiere $\sigma_W=\varphi=1$ en ilustracion, positividad y escala **O** |
| 10→10 | Euler del hogar | Fuente $1-R^Dm_W/\Pi$, Python $\log(R^Dm_W/\Pi)$: signos y ceros equivalentes en dominio positivo, factores CRS/CRRA pendientes **O** |
| 11→11 | NKPC Rotemberg | Residuo en niveles; alinear coeficientes de precio, descuento, output y shocks **O** |
| 12→12 | Regla de remuneración de reservas | Fuente diferencia de logs, Python log tasa realizada/tasa de regla; comprobar persistencia y fechas **O** |
| 13→13 | Regla de cantidad de reservas | Fuente diferencia de logs, Python log cociente sobre tasa de regla de cantidad **O** |
| 14→14; 15→15 | Precio OTC de crédito y depósitos | Niveles en ambos módulos; verificar pendientes de negociación, soporte de pagos, corredor y momentos **O** |
| 16→16 | Balance bancario | Niveles en ambos; en SOURCE ya existe lema de reconstruccion del balance con identidades de cantidades y ratio no nulo (**L** condicional). Igualdad de definiciones de depósitos y patrimonio Python **O** |
| 17→17; 18→19 | Presupuesto H/L fecha 1 | Misma identidad fuente generica de presupuesto (**L**), condicionada a la identificacion de variables futuras **O** |
| 19→18; 20→20 | Euler H/L fecha 1 | B: identidad de Euler reducida con garantia **L**; operacion de fila invertible en stencil numerico **N** |
| 21→21 | Garantia nominal comun fecha 1 | Fuente diferencia $J-(1-\delta)\Pi q$ vs log cociente; requiere positividad y escala **O** |
| 22→22; …; 32→32 | Once filas recurrentes bancarias, de capital, recursos, trabajo, hogar, precios y politica | Se repite la auditoria de tipos de filas 6–16, pero con estados de fecha 1, siguiente estado 2 y regla terminal; no basta la coincidencia de nombres **O** |

**Fila 34 fuera del vector `Fin 33`:** el residuo adicional de `augmentedBoundaryZeroResidual` es `localNormalizedCollateralDualL`, NO una nueva innovacion. Su valor diagnostico coincide numericamente con la formula fuente $1/R_L-\beta_E[c_{L,t}/c_{L,t+1}]^{\sigma_E}/\Pi_{t+1}$ sobre 160 transiciones de cada rama S/B (error maximo $2.22\times10^{-16}$, [Actions 42920743503](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42920743503)). En B tras el shock la ecuacion dual 34 **no es igual a cero**: es aprox. $3.2188\times10^{-5}$. El sistema aumentado con dual=0 es el problema de **frontera**, no el equilibrio B interior a su rama; imponerlo en B seria un error economico.

## 3. Ruta de cierre formal

El cierre exige, en este orden: (i) demostrar ceros y escala de las filas de regimen en el dominio positivo con Lean, (ii) completar las transformaciones de las otras filas con definiciones SOURCE exactas, fechas y parametros, (iii) construir y auditar la matriz compuesta de permutacion, shear y escalas positivas en el estacionario, (iv) relacionar el jacobiano y las seis coordenadas de la transicion fuente, (v) levantar la conclusion a un grafo no lineal C1 con radio y restricciones activas, (vi) demostrar optimizacion, pagos contingentes y condiciones terminales. Nada de ello es una prueba de crecimiento endogeno permanente por si mismo.

**Interpretacion economica:** equivalencia de una ecuacion de restricciones necesarias no implica suficiencia de equilibrio. Un sistema de estacionariedad, KKT y persistencia finita puede soportar comparativas de niveles sin generar una tasa de crecimiento tendencial distinta. Cualquier promesa de crecimiento permanente requiere especificar una ley endogena de acumulacion/tecnologia y sus hipotesis de estabilidad/transversalidad.
