# Del alivio de colateral al crecimiento: obligacion estructural pendiente

**Estatus:** nota de diseno de investigacion, no teorema de crecimiento
ni calibracion empirica. No modifica las ecuaciones economicas
existentes, las IRF o sus resultados.

## 1. La heterogeneidad de firmas del caso ilustrativo SI apunta al mecanismo deseado

La fuente numerica `code/v0m/cotas_2026_10_15/verified_linear_operator.py:steady()`
establece en orden `[H,L]`:
`technology=[1.01,1.00]`,
`pledgeability=[0.15,0.40]` y
`mass=[0.5,0.5]`. En la construccion estacionaria del mismo
archivo, evaluada con aritmetica ordinaria solo como control
orientativo, se obtiene
`K_H aproximadamente 11.67` y
`K_L aproximadamente 19.39`.
Son valores *ilustrativos*, no intervalos certificados ni
estimas empiricas. Este orden conserva la intuicion:
`A_H>A_L`, `theta_H<theta_L` y `K_H<K_L`.
La firma relativamente pequena y productiva es H, no L.

`EconomicModel.lean` mantiene literalmente
`productivity_order : productivity L < productivity H`.
La prueba de que la firma H esta en efecto mas restringida
en una asignacion concreta exige ademas examinar sus
dualidades y la restriccion activa; `theta_H<theta_L`
por si sola no implica que una KKT sea vinculante.

## 2. Mala asignacion estatica, efecto nivel y efecto crecimiento NO son sinonimos

Con tecnologia `Y_i=A_i K_i^alpha L_i^beta`,
manteniendo fijos trabajo por firma y capital agregado
`K=K_H+K_L` (o con masas incorporadas explicitamente),
una reasignacion local `dK_H=-dK_L` tiene efecto

```text
dY = (MPK_H - MPK_L) dK_H,
MPK_i = alpha * A_i * K_i^(alpha-1) * L_i^beta.
```

Un `A_H>A_L` no asegura `MPK_H>MPK_L` para
todo `K_H,K_L`; es necesario comprobar el margen
de productos marginales en la asignacion. Si el banco
central reduce el costo de credito y aumenta el capital
de H, la mejora asignativa puede depender de ese margen,
de otras decisiones endogenas, de recursos de intermediacion,
de trabajo, y de la rama S/B seleccionada.

Una mejora del PRODUCTO DE LARGO PLAZO es una afirmacion
`Y_infty^(policy)>Y_infty^(base)`, condicionada a existencia
y comparabilidad de ambas trayectorias.
Una mejora de la TASA DE CRECIMIENTO DE LARGO PLAZO es
otra afirmacion:

```text
g_inf = lim_(T -> inf) (log Y_T - log Y_0)/T.
```

**Obstruccion matematica:** si `0<m<=Y_t<=M<infty`
para todos los `t` de una trayectoria de equilibrio
(uniformemente acotada y estrictamente positiva), entonces
`abs(log(Y_T/Y_0))/T <= log(M/m)/T -> 0`.
En particular, si `Y_t` converge a un estado
estacionario positivo, `g_inf=0`.
Una politica que cambia solamente el estado
estacionario puede generar un efecto permanente
de NIVEL sin cambiar la tasa tendencial de crecimiento.
Es una proposicion condicional; la acotacion de
`Y_t` para toda trayectoria competitiva no se
ha demostrado en el archivo fuente.

## 3. Frontera del modelo actual

`EconomicModel.lean` fija
`aggregateProductivity : S -> Real` sobre estados
Markov y `productivity : FirmType -> Real` como
primitivas. En el nucleo actual no se ha especificado
una ley de acumulacion ENDOGENA del conocimiento
o la calidad tecnologica de firmas financiada por
credito. El estado recurrente y la linearizacion
local tampoco construyen por si mismos una tendencia
de productividad en crecimiento balanceado.

El manuscrito `paper/paper.tex` ya declara que el
nucleo no incorpora esos motores de crecimiento; este
documento convierte esa limitacion en una compuerta
matematica explicita y separa efectos de nivel y de tasa.

## 4. Extension candidata: innovacion financiada con restriccion de colateral

Una posibilidad coherente con el objetivo del usuario,
**no implementada ni demostrada**, consiste en introducir
inversion en innovacion `R_{i,t} >= 0`, con recursos
agregados usados tambien por `sum_i mass_i R_{i,t}`
y una tecnologia de conocimiento, por ejemplo

```text
A_(i,t+1) = A_(i,t) * (1 + chi_i R_(i,t)/Y_(i,t)),
chi_i > 0, Y_(i,t) > 0.
```

La ley exige una interpretacion economica de `R/Y`
y que el gasto no se contabilice dos veces. La
inversion innovadora de la firma H debe competir
por liquidez con capital fisico, y debe especificarse
si `R` es financiable, pignorable o no pignorable.
Si las restricciones impiden que H financie
`R_H` aun cuando su retorno privado/social es
alto, una relajacion FINANCIERA persistente puede,
bajo condiciones adicionales, elevar su intensidad
`R_H/Y_H` y su tasa de innovacion.

**No basta escribir esa ecuacion.** Para integrarla
al DSGE/Markov son necesarios: problemas
intertemporales de firmas y bancos con nuevas KKT
y suficiencia; precio sombra de productividad;
law of motion y agregacion de `A_i`; restriccion
de recursos; tratamiento de spillovers si existen;
equilibrio estacionario en variables detrendizadas
(o distribucion relativa estacionaria); continuidad
y terminalidad; seguridad de dominios positivos;
contrafactual de la MISMA regla monetaria con
innovacion no distorsionada, y una demostracion
`g_inf(policy)>g_inf(base)` en un conjunto claro
de parametros. El crecimiento de `A_H/A_L` puede
impedir estabilidad de participaciones; no asumir
automatica convergencia de la distribucion.

## 5. Plan de implementacion sin confundir evidencia

1. **Cerrar el nucleo actual:** equivalencia
   fuente Python/Lean para las 34 filas; raiz
   matematica formal; prefijos completos; solucion
   competitiva y condiciones terminales.
2. **Validar el mecanismo transitorio:** demostrar
   cuando `MPK_H>MPK_L` y documentar
   `R^{policy} -> credito_H -> K_H -> Y`
   por rama S/B, con costos de intermediacion.
3. **Definir version 2 de crecimiento:** decidir
   si aprendizaje, innovacion, entrada o seleccion
   generan `A_t` endogeno, con unidades
   y politica instrument-specific.
4. **Resolver crecimiento balanceado:** proponer
   una transformacion de estados al nuevo
   steady detrendizado y teorema para tasa
   permanente. No llamar `g_inf>0` a una
   diferencia de niveles ni a una IRF de horizonte
   finito.

**Regla editorial:** hasta esa extension
estructural y su prueba, el manuscrito y las
diapositivas deben describir las ganancias como
`efectos sobre inversion, eficiencia asignativa,
produccion y transicion condicionales`, no como
`crecimiento endogeno permanente demostrado`.
