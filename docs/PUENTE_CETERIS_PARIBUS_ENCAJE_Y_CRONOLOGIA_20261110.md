# Encaje, liquidez bancaria y cronologia: puente de comparativas SOURCE

## Objeto y evidencia

Este anexo sigue la funcion **literal** del SOURCE
\`localPrefixReserveDepositRatio\` en \`lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean\` y la instancia de primitivas estacionarias e intervenidas
\`ProposedStationaryInterventionSourceBridge.intervenedPrimitives G v\`.
La ley de pagos binaria tiene pagos ±1/5 equiprobables, y el teorema comprobado
\`intervened_mean_absolute_payment\` establece \`E|omega|=1/5\` para toda
intervencion inicial \`v\`. Por ello la funcion de datos locales es exactamente

\[
h(\rho,R^D,R^R,\tau)=
\rho+\left(\frac{R^D}{R^R}-\rho\right)\zeta\frac{1-\tau}{1+\tau},
\qquad \zeta=\frac15.
\]

Esta identidad se demostro bajo el SOURCE real en el workflow
[Lean #42937592586](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42937592586),
sin \`sorryAx\`. **No** es una ecuacion que por si sola determine un equilibrio.

## Respuesta exacta de encaje a datos fijos

Para \(\varepsilon\in\mathbb R\), dejando fijos \(R^D,R^R,\tau\),

\[
h(\rho+\varepsilon)-h(\rho)
=\varepsilon m_\rho(\tau),\qquad
m_\rho(\tau)=1-\frac15\frac{1-\tau}{1+\tau}.
\]

Si \(0\le\tau\le1\), entonces \(0\le(1-\tau)/(1+\tau)\le1\) y por tanto

\[
\frac45\le m_\rho(\tau)\le1.
\]

En \(\tau=1/2\), \(m_\rho=1-1/15=14/15\). Un anuncio que eleve el coeficiente
de encaje de \(\rho=.10\) a \(\rho=.11\) eleva **directamente** \(h\) en \(0.01(14/15)=0.009333\ldots\) si se mantienen los demas argumentos de \`LocalPrefixDateData\`. Un aumento de 0.01 en una razon es un punto porcentual, no una variacion proporcional de uno por ciento.

Para una perturbacion solo del campo \`corridorWidth\` del registro de datos, sin cambiar controles ni tasas, la misma identidad SOURCE no varia:
\[
h(d[\Delta\leftarrow \Delta+\varepsilon])=h(d).
\]
Esto **no** implica IRF cero frente a un corredor distinto: \(\Delta\)
altera las pendientes OTC en otro bloque de ecuaciones y los
precios/controles son endogenos.

La prueba Lean de estas comparativas se incorporo como **CANDIDATO**
en commit \`328cb538\` con tres lemas:
\`source_intervened_reserve_ratio_exact_requirement_change\`,
\`source_intervened_reserve_ratio_requirement_coefficient_bounds\` y
\`source_intervened_reserve_ratio_no_direct_corridor_width\`.
No marcar DEMOSTRADO hasta obtener el gate verde y \`#print axioms\` del
SHA correspondiente. El segundo lema actualmente prueba positividad y
cota superior \(m_\rho\le1\); la cota mas fuerte \(m_\rho\ge4/5\) se
deduce analiticamente de la fraccion en \([0,1]\), pero todavia no
se declara como ese mismo teorema Lean.

## Dependencia respecto de otras variables

Si \(R^R>0\), \(R^D>0\) y \(0<\tau<1\), se obtiene a datos fijos:

\[
\frac{\partial h}{\partial R^R}
=-\frac15\,\frac{1-\tau}{1+\tau}\frac{R^D}{(R^R)^2}<0,
\qquad
\frac{\partial h}{\partial R^D}
=\frac15\,\frac{1-\tau}{1+\tau}\frac{1}{R^R}>0.
\]

Con \(\xi=R^D/R^R\),
\[
\frac{\partial h}{\partial\tau}
=-\frac25\frac{\xi-\rho}{(1+\tau)^2}.
\]
La derivada respecto a estrechez no tiene un signo universal: depende
de la comparacion \(\xi-\rho\).

El primer instrumento afecta una **innovacion de la ecuacion en
logaritmos de remuneracion de reservas**, no un cambio exogeno de
\(R^R\) manteniendo todo lo demas fijo. El segundo afecta analogamente
la ecuacion de cantidad de reservas. Los instrumentos tercero y cuarto
se suman en **niveles** a \(\rho_0\) y \(\Delta_0\).
La diferencia de unidad y su cronologia se demostraron para las
proyecciones \`source_stationary_datezero_four_policy_fields\` y
\`source_stationary_dateone_data_invariant_fixed_coordinates\`, ambos
compilados sin \`sorryAx\` en
[Lean #42941278175](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42941278175).

## De la derivada parcial a una IRF

El equilibrio es un sistema \(F(z,v)=0\), no una sola ecuacion de
liquidez. En una solucion regular y para el operador economico correcto,

\[
D_zF(z_*,0)\frac{dz}{dv}=-D_vF(z_*,0).
\]

Las identidades anteriores solo restringen algunas componentes de
\(D_vF\) y sus transmisiones locales. No determinan \(dz/dv\) porque
hay terminos de balance, oferta de credito, colateral, consumo y precios
que reaccionan simultaneamente. Debe demostrarse la igualdad funcional
de las 33 filas y la invertibilidad del Jacobiano del **SOURCE**
antes de transportar resultados del solucionador Python.

## Alcance adicional del benchmark

La equivalencia de las dos expresiones OTC demostradas con
\(\lambda=\log2\) exige \(\tau\le1\): el SOURCE tiene un ramo distinto
para \(\tau>1\). El auditor
\`frozen_same_predecessor_branch_audit.py\` ademas identifica una
exclusion local de la raiz S alrededor del antecedente comun. No
usar las comparativas parciales para concluir la existencia de dos
equilibrios intervenidos ni un mayor crecimiento permanente.

**PR #2 queda en borrador, sin fusionar \`main\`.**
