# IE Project: ocho filas empresariales SOURCE/Python y el shear de garantia (10-XI-2026)

**Naturaleza:** estudio de correspondencia algebraica condicionado a la identificacion de estados, parametros y funcion de produccion. El ejecutor fuente no ha sido conectado integralmente a Python. Este documento complementa, pero no reemplaza, el registro de las 25 transformaciones candidatas previas.

## 1. Orden y dominio

El orden SOURCE de presupuestos/Euler H-L en fechas 0 y 1 es \`(0,1,2,3,17,18,19,20)\`. Su imagen Python es \`(0,3,1,4,17,19,18,20)\`. Los seis renglones \`SOURCE (0,1,2,3,17,18)\` tienen formulas transcritas de identidad en niveles, al usar las mismas funciones de ganancia, riqueza e inversion que los operadores reducidos. La rama S solo modifica la Euler de L en fecha cero; desde fecha uno las dos ramas imponen colateral vinculante.

La identidad de presupuestos SOURCE es:

\`\`\`text
c_i,t + q_t*k_i,t+1 - F_i,t+1/RL_t
 - [profit_i,t+(1-delta)*q_t*k_i,t-F_i,t/Pi_t]=0.
\`\`\`

En fecha uno Python sustituye \`F_i,2=theta_i*J2*k_i,2\`, lo cual equivale a usar el precio efectivo \`q1-theta_i*J2/RL1\` bajo esa igualdad nominal; no equivale a imponer la garantia fisica \`J2=(1-delta)*Pi2*q2\` fuera del conjunto de ceros.

## 2. Euler de fecha uno: identidad exacta de diferencia

Defina \`A2=(1-delta)*Pi2*q2\` y \`m_i=beta_E*(c_i,1/c_i,2)^sigma_E\`, siempre con \`Pi2>0, RL1>0\`. La Euler SOURCE de cada tipo utiliza \`theta_i*A2\`, mientras que el prefijo Python usa \`theta_i*J2\` en el rendimiento de deuda y de capital. En consecuencia:

\`\`\`text
F_SOURCE_i1 - G_Python_i1
   = theta_i*(J2-A2)*(1/RL1-m_i/Pi2).      (S1)
\`\`\`

Esta identidad es exacta en niveles, tambien fuera de la raiz. Sea \`g=log(J2/A2)\` la fila 21 Python; para \`A2,J2>0\`, \`J2-A2=A2*expm1(g)\`. Defina \`h(g)=expm1(g)/g\` para \`g !=0\` y \`h(0)=1\`. Entonces:

\`\`\`text
F_SOURCE_i1 = G_Python_i1 +
  [theta_i*A2*(1/RL1-m_i/Pi2)*h(g)]*g.
\`\`\`

En una raiz \`g=0\`, la diferencia de diferenciales se reduce a:

\`\`\`text
D F_SOURCE_i1 = D G_Python_i1
     + theta_i*A2*(1/RL1-m_i/Pi2)*D g.   (S2)
\`\`\`

La operacion \`(G_EulerH,G_EulerL,g) -> (G_EulerH+a_H*g,G_EulerL+a_L*g,g)\` es un shear triangular con determinante 1. Ello NO prueba el rango del Jacobiano 33x33 completo ni la existencia de \`D psi\` entre coordenadas.

## 3. Nueva prueba y control CI

El auditor \`code/irf/audit_source_firm_budget_euler_shear.py\` contrasta las seis filas directas y las dos Euler corregidas, en ambas ramas, cinco intervenciones (cero mas cuatro instrumentos), tres puntos incluidos dos fuera de raiz y las 33 columnas de derivadas numericas. Comprueba tambien el factor de (S2) en la carta estacionaria. Salida: \`code/irf/output/source_firm_budget_euler_shear_audit.json\`, con SHA256, errores y limites de validez.

Los dos nuevos lemas del fichero \`HandStencilPledgeRowEquivalenceCandidate.lean\` son: \`source_binding_euler_minus_common_face_is_pledge_shear\` (identidad literal de Euler) y \`source_firm_budget_with_common_face\` (presupuesto con cara comun condicionado a \`F_i=theta_i*J*k_i\`). Se debe inspeccionar el **SHA y los logs Lean** antes de clasificarlos DEMOSTRADO; el hecho de que el script Python pase no los certifica. Ningun lema prueba el equilibrio intertemporal completo.

## 4. Ledger de verificacion

Las nueve filas de factores log/nivel, dieciseis de igualdad de forma y ocho empresariales cubren ahora **33 de 33 filas como propuestas**, no como equivalencia ya demostrada. Falta una unica carta \`psi\`, coincidencia de \`LocalPrefixDateData\` con las variables Python (historia, productividad, politica, OTC, patrimonio), las transformaciones funcionales en vecindad de la raiz, invertibilidad de \`T,D psi\`, Jacobiano SOURCE y las pruebas independientes de optimalidad global, transversalidad y crecimiento. La condicion numero 34 del dual L es de **frontera S/B**, no debe agregarse artificialmente en la rama B.

**Estatus: candidato de puente parcial. PR #2 permanece draft; main intacta.**
