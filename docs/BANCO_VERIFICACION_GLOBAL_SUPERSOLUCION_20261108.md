# Banco: lema de verificacion global por super-solucion de Bellman

**Fecha:** 2026-11-08. **Rama:** `work/lean-ci-validation-otc-20261106`.
**Estado:** DEMOSTRACION MATEMATICA CONDICIONAL DOCUMENTADA; NO CERTIFICADO EN LEAN. No sustituye `BankOptimal` ni demuestra existencia de equilibrio S/B.

## 1. Problema y normalizacion

Sea `h_t` una historia soportada del modelo y `x_t=(e_t,h_t)` el estado individual del banco. Una politica admisible `q` selecciona dividendos `D_t(q)>=0`, cartera y sucesor `e_{t+1}(q)>=0` en cada historia, respetando *todas* las restricciones de balance, caps, solvencia y transicion de la fuente.

Definimos `lambda_t=Lambda_{t,t+1}>=0`, `s=1-eta_B` con `0<=eta_B<=1`, el flujo no negativo

`g_t(q)=D_t(q)+eta_B*lambda_t*e_{t+1}(q)`,

y el factor de supervivencia `A_{0,0}=1`, `A_{0,t+1}=A_{0,t}*s*lambda_t`.

La prima de salida se contabiliza una sola vez en `g_t`; no debe insertarse nuevamente en el termino de supervivencia. El objetivo de la politica individual es `J(q)=E_0[sum_{t>=0} A_{0,t}g_t(q)]`, entendido en `[0,+infty]` si los flujos son no negativos. Todas las desigualdades puntuales siguientes son bajo la medida y filtracion de las historias de la fuente. Las tasas `lambda_t` y el proceso de estados pueden ser aleatorios y adaptados.

## 2. Proposicion de cota universal (pendiente de traduccion Lean)

**Hipotesis.** Existe una funcion candidata `V_t(x)>=0`, finita y medible en cada historia, tal que para *cada* politica admisible `q`, en *cada* nodo alcanzable, se cumple

`V_t(x_t(q)) >= g_t(q) + E_t[s*lambda_t*V_{t+1}(x_{t+1}(q))]`.

Se asume integrabilidad suficiente para que la esperanza condicional y la multiplicacion por factores historicamente medibles sean validas. En particular, `A_{0,t}` debe ser `F_t`-medible y no negativo. Para aplicaciones donde `V` o los flujos no sean acotados, usar variables aleatorias no negativas y esperanzas extendidas, con las condiciones de finitud precisas en el paso algebraico.

**Afirmacion.** Para cada desviacion admisible `q` y cada entero `T>=1`,

`V_0(x_0) >= E_0[sum_{t=0}^{T-1} A_{0,t}g_t(q) + A_{0,T}V_T(x_T(q))]`.

Por `V_T>=0`, se sigue `V_0(x_0)>=E_0[sum_{t=0}^{T-1} A_{0,t}g_t(q)]`. La convergencia monotona permite concluir `J(q)<=V_0(x_0)` **sin imponer una condicion terminal sobre todas las desviaciones**.

**Demostracion.** La afirmacion para `T=1` es exactamente la desigualdad de super-solucion. Suponerla para `T`. En la ultima esperanza, aplicar la desigualdad en `t=T` y multiplicar por `A_{0,T}>=0`, que es `F_T`-medible. La propiedad de torre transforma el termino de continuacion en

`E_0[A_{0,T}*E_T(s*lambda_T*V_{T+1})] = E_0[A_{0,T+1}*V_{T+1}]`.

Reordenar da `T+1`. El resto sigue de la no negatividad y convergencia monotona. QED bajo las hipotesis declaradas.

## 3. Proposicion de alcanzabilidad por la candidata

Supongamos ademas que una politica admisible concreta `q*` realiza **igualdad** de Bellman en todos los nodos de su trayectoria, y satisface

`lim_{T->infinity} E_0[A_{0,T}V_T(x_T(q*))]=0`.

Las identidades de induccion pasan a ser igualdades para `q*`; el limite da `J(q*)=V_0(x_0)`. Junto a la cota universal, `J(q*)>=J(q)` para toda `q` admisible.

**Precaucion:** ni `V_T(x_T(q*))=O(e_T)` ni su limite terminal se deducen de KKT estatico. Un criterio suficiente adicional seria `0<=V_T(e,h)<=M_T(h)e` en las historias candidatas y `E_0[A_{0,T} M_T(h_T)e_T(q*)]->0`. Si `M_T<=M<infinity` uniformemente y `E_0[A_{0,T}e_T(q*)]->0`, basta. Estas cotas requieren prueba separada en el problema fuente.

## 4. Ruta concreta a Lean: compuertas no intercambiables

1. Definir el espacio de historias, politicas admisibles y objetivo `J` con los mismos campos que `Primitives`, `Allocation`, `BankContinuationPolicy` y la rentabilidad OTC del checkpoint; no construir un banco alternativo simplificado y llamarlo equivalente.
2. Formalizar por induccion la desigualdad de horizonte finito para `T` arbitrario, dejando visibles integrabilidad, positividad, medibilidad y propiedad de torre. Primero un lema de sumas finitas adaptadas; despues transporte a los tipos fuente.
3. Deduzca `J(q)<=V_0` para cada desviacion desde monotone convergence, **sin TVC universal**.
4. Establecer la identidad de Bellman de la politica candidata con su verdadero `V`, no postularla como premisa al certificar `BankOptimal`.
5. Probar limite terminal para `q*`, con cota de pendiente de valor o argumento alternativo.
6. Cotejar exhaustivamente dominio de politicas, renovacion `a_B`, ramas S/B, shocks, multiplicadores KKT y contratos bancarios; ejecutar CI focalizada, `#print axioms`, luego CI general.
7. Solo entonces conectar la verificacion bancaria con el cierre de las 33 filas del reducido y el equilibrio competitivo completo.

## 5. Auditoria de alcance

- **DEMOSTRADO EN CI ANTERIOR:** suficiencia estatica con cinco duales y construccion del entorno Bellman local, condicionada a la identidad puntual de valor.
- **DEMOSTRADO SOLO EN ESTE DOCUMENTO, MATEMATICAMENTE Y BAJO HIPOTESIS:** dos proposiciones abstractas de verificacion por induccion y convergencia monotona.
- **PENDIENTE:** implementacion Lean de los dos resultados abstractos; interpretacion literal en el objeto economico fuente; funcion de valor efectiva; terminalidad candidata; `BankOptimal`; equilibrio dinamico y consecuencias de crecimiento.
- **NO INFERIR:** ningun aumento transitorio de la inversion demuestra una tasa de crecimiento positiva en el largo plazo. No fusionar PR #2 a `main` mientras estas compuertas sigan abiertas.
