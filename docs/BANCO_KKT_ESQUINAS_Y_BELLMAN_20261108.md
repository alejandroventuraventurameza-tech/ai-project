# IE project — Certificado KKT global del banco y compuerta Bellman

**Rama de trabajo:** `work/lean-ci-validation-otc-20261106`.  
**Estado al crear esta nota:** demostraciones candidatas enviadas a GitHub Actions; ninguna promoción de evidencia antes de CI focalizada y auditoría `#print axioms`.  
**Objeto:** economía fuente `EconomicModel.lean`, no una función objetivo alternativa.

## I. Fuente y distinción institucional

Para el banco individual con patrimonio retenido fijo `e`, elegir préstamos `b`, reservas iniciales `m` y depósitos `d`, sujeto a

```
b + m = d + e
0 <= b <= kappa_L * e
0 <= d <= kappa_D * e
0 <= m
```

y solvencia robusta para todos los pagos y estados de transición soportados. La función de liquidación reducida coincide con los flujos OTC/facilidad de la fuente cuando `R^R != 0`; no hay un segundo mercado inventado.

```
s(m,d,omega) = m - rho*d + (xi-rho)*omega*d,
xi = R^D/R^R,
Pi(b,m,d) = R^L*b + R^R*m - R^D*d + E[chi(s(m,d,omega))].
```

El coeficiente de encaje `rho` NO es la remuneración de reservas `R^R`. Los límites `kappa_L,kappa_D` son restricciones de apalancamiento de los bancos; no deben confundirse con el colateral empresarial.

## II. Condiciones KKT suficientes, con esquinas

Sea `mu(omega)` un supergradiente de la función cóncava de liquidación `chi` en la cartera candidata para todo `omega` soportado, con `muBar=E[mu]` y `muShock=E[mu*omega]`.

Los multiplicadores **no negativos** `lambda_L^cap,lambda_L^0,lambda_D^cap,lambda_D^0` satisfacen la complementariedad:

```
lambda_L^cap*(kappa_L*e-b*)=0,  lambda_L^0*b*=0,
lambda_D^cap*(kappa_D*e-d*)=0,  lambda_D^0*d*=0.
```

Las condiciones de precios, incluidas las cuñas por restricciones de préstamos y depósitos, son

```
R^L = R^R + muBar + lambda_L^cap - lambda_L^0,
R^D = R^R + (1-rho)*muBar + (xi-rho)*muShock
                 - lambda_D^cap + lambda_D^0.
```

Estas condiciones reflejan el **problema con el balance individual ya sustituido**. En particular el depósito adicional financia reservas; por eso aparece `1-rho`. Las cuñas normalizadas son nulas cuando ambas restricciones correspondientes están holgadas. Las hipótesis de precio no se deducen automáticamente de un solver numérico.

Para una alternativa factible, denotar `delta b=b-b*`, `delta m=m-m*`, `delta d=d-d*`. La concavidad de `chi` y los precios anteriores dan

```
Pi(b,m,d)-Pi(b*,m*,d*) <=
  (lambda_L^cap-lambda_L^0)*delta b +
  (lambda_D^cap-lambda_D^0)*delta d
 + (R^R+muBar)*(delta b+delta m-delta d).
```

El balance impone `delta b+delta m-delta d=0`. Por factibilidad de la desviación, complementariedad de la candidata y no negatividad de los multiplicadores,

```
(lambda_L^cap-lambda_L^0)*delta b <= 0,
(lambda_D^cap-lambda_D^0)*delta d <= 0.
```

De ello sigue **suficiencia global de cartera en una fecha** para toda cartera literalmente factible, con independencia del signo del saldo de liquidación de la alternativa. Los `sorry` o postulados de optimalidad final están prohibidos.

**Alcance importante:** el certificado cubre ceros de préstamos/depósitos y sus caps, pero **no** incluye un multiplicador no nulo para el límite inferior de reservas. Si la candidata tiene `m*=0`, las condiciones de precios escritas son suficientes pero pueden no ser necesarias; no declararlas como KKT exhaustivo de toda esquina posible. Tampoco se han eliminado restricciones de solvencia, cuyo papel es restringir el conjunto factible y no reemplazar la cota de concavidad.

El objetivo de Lean está en `PaperBankKKTGlobalSufficiencyCandidate.lean`.

## III. Enlace correcto con Bellman

La biblioteca fuente ya prueba, para una cartera admisible, que si el valor futuro es homogéneo en patrimonio, el retorno real no negativo puede factorizarse:

```
BellmanContinuation_t(b,m,d;V_{t+1})
  = W_t(V_{t+1}) * Pi_t(b,m,d).
```

Si `W_t>0` y se ha demostrado el certificado estático global, toda cartera alternativa factible presenta valor de continuación menor o igual. La positividad de `W_t` puede derivarse del teorema fuente bajo consumo/inflación positivos en los sucesores posibles, salida bancaria positiva y valores unitarios futuros no negativos.

`PaperBankBellmanEnvironmentFromStaticCandidate.lean` busca además reunir las nueve condiciones del predicado **literal** `BankBellmanLocalEnvironmentAt`. Todavía debe exigir la **identidad puntual de valor de la cartera candidata**:

```
V_t(e) = dividend_t + BellmanContinuation_t(b*,m*,d*;V_{t+1}).
```

Esa igualdad NO queda demostrada simplemente por la cota estática: exige definir y validar la función `V` y la continuación de la candidata. El nuevo teorema no presupone `BankBellmanLocalEnvironmentAt`; sí mantiene la identidad puntual como premisa explícita.

## IV. Resultados numéricos existentes y pendientes formales

`code/irf/output/financial_blocks_audit/REPORT.json` informa, a lo largo de las dos trayectorias T=640, márgenes bancarios mínimos positivos:

| Banco | S (slack) | B (binding) |
|---|---:|---:|
| Deposits cap slack | 3.4045206 | 3.4044483 |
| Loans cap slack | 5.6529231 | 5.6528512 |

La esquina de depósitos empresariales, la restricción de colateral de firmas y los duales de esa restricción son **objetos diferentes**. Los errores de precios bancarios y soporte numéricos son pequeños, pero no sustituyen una realización formal de `Primitives`, `Allocation` y `BankContinuationPolicy`.

**Próximas obligaciones no resueltas:** control `m*=0` con multiplicador propio si corresponde; probar la identidad puntual Bellman para la continuación efectiva; demostrar cota de valor para TODAS las políticas alternativas factibles sin imponerles TVC por decreto; obtener sumabilidad y terminalidad de la candidata; demostrar que los estados numéricos S/B inducen una asignación y un equilibrio completo. La calibración de renovación bancaria `a_B` sigue siendo una restricción adicional.
