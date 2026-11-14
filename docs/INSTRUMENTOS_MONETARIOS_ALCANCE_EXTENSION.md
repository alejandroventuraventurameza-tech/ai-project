# Pool de instrumentos monetarios: alcance verificado y extension propuesta

**Estatus:** diseno tecnico de investigacion, no extension ya implementada,
ni estimacion causal, ni teorema de equilibrio. Fuente primaria:
`lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`;
evaluador ilustrativo:
`code/v0m/cierre_interno_2026_10_17/finite_bridge.py`.

## 1. Instrumentos disponibles en la fuente actual

`Primitives` define:
- `reserveRateInnovation : S -> Real`: innovacion de la remuneracion de reservas;
- `reserveQuantityInnovation : S -> Real`: innovacion de reservas prepagos;
- `reserveRequirementPath : AdaptedProcess S`: coeficiente de encaje;
- `corridorWidthPath : AdaptedProcess S`: amplitud del corredor.

`initialIntervenedPrimitives` altera estos cuatro objetos en el
periodo inicial, conservando las primitivas reales y los anuncios
posteriores. La logica de `LocalScalarAugmented34SourceCandidate`
y los certificados recientes toman `v_R` (remuneracion de
reservas) como el segundo componente del vector de cinco entradas,
siendo la primera la holgura de colateral prescrita; los otros
tres instrumentos se mantienen en cero durante esa prueba.
El certificado de 34 ecuaciones NO constituye una comparacion
simultanea de todos los instrumentos.

El modelo fuente no contiene todavia una decision separada de
compras de activos o cartera de titulos del banco central que
pueda confundirse con el stock `reserveQuantitySteady`.
La variable `governmentBondSupply` no demuestra por si sola
un balance de compras de activos de la autoridad monetaria.

Tampoco se ha demostrado una correspondencia uno-a-uno entre
`reserveRateInnovation` y una tasa de politica *headline*
separada. La remuneracion de reservas puede actuar como una tasa
administrada, pero no es por definicion un instrumento de tasa
de referencia adicional.

## 2. Pool a formalizar, sin duplicar controles

Una extension candidata considera

```text
u_t = (i_policy, i_reserves, corridor_spreads,
       reserve_requirement, reserves_supply,
       CB_asset_purchases).
```

La remuneracion `i_reserves` y la tasa guia `i_policy`
pueden estar vinculadas por una regla; si se quieren shocks
independientes, debe explicarse por que ambos son controles
y comprobar rango de identificacion. El corredor debe fijar
facilidades de deposito y credito `i_DF` e `i_LF`
alrededor de un centro especificado (no inferir que la amplitud
es la tasa). El encaje `rho` modifica las restricciones
bancarias, no la regla de remuneracion por identidad.
`reserves_supply` es una cantidad nominal; debe indicarse si
es prepagos, cierre del periodo o saldos requeridos.

## 3. Contabilidad requerida para balance del banco central

Antes de incorporar compras de activos `Q_t^{CB}` se debe
anotar al menos una identidad de stocks nominales, por ejemplo

```text
Q_t^{CB} + L_t^{CB} = M_t + N_t^{CB},
```

donde `L^{CB}` son prestamos de la facilidad,
`M` son pasivos monetarios elegibles, y `N^{CB}`
patrimonio de la autoridad. La identidad de flujos
requiere tratar valoraciones, intereses pagados por reservas,
cupones, beneficios y remesas, segun los contratos elegidos.
No es correcto afirmar `Delta Q = Delta M` sin
especificar los otros cambios de activos, pasivos y patrimonio.
Las operaciones de cartera deben aparecer con signo contrario
en balances privados y clearing de bonos.

La estructura OTC y las restricciones de liquidez bancaria
deben mantenerse consistentes con la nueva cantidad de
reservas y facilidades. El bloque de politica mas amplio
requiere rederivar KKT, recursos y presupuesto del sector
publico, no solo sumar un shock al vector numerico.

## 4. Orden eficiente de implementacion

1. **Cerrar equivalencia semantica 34x34** en la
   perturbacion de remuneracion actual: cotejo literal
   de datos, parametros, calendarios y 34 filas; certificado
   condicional Banach y testigo Lean.
2. **Identificar instrumentos monetarios actuales** de
   manera independiente: remuneracion, cantidad,
   encaje y amplitud del corredor. Obtener IRF con
   signos y unidades desde CSV auditado para cada uno;
   certificar la solucion reducida antes de llamarla
   equilibrio competitivo.
3. **Agregar tasa de politica referencia separada solo
   si es economicamente necesaria**, con reglas
   transparentes de relacion con la remuneracion y las
   facilidades.
4. **Agregar compras de activos con contrapartidas de
   balance**, y rehacer el sector bancario para
   incorporar stocks y flujos de la autoridad.
5. **Comparar el canal de H productiva y poco
   pignorable** mediante dos asignaciones KKT completas
   y la misma perturbacion, antes de cualquier
   inferencia de crecimiento permanente.
6. **Crecimiento tendencial** es una extension distinta:
   ver `docs/CRECIMIENTO_VERSUS_NIVEL_CONDICIONAL.md`.

## 5. Compuertas de afirmacion economica

- Demostrar `F_r=0` (33 filas) no equivale a
  optimalidad del banco ni factibilidad intertemporal.
- Una respuesta del precio de prestamo no demuestra
  por si sola un alivio de la KKT de colateral de H.
- Un cambio en reservas no es una compra de activos
  del banco central a menos que la contabilidad lo imponga.
- Una mejor asignacion y un mayor producto estacionario
  NO prueban una tasa de crecimiento tendencial mayor.
- Las pruebas Lean que identifican reglas de politica
  son condicionales a datos/calibracion; el certificado
  de 34 dimensiones sigue siendo numerico condicional
  hasta cerrar el puente semantico.
