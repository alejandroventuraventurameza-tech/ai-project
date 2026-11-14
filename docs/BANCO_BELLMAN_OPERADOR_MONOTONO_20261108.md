# IE project — puente de Bellman con operador monótono

**Fecha:** 2026-11-08.
**Rama:** `work/lean-ci-validation-otc-20261106`.
**Estatus:** nuevos candidatos Lean; sin run focalizado de kernel confirmado para los commits `6c9e05bf` ni `ea835729`.

## Objeto matemático incorporado

`lean/candidates/Ventura26LiquidityAllocation/PaperBankMonotoneBellmanEnvelopeCandidate.lean` define un operador temporal `continuation t` sobre funciones de estados a números reales; su monotonicidad es una hipótesis y no una conclusión sobre el banco fuente.

Los objetivos `recurse_le_value` y `recurse_eq_value` enuncian, respectivamente, la cota de horizonte finito y la identidad de una candidata bajo Bellman. Se importan indirectamente desde `PaperBankBellmanEnvironmentFromStaticCandidate.lean` por `PaperBankFiniteHorizonEnvelopeCandidate.lean`.

## Qué significa para la economía

Un operador del tipo

`T_t f(x) = E_t[ (1-eta_B) * Lambda_(t,t+1) * f(x_(t+1)) ]`

es monótono si los pesos correspondientes son no negativos y las esperanzas están bien definidas. **Esto es una interpretación matemática, no una instancia Lean construida para `EconomicModel.lean`**. El valor del dividendo y la prima de salida deben permanecer en la recompensa corriente, sin duplicarlos.

## Contrato de auditoría

1. Ejecutar un workflow Lean focalizado sobre ambos módulos nuevos y revisar `#print axioms`. Las ejecuciones de Python/LaTeX no sustituyen esto.
2. Construir una instancia del operador a partir de la distribución de transición, descuentos estocásticos y espacios de historias literales del proyecto.
3. Probar medibilidad, integrabilidad/no negatividad y preservación del orden para esa instancia.
4. Elevar la inducción punto a punto a las expectativas condicionales, con propiedad de torre en todas las historias.
5. Demostrar que `V` es supersolución para cada desviación; demostrar la igualdad para una política efectivamente admisible y el límite terminal de **esa** política.
6. Solo entonces reclamar `BankOptimal`; suponer el valor candidato o su TVC como premisa no descarga las obligaciones de existencia ni optimalidad fuente.

## Semáforo científico

- **Lean verificado antes:** KKT estático con cinco duales; ambiente Bellman local condicional (CI #42515897038).
- **Nuevo código pendiente de verificación:** inducción determinista finita y generalización por operador monótono.
- **No demostrado:** óptimo bancario infinito, 33 ecuaciones reducidas como equilibrio pleno, políticas S/B, causalidad de IRF, crecimiento sostenido.
- **Entrega:** PR #2 en borrador, no fusionar a `main`.
