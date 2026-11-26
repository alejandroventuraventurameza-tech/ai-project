# Puente bancario: operador conjunto pagos-estados y límites de certificación

**Fecha:** 2026-11-08. **Rama:** `work/lean-ci-validation-otc-20261106`.
**Candidato:** `PaperBankJointContinuationMonotonicityCandidate.lean`.

## Resultado construido (todavía no verificado por kernel)

El nuevo operador

`jointSurvivalContinuation P X t h f`

suma sobre `P.paymentSupport` y los estados agregados `S` usando literalmente `P.paymentProbability`, `P.tree.transition`, `bankStochasticDiscountAt` y `1-P.bankExit`. La declaración `jointSurvivalContinuation_monotone_of_consumption` demuestra, si supera el kernel, que `f<=g` en los pares soportados implica orden de las continuaciones. Usa el teorema fuente `bankStochasticDiscountAt_pos_of_consumption` y trata separadamente transiciones con peso cero.

**Distinción económica:** para una cartera fija la parte de valor futuro bajo supervivencia es monótona. El término de patrimonio de salida no depende de la función de valor comparada y por ello se cancela al comparar dos continuaciones en la misma cartera. La prueba NO muestra que la cartera fija sea óptima, ni que la política óptima tenga una representación suficiente por `f : BankPayment -> S -> Real`.

## Obligaciones restantes

1. Confirmar la compilación real con `lean-focused-paper-claims.yml` en el SHA que incluye este módulo; revisar `#print axioms` y ausencia de `sorryAx`.
2. Demostrar una identidad del operador conjunto con la parte dependiente de `bankValueNext` de `bankBellmanContinuationAt`, haciendo explícitos los sucesores de patrimonio `bankRealPortfolioReturnAt` y la coincidencia del término de salida.
3. Elevar el orden a continuaciones de políticas factibles con historias `History` y pagos `BankPayment` y estados adecuados; aplicar la inducción `recurse_le_value`.
4. Conectar la desigualdad local para toda desviación con el objetivo infinito `bankContinuationPayoffAt`, usando `bankContinuationPayoffAt_first_step`, sumabilidad y terminalidad sin imponer TVC a toda desviación.
5. Probar igualdad y un límite terminal únicamente para la candidata; posteriormente auditar `BankOptimal`, las ramas S/B, el sistema económico completo y los efectos de crecimiento.

**Semáforo:** KKT global estático, con hipótesis, ya verificado en runs anteriores. Esta monotonía conjunta permanece **CANDIDATO LEAN** hasta CI inequívoca. El PR #2 debe mantenerse draft; no fusionar `main`.
