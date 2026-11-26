# IE Project 18 — Dependencia heredada del sistema reducido de 33 residuos (11-XI-2026)

## Hallazgo preciso en el código SOURCE

En `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`, la función `localReducedPrefixResidual` recibe el registro `InheritedState`, pero primero construye `d0 := localPrefixDateZeroData P I Z dateOne` y `d1 := localPrefixDateOneData P Z dateOne recurrent tail`. En el cuerpo del despachador de las 33 filas, las ecuaciones dependen de `d0`, `d1` y, en una fila, de `Z.stateTwo`; no leen otros campos de `I` directamente.

A su vez, el constructor `localPrefixDateZeroData` solo extrae cinco **campos estructurales** del registro heredado:

- `I.capital`, vector de dos tipos de empresa H/L;
- `I.firmFace`, dos caras nominales H/L;
- `I.bankFace`;
- `I.reserveRateLag`;
- `I.reservesPreLag`.

Estas cinco entradas estructurales se expanden en **siete coordenadas escalares**. Por sustitución funcional, y manteniendo fijos `P,Z,dateOne,recurrent,tail` y la rama S/B, el sistema **reducido** de 33 residuos debe ser insensible a los siete campos heredados restantes: depósitos, bonos, tasa de depósitos rezagada, tasa de bonos públicos rezagada, reservas posteriores a pagos, tasa de facilidad y crédito de facilidad heredado.

Se trata de una **proposición de dependencia del operador reducido**, no de irrelevancia de esos campos en la economía completa. Los campos adicionales reaparecen en presupuesto público, liquidación, restricciones y optimalidad de bancos y hogares; por eso no pueden borrarse del problema de equilibrio general sin una demostración adicional.

## Auditoría ejecutable

El nuevo `code/irf/audit_reduced_prefix_inherited_support.py`:

1. lee el SOURCE literal y comprueba los doce nombres del registro, los cinco accesos heredados del constructor de fecha cero y que el despachador de las 33 filas no lea directamente otros campos de `I`;
2. comprueba que la fecha uno no incorpora directamente datos del registro `I`, y que ambos constructores siguen teniendo dieciocho campos;
3. evalúa el residuo Python en el estado heredado estacionario fijo `frozen_stationary_seed`, antes y después de adjuntar metadatos financieros que la API reducida no recibe, y exige igualdad exacta de las dos listas;
4. genera un informe JSON con hashes y banderas explícitas de evidencia que **no** se ha demostrado (`source_lean_semantic_extensionality_proved_in_kernel=False`, `fiscal_closure_unchanged_proved=False`, `full_33_operator_transport_proved=False`).

El auditor se ejecuta desde `code/verify.py` y `build.yml` conserva el artefacto `source-reduced-inherited-support`. La comprobación queda pendiente de resultado del workflow del SHA más reciente.

## Próximo teorema SOURCE propuesto

Para dos estados heredados `I,J` tales que, para todo tipo `i`, coinciden `I.capital i=J.capital i`, `I.firmFace i=J.firmFace i`, y también `I.bankFace=J.bankFace`, `I.reserveRateLag=J.reserveRateLag`, `I.reservesPreLag=J.reservesPreLag`, el teorema debe afirmar:

`localReducedPrefixResidual branch P I Z dateOne recurrent tail eq = localReducedPrefixResidual branch P J Z dateOne recurrent tail eq`.

Esta igualdad es plausible por reducción definicional del constructor `d0`; requiere formalización y comprobación por el kernel Lean para adquirir el estatus de **DEMOSTRADO**.

El teorema no implica que los dos estados heredados constituyan equilibrios completos iguales, ni que el cierre fiscal, la restricción de bonos o el problema bancario sean invariantes. El siguiente trabajo debe demostrar el teorema en Lean, inspeccionar axiomas y verificarlo en GitHub Actions antes de utilizarlo para transportar Jacobianos.

**Estado:** código de auditoría y documentación incorporados. PR #2 sigue en borrador, `main` no se fusiona.
