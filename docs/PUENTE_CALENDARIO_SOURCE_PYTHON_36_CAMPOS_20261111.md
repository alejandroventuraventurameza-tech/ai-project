# IE Project 18 — puente de calendario SOURCE–Python y datos heredados (11-XI-2026)

## Pregunta de correspondencia

El ejecutor numérico `finite_irf.prefix_residual` recibe una carta positiva de 33 coordenadas y un vector de cuatro instrumentos `(v_R,v_M,v_rho,v_Delta)`. SOURCE, en cambio, construye `LocalPrefixDateData` mediante `localPrefixDateZeroData` y `localPrefixDateOneData` a partir de una instancia de `Primitives`, el estado heredado `InheritedState`, las coordenadas `LocalPrefixCoordinates`, un calendario `0→1→2→2` y la regla de continuación `tail`.

Esta discrepancia de *representación* es una de las brechas que impide todavía afirmar que los 33 residuos son el mismo operador económico.

## Inventario literal verificado

Se inspeccionaron en el SOURCE los **18 campos** de cada constructor `LocalPrefixDateData`. Entre los campos relevantes están el capital y las caras nominales heredadas, `bankFace`, las reservas anteriores, controles actuales y próximos, productividad, innovaciones y dos herramientas en niveles. En fecha cero, los datos heredados proceden de `InheritedState`; en fecha uno proceden de `Z.stateOne`. Para las caras nominales de fecha dos se usa `localPrefixStateSixFace P Z.stateTwo`, que debe identificarse cuidadosamente con la convención de la implementación Python.

La intervención SOURCE `initialIntervenedPrimitives` suma `v_R` y `v_M` solo en el estado inicial, y suma `v_rho` y `v_Delta` solo cuando `t=0`. Python introduce estos cuatro términos en `e0`, `aux0` y los parámetros `rho` y `corridor` de `aux0`, mientras que las fechas posteriores usan `base.e1` y luego innovaciones cero. La ausencia de innovación directa en fecha uno NO significa ausencia de efecto endógeno en esa fecha.

## Nueva auditoría automatizada

`code/irf/audit_source_python_calendar_contract.py` realiza las comprobaciones siguientes:

1. Analiza de forma literal los dos constructores fuente, incluidas las asignaciones divididas en más de una línea; exige exactamente los 18 nombres de campo y sus expresiones.
2. Detecta cambios en las cuatro reglas de intervención de `initialIntervenedPrimitives`.
3. Detecta cambios en las reglas correspondientes de Python `prefix_residual`: lectura y orden de instrumentos, localización en fecha cero, `aux1`, `aux2`, rama slack de la firma L y número de ecuaciones.
4. Registra los SHA256 de los archivos SOURCE y Python y genera `code/irf/output/source_python_calendar_contract.json`.
5. Declara explícitamente `False` para equivalencia numérica de estado heredado, igualdad de 33 funciones económicas y certificado de Jacobiano.

El auditor se incorporó a `code/verify.py` y el workflow `build.yml` debe archivar su resultado como `source-python-calendar-contract`. **Estado: código incorporado; validar CI del SHA nuevo antes de promover su ejecución a comprobada.**

## Brechas específicas identificadas

- Construir formalmente un mismo estado heredado `I` y `base.X0` con caras nominales y reservas concordantes.
- Probar que la productividad, la ley de pagos y las funciones de demanda/OTC de `Primitives` corresponden a los parámetros y auxiliares de Python en ambas fechas.
- Cotejar `tail Z.stateTwo` contra el `u2` construido por el grafo `P0`; una coincidencia de nombres no prueba equivalencia del operador recurrente ni condiciones terminales.
- Transportar las filas Euler y la cara nominal común preservando las restricciones KKT de ambas ramas.
- Establecer la igualdad de las 33 funciones sobre una carta abierta o, en su defecto, una cota certificada de discrepancias de derivadas.

El inventario literal de 36 asignaciones **es una compuerta de procedencia**, no una demostración en Lean ni un certificado causal. Mantener PR #2 como borrador y no fusionar `main`.
