# Puente literal de cronologia para cuatro instrumentos — 10-XI-2026

## Pregunta formal

La intervencion inicial v=(v_R,v_M,v_rho,v_Delta) altera exclusivamente cuatro anuncios en fecha cero? Es una condicion necesaria para equiparar el operador economicamente generado en Lean y el evaluador IRF de Python. Debe probarse sin confundir la **dependencia directa del residual a coordenadas fijas** con la respuesta endogena del equilibrio completo.

El SOURCE define en initialIntervenedPrimitives:
- Innovaciones de remuneracion y cantidad de reservas solo cuando el estado Markov coincide con P.tree.initial.
- Trayectorias del coeficiente de encaje y amplitud del corredor solo cuando t=0.
- Fecha 1 usa un estado dateOne distinto del inicial y reservaRequirementPath 1 / corridorWidthPath 1; las primitivas restantes, el estado heredado y la regla terminal se conservan.

En Lean, los lemas source_initial_policy_innovation_pair, source_noninitial_policy_innovations_unchanged, source_initial_policy_path_pair, source_future_policy_paths_unchanged y source_dateone_prefix_data_fixed_coordinates_unaffected hacen explicitas esas condiciones. El ultimo requiere dateOne != P.tree.initial y compara la estructura LocalPrefixDateData de la fecha 1 en **coordenadas fijas**. Los lemas son candidatos hasta que la corrida Lean del SHA exacto muestre su compilacion y #print axioms sin sorryAx.

## Correspondencia condicional con Python

En prefix_residual(base,p0,branch,(v_R,v_M,v_rho,v_Delta),z), a coordenadas z fijas, se cumple:

- E0(v)=(e0_R+v_R,e0_M+v_M), rho0=rho+v_rho, Delta0=Delta+v_Delta.
- E1=e1, rho1=rho y Delta1=Delta, independientemente del shock inicial.
- Los indices 17..32 (t=1) y 0..11 (ecuaciones sin anuncios directos en t=0) no dependen explicitamente de v.
- El residual 12 cambia por -v_R y el residual 13 por -v_M. Los anuncios reales rho y Delta modifican filas de precios OTC y balance de fecha cero, no las reglas de innovacion.

El auditor code/irf/audit_source_four_tool_direct_support.py verifica anclas literales SOURCE, seis vectores de perturbacion (incluido shock conjunto), tres puntos en la carta positiva, ambas ramas, el soporte no nulo y los multiplicadores exponenciales de los dos anuncios logaritmicos. Es un test NUMERICO/CONDICIONAL; no ejecuta por si mismo la fuente Lean.

**No inferir respuesta dinamica nula**: si z=z(v) es la solucion del sistema, entonces por regla de la cadena dG_1(z(v))/dv = D_z G_1 dz/dv, que en general no es cero aunque la derivada parcial (a z fijas) respecto del shock sea exactamente cero. La equivalencia de ambos operadores, su Jacobiano fuente, las 34 condiciones KKT y el horizonte infinito siguen como obligaciones separadas. Mantener PR #2 en borrador y main sin modificar.
