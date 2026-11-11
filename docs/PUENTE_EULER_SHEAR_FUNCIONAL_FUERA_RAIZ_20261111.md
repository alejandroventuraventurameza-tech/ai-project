# IE Project 18 — auditoría funcional de shear Euler fuera de raíz (11-XI-2026)

## Pregunta

¿La diferencia entre la Euler SOURCE y la Euler Python en fecha uno representa un error económico o una operación reversible de filas que depende del estado? Para tipos `i∈{H,L}`, el auditor `code/irf/audit_source_firm_budget_euler_shear.py` transcribe, bajo los parámetros del experimento Python, la relación ya reconstruida:

`F_i(z)-G_i(z)=theta_i (J_2(z)-A_2(z)) (1/R^L_1(z)-m_i(z)/Pi_2(z))`,

donde `A_2=(1-delta)Pi_2 q_2`, `m_i=beta_E(c_i1/c_i2)^sigma_E` y `g(z)=log(J_2/A_2)`. En la carta positiva `A_2>0, J_2>0, R^L_1>0, Pi_2>0`, la forma funcional **exacta, incluso fuera de raíz**, es

`F_i(z)=G_i(z)+a_i(z)g(z)`,

`a_i(z)=theta_i A_2(z) (1/R^L_1(z)-m_i(z)/Pi_2(z)) h(g(z))`,

`h(x)=expm1(x)/x` para `x != 0` y `h(0)=1`.

El cociente tiene extensión analítica en cero, `h(x)=1+x/2+x²/6+x³/24+...`.

## Regla del producto

Para una perturbación `v` en la carta,

`DF_i(z)[v]=DG_i(z)[v] + a_i(z)Dg(z)[v]+g(z)Da_i(z)[v]`.

En `g(z*)=0`, se elimina el último término; fuera de raíz es generalmente distinto de cero. La transformación triangular de filas es `T(z)=I+K(z)` con entradas `K_{Euler_i,pledge}=a_i(z)`. Dado que la matriz tiene únicamente esas dos entradas fuera de diagonal y `K(z)^2=0`, se obtiene `T(z)^{-1}=I-K(z)` **punto a punto**, siempre que estas filas y la fila de garantía estén correctamente identificadas. Esta invertibilidad algebraica no prueba la igualdad de los demás residuos económicos.

La fórmula anterior por sí sola NO autoriza escribir `DF=T DG` fuera de raíz: aparece `DT(z)[v]G(z)`. En una raíz común del vector completo `G(z*)=0`, ese término desaparece.

## Nuevo control

La auditoría empresarial existente ahora contrasta `F_i-G_i-a_i(z)g(z)` en ambas ramas, cinco intervenciones y tres puntos de la carta, incluidos estados fuera de raíz. Asimismo, en cada rama toma 33 perturbaciones de coordenadas para cada una de las dos Euler y verifica que la derivada numérica de `F_i-G_i` coincide con la derivada de la transformación **completa con coeficiente variable**. Son 132 verificaciones de esa regla de producto, además de los controles previos de las otras seis filas y de las condiciones de raíz.

En la evaluación del cociente `h(g)` se emplea una expansión de Taylor cerca de cero para evitar cancelación numérica, sin confundir esta aproximación computacional con un teorema de equivalencia SOURCE/Python.

## Veredicto y límites

**Algebraicamente:** bajo el dominio positivo y la identificación funcional de `J_2,A_2,R^L_1,m_i`, hay un shear exacto y reversible.

**CI:** el nuevo código fue incorporado a la rama de desarrollo; sus resultados aún requieren una corrida exitosa en el SHA correspondiente.

**Pendiente de prueba SOURCE completa:** identificar el mismo `LocalPrefixDateData` y los datos intertemporales en Lean y Python, construir las 33 filas bajo la misma carta `psi`, comprobar `DF` y `DG`, las 34 condiciones KKT y la optimalidad. Las ramas S/B de este test se evalúan sobre el experimento de frontera común, no sobre dos equilibrios distintos probados.

No fusionar PR #2 a `main` con estas obligaciones pendientes.
