# Diagnóstico acotado de la caída inicial de producción

Se revisan condiciones laborales, tecnología corriente y curva de Phillips frente al artículo.
El capital instalado es fijo al impacto. Con beta=0.5, phi=1 y sigma_W=1:
`Delta log Y_0 = (Delta log m_0 - Delta log Cw_0) / 3`.

Las contribuciones siguientes son identidades de equilibrio evaluadas en la solución; no identifican efectos causales independientes.

## Rama slack
Producción al impacto (log %): -3.579757199e-05
Contribución precio del insumo: -0.0002042346145
Contribución consumo del hogar: 0.0001684370426
Error máximo de las identidades: 2.887e-13

## Rama binding
Producción al impacto (log %): -0.004142551019
Contribución precio del insumo: -0.004303723648
Contribución consumo del hogar: 0.0001611726291
Error máximo de las identidades: 1.951e-13

## Curva de Phillips: descomposición exacta evaluada

m_0 = (epsilon-1)/epsilon + (phi_p/epsilon) Pi_0(Pi_0-1)
      - (phi_p/epsilon) Lambda_01 (Y_1/Y_0) Pi_1(Pi_1-1).
El término contemporáneo y el término futuro se calculan en cada trayectoria y se restan sus referencias.
La conversión a contribuciones logarítmicas usa el factor exacto Delta log(m)/Delta m; no sustituye un contrafactual.

- slack: {'current_inflation_component_output_log_pct': 0.005051306292467185, 'future_pricing_component_output_log_pct': -0.005255540906716581, 'worker_consumption_component_output_log_pct': 0.00016843704255224237}
- binding: {'current_inflation_component_output_log_pct': 0.004830103679809929, 'future_pricing_component_output_log_pct': -0.00913382732812557, 'worker_consumption_component_output_log_pct': 0.00016117262905506217}

El componente futuro negativo supera al contemporáneo positivo en ambas ramas. Esto localiza la importancia del bloque de expectativas y continuación, pero no identifica una causa exógena independiente.

## Sensibilidad

- half_shock: {'slack': -1.7788482481544893e-05, 'binding': -0.00207115288241248}
- tenth_shock: {'slack': -3.540051614557787e-06, 'binding': -0.0004142109617797015}
- smaller_jacobian_step: {'slack': -3.5797572019113753e-05, 'binding': -0.004142551018776802}
- larger_jacobian_step: {'slack': -3.5797572052420465e-05, 'binding': -0.004142551019065471}

## Conclusión provisional
La caída persiste con los choques menores y los pasos de Jacobiano comprobados si `negative_in_all_tested_cases` es verdadero en diagnosis.json.
No se observa contradicción en las identidades acotadas revisadas. Esto no descarta errores en otros bloques ni acredita optimalidad.
Falta contrastar con una continuación no lineal independiente y completar la correspondencia económica.
El horizonte 160/320 del reproductor anterior no constituye una prueba independiente del cierre lineal.

Reproducción: `python code/irf/diagnose_impact.py`. No cambia ecuaciones, parámetros ni las IRF principales.
