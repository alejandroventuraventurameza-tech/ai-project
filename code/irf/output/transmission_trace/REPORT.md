# Transmisión: regla monetaria, Euler y precios

Este diagnóstico usa la solución reducida no lineal con T=640 y cierre de gráfica estable en T. No cambia parámetros, estados heredados ni anuncios.

## Ecuaciones enlazadas
0. Banco en el régimen interior utilizado: RL_t = RR_t + chi_bar_t; RD_t = RR_t + (1-rho)chi_bar_t - (RD_t/RR_t-rho)*zeta*chi_diff_t/2. Las pendientes provienen del matching y corredor, no se estiman como residuo.
1. Regla: Delta log RR_t = 0.5 Delta log RR_(t-1) + 0.75 Delta log Pi_t + 0.0625 Delta log Y_t + v_t.
   Los anuncios de referencia se mantienen: v_0=-1e-5 y v_t=0 después. Las contribuciones son logaritmos, no diferencias de tasas brutas.
2. Euler del hogar: Delta log Cw_(t+1) - Delta log Cw_t = Delta log RD_t - Delta log Pi_(t+1).
3. En este experimento determinista, Lambda_(t,t+1)=Pi_(t+1)/RD_t. Entonces la curva de Phillips puede escribirse:
   m_t = 5/6 + 25 Pi_t(Pi_t-1) - 25 (Y_(t+1)/Y_t) Pi_(t+1)^2(Pi_(t+1)-1)/RD_t.
4. Con capital y tecnología fijos al impacto: Delta log Y_0 = (Delta log m_0 - Delta log Cw_0)/3.

## Qué permite concluir esta cadena
La regla baja inicialmente la remuneración por la innovación, pero la retroalimentación de inflación y producto y la persistencia afectan toda su trayectoria. La reversión posterior de la tasa es endógena a las reglas y a la solución; no es una segunda sorpresa monetaria añadida.
Euler describe crecimiento de consumo entre fechas, no determina su nivel inicial a partir de la tasa real inicial. El nivel también depende del resto de la trayectoria y del anclaje terminal, que aquí se deja explícito.
El término futuro de la curva de Phillips incluye simultáneamente inflación futura, producción relativa y la tasa de depósito. Su contribución negativa puede superar la contemporánea positiva y reducir el precio del insumo m_t.
Con capital instalado fijo, el menor precio recibido por las empresas en relación con el salario reduce su demanda de trabajo y su producción. La caída del consumo del hogar, a m fijo, operaría en sentido compensador mediante la oferta laboral.

## Resultados cuantitativos

### Rama slack
Output inicial, log %: -3.559159239e-05.
Contribuciones de las ecuaciones bancarias, diferencias de tasas en pb: {'reserve_rate_difference_bp': -0.0636435332279639, 'mean_liquidity_slope_difference_bp': 1.8114909398903034e-06, 'deposit_liquidity_component_bp': 1.630341845901273e-06, 'deposit_payment_risk_component_bp': -2.483814673034934e-07, 'loan_rate_difference_bp': -0.06364172173700666, 'deposit_rate_difference_bp': -0.06364215126897221}.
Consumo inicial del hogar, log %: -0.0005051665463.
Descomposición Euler del consumo inicial: {'terminal': -8.437694987151226e-13, 'real_returns_dates_0_to_2': 0.002448902548690428, 'real_returns_dates_3_to_639': -0.002954069088545569, 'identity_error': 5.613190034309268e-12}.
Contribuciones contables al output inicial: {'current_inflation_term': 0.005049836514701366, 'future_pricing_term': -0.005253816955849814, 'worker_consumption_term': 0.00016838884877070013}.
Primera fecha con remuneración de reservas no inferior a su referencia: 2.
Errores máximos de identidades: {'Euler': 6.309566307742127e-16, 'policy_rule': 3.7469108621105885e-16, 'Phillips_Euler_reduction': 7.699454951642232e-15, 'loan_pricing': 6.83481049534862e-16, 'deposit_pricing': 6.880346986593011e-16}.

### Rama binding
Output inicial, log %: -0.004142220876.
Contribuciones de las ecuaciones bancarias, diferencias de tasas en pb: {'reserve_rate_difference_bp': -0.09153922487126209, 'mean_liquidity_slope_difference_bp': 0.0006216239543770097, 'deposit_liquidity_component_bp': 0.0005594615589393087, 'deposit_payment_risk_component_bp': 7.87908684043298e-05, 'loan_rate_difference_bp': -0.09091760091672896, 'deposit_rate_difference_bp': -0.09090097244257578}.
Consumo inicial del hogar, log %: -0.0004833628526.
Descomposición Euler del consumo inicial: {'terminal': -7.438494264988577e-13, 'real_returns_dates_0_to_2': 0.0024670876098703367, 'real_returns_dates_3_to_639': -0.0029504504567040763, 'identity_error': 5.041188386872841e-12}.
Contribuciones contables al output inicial: {'current_inflation_term': 0.004828528669703902, 'future_pricing_term': -0.009131870496184882, 'worker_consumption_term': 0.00016112095087292578}.
Primera fecha con remuneración de reservas no inferior a su referencia: 1.
Errores máximos de identidades: {'Euler': 5.551115731693222e-16, 'policy_rule': 3.9471904583203724e-16, 'Phillips_Euler_reduction': 7.448055572897155e-15, 'loan_pricing': 5.221517662690189e-16, 'deposit_pricing': 7.205607638338662e-16}.

## Límites de interpretación
Las descomposiciones evalúan identidades sobre una trayectoria conjunta. No aíslan intervenciones causales independientes: mantener otros términos fijos en una derivada parcial no equivale a resolver otro equilibrio.
El canal del precio del insumo afecta producción corriente. La pérdida asignativa reportada en las IRF usa producción del período siguiente, por lo que no es la misma variable ni el mismo horizonte.
No se demuestra optimalidad dinámica bancaria, selección de rama ni equilibrio completo. Tampoco se valida una economía abierta o crecimiento sostenido.

Reproducción: `python code/irf/trace_transmission.py`. Requiere los insumos y el reporte de `compare_nonlinear_tail.py`.
