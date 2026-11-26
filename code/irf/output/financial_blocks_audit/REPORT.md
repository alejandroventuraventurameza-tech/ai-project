# Auditoría de empresas y liquidación bancaria

Literal numerical firm KKT, deposit corner, bank balance and two-atom settlement on the deterministic reduced nonlinear T=640 path. Necessary conditions and a conditional one-period concavity bound; no global dynamic sufficiency claim.

## Empresa: condiciones sin eliminar el multiplicador
Se reconstruye N a partir de producción, salario, capital heredado y repago nominal; no se define como residuo del presupuesto.
Con u_E(c)=log(c), M_E=beta_E*c_t/c_(t+1) y h=theta_i(1-delta)Pi_(t+1)q_(t+1):
- upsilon=mu/lambda=1/RL-M_E/Pi_(t+1). Esta igualdad reconstruye el dual desde la FOC de préstamos.
- Se comprueban además capital, caja, complemento, no negatividad del dual y del colateral, y la esquina sin depósitos.
- El dual de no depositar es 1-M_E*RD/Pi_(t+1); resulta positivo. Crédito positivo con depósitos empresariales cero es consistente con esa esquina.
- La cobertura robusta se especializa a la única transición agregada del experimento; no audita un árbol agregado estocástico general.

## Identidades para H restringida
k_(H,t+1)=(N_Ht-c_Ht)/(q_t-h_Ht/RL_t).
Delta log k_next = Delta log(N-c) - Delta log(q-h/RL).
b_Ht=h_Ht*k_(H,t+1)/RL_t; por tanto Delta log b = Delta log h + Delta log k_next - Delta log RL.
Las contribuciones son identidades sobre soluciones conjuntas, no contrafactuales causales independientes.

| Rama | Crédito H (log %) | Capital elegido H (log %) | Cambio dual normalizado H |
|---|---:|---:|---:|
| slack | 0.001095170561 | 0.0001640913165 | -1.216744096e-06 |
| binding | 0.0008406449876 | -0.001072639169 | 2.308135988e-05 |

## Recursos propios de H: trazabilidad de patrimonio y consumo
n=N-c=beneficio operativo + valor de reventa del capital instalado - repago real heredado - consumo.
Se verifica su descomposición exacta en niveles y se convierte a contribuciones logarítmicas mediante Delta log(n)/Delta n. No son efectos causales aislados.

- slack: {'operating_profit': -5.90473084583321e-05, 'resale_value_installed_capital': 1.68259982491964e-05, 'negative_inherited_real_repayment': 8.337307031732372e-05, 'negative_consumption': -1.3804205313319414e-05}
- binding: {'operating_profit': -0.0015548484854207183, 'resale_value_installed_capital': -0.00034322920942205567, 'negative_inherited_real_repayment': 7.971510478781367e-05, 'negative_consumption': 7.638250044098111e-05}

## Banco: contabilidad y condiciones de reducción
Se calculan por separado los dos pagos, el exceso de reservas, préstamo interbancario, facilidad, reservas finales y retorno detallado. Se verifican clearing esperado, encaje posterior, caps holgados, orden de pendientes, solvencia y renovación.
Bajo los precios y matching del régimen, chi es cóncava y homogénea. Su pendiente en cada átomo candidato proporciona una cota superior global de una etapa:
E[N_nominal] <= (RR+E[g])*x + (RL-RR-E[g])*L + (RR-RD+E[g*(1-rho+(xi-rho)*omega)])*D.
Las ecuaciones de precios anulan los coeficientes de L y D y hacen RR+E[g]=RL. Por ello la cota es RL*x. Se comprueban sus coeficientes numéricamente y que la cartera candidata alcanza la igualdad.
Este argumento requiere precios y matching dados e independencia de los pesos futuros respecto al pago individual. No resuelve por sí solo la elección dinámica de dividendos ni demuestra el valor infinito.

## Resultado e interpretación
En S, H recibe más crédito, elige más capital y baja su dual. En B, recibe más crédito, pero elige menos capital y sube su dual. El capital efectivo y las promesas no se confunden con el principal del préstamo.
Por tanto, el experimento no justifica describir las dos ramas como relajación económica uniforme de la restricción. La expansión de crédito no equivale a una mejora asignativa ni a una caída del valor marginal del colateral.
Los errores y márgenes se detallan en REPORT.json; el inventario de las 33 filas es una trazabilidad de fuente, no cobertura formal ni prueba de suficiencia.

## Pendientes
Optimalidad dinámica, valor y dominación de todas las políticas admisibles; suficiencia de los demás agentes; instancia de equilibrio completo y reflexión Lean de la evidencia externa.

Reproducción: `python code/irf/audit_financial_blocks.py`. No cambia las IRF principales ni parámetros.
