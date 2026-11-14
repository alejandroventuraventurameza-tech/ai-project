# Atlas de las 33 ecuaciones del prefijo IRF: residual, tiempo y alcance

**Revisión:** 7 de noviembre de 2026. **Fuente primaria:** code/irf/finite_irf.py, funciones prefix_residual(), remaining_residuals() y binding_period_residual(). **Contraste independiente:** code/irf/audit_prefix_rows.py, ejecutado por editorial-qa y code/verify.py. **Evidencia de soluciones:** code/irf/output/main/finite_irf_validation.json y code/irf/output/financial_blocks_audit/REPORT.json.

**Advertencia:** estas son las 33 relaciones *reducidas* del prefijo determinista con pagos idiosincráticos binarios. El DSGE estructural contiene otras condiciones de mercado, complementarias, de valor y de terminalidad que fueron eliminadas o impuestas al reducirlo; satisfacer este sistema no basta para demostrar equilibrio competitivo óptimo de horizonte infinito.

## I. Vectores, unidades y estados predeterminados

El código resuelve \(F_r(Z,v_R)=0\) por separado para \(r=S,B\), con 33 coordenadas logarítmicas:

\[
Z=(X_1^{(7)},u_0^{(10)},x_2^{(6)},u_1^{(10)}).
\]

Orden exacto de estados \(X_1=(k_{H1},k_{L1},F_{H1},F_{L1},F^B_1,\mathfrak R_1,\mathfrak M_1)\). La letra \(F_{i,t+1}\) denota el **valor facial normalizado** del repago del préstamo nuevo en t, no su principal; este es \(b_{it}=F_{i,t+1}/R_t^L\). \(F^B\) representa la promesa bancaria heredada. \(\mathfrak R_t,\mathfrak M_t\) almacenan rezagos de la regla de remuneración y la regla de reservas, no tasas independientes.

Los diez controles de cada fecha tienen orden

\[
u_t=(c_{Ht},c_{Lt},C^W_t,w_t,m_t,\Pi_t,q_t,R^D_t,R^L_t,\vartheta_t).
\]

En fecha dos, los seis estados comprimidos son

\[
x_2=(k_{H2},k_{L2},J_2,F^B_2,\mathfrak R_2,\mathfrak M_2),\qquad
F_{i2}=\theta_iJ_2k_{i2}.
\]

Esta compresión **solo es válida porque ambas firmas originan crédito con garantía activa en fecha 1**. No permite identificar \(F_{H1}\) y \(F_{L1}\) con una garantía común en fecha cero. El factor \(J_2=(1-\delta)\Pi_2q_2\) se impone como relación número 22.

Defina \(a_\delta=1-\delta\), \(\mathcal E^E_{it}=\beta_E c^E_{it}/c^E_{i,t+1}\) y \(\mathcal E^W_t=\beta_W C^W_t/C^W_{t+1}\), especializados aquí a utilidad logarítmica. Sea \(H_{it}=\theta_i a_\delta\Pi_{t+1}q_{t+1}\), \(\xi_t=R_t^D/R_t^R\), \(\bar\chi_t=(\chi^-_t+\chi^+_t)/2\), \(\Delta\chi_t=\chi^-_t-\chi^+_t\). Use \(\mathfrak h_t\) para la **razón reservas/depósitos** de los bancos, evitando confundirla con la garantía empresarial \(H_{it}\).

La producción por firma se obtiene **antes** de evaluar las 33 filas, por la FOC laboral con \(k_{it}\) predeterminado:

\[
\ell_{it}=\left(\frac{\beta m_t A_i k_{it}^{\alpha}}{w_t}\right)^{1/(1-\beta)},
\quad
F_{it}=A_i k_{it}^{\alpha}\ell_{it}^{\beta},
\quad
MRPK_{i,t}=m_t\alpha F_{it}/k_{it}.
\]

La riqueza disponible, también reconstruida antes de resolver el prefijo, es \(N_{it}=\pi^{op}_{it}+a_\delta q_tk_{it}-F_{it}^{\rm face}/\Pi_t\), con depósitos empresariales nulos en esta rama (la variable facial no debe confundirse con \(F_{it}\), producción). El código representa la promesa facial como state[2+i]; la producción es auxiliary()["output_by_type"][i].

## II. Las 17 filas exactas de fecha 0

Las igualdades se escriben como **residuo igual a cero**. Las restricciones de signo y complementariedad que distinguen las ramas deben revisarse **adicionalmente**.

| ID y nombre literal del código | Residuo estructural (igual a cero) | Fuente del manuscrito |
|---|---|---|
| R01 firm_budget_0_H | \(c_{H0}+q_0k_{H1}-F_{H1}/R^L_0-N_{H0}\) | eq:firmbudget; eq:wealth |
| R02 firm_capital_euler_0_H | \(q_0-H_{H0}/R^L_0-\mathcal E^E_{H0}(MRPK_{H1}+a_\delta q_1-H_{H0}/\Pi_1)\) | eq:capitalFOC; eq:loanFOC |
| R03 firm_regime_0_H | \(\log[F_{H1}/(H_{H0}k_{H1})]\) | eq:collateral; eq:complementarity |
| R04 firm_budget_0_L | \(c_{L0}+q_0k_{L1}-F_{L1}/R^L_0-N_{L0}\) | eq:firmbudget; eq:wealth |
| R05 firm_capital_euler_0_L | **S:** \(q_0-\mathcal E^E_{L0}(MRPK_{L1}+a_\delta q_1)\); **B:** \(q_0-H_{L0}/R^L_0-\mathcal E^E_{L0}(MRPK_{L1}+a_\delta q_1-H_{L0}/\Pi_1)\) | eq:capitalFOC; eq:loanFOC |
| R06 firm_regime_0_L | **S:** \(\log(R^L_0\mathcal E^E_{L0}/\Pi_1)\); **B:** \(\log[F_{L1}/(H_{L0}k_{L1})]\) | eq:loanFOC; eq:collateral |
| R07 bank_equity_0 | \(\log[F^B_1/(a_BR^L_0F^B_0/\Pi_0)]\) | eq:bankwealth; eq:equityidentity |
| R08 capital_supply_0 | \(q_0-1-\phi_I I_0/K_0\) | eq:q |
| R09 resources_0 | \(C^W_0+\sum_i v_ic^E_{i0}+\Gamma(I_0,K_0)+\mathcal R_0-Y_0\) | eq:resources |
| R10 worker_labor_0 | \(\log[w_0/(\chi_W L_0C^W_0)]\), aquí \(\varphi=\sigma_W=1\) | eq:household, FOC laboral |
| R11 household_euler_0 | \(\log[R^D_0\mathcal E^W_0/\Pi_1]\) | eq:household, Euler |
| R12 nkpc_0 | \(1-\varepsilon+\varepsilon m_0-\phi_p\Pi_0(\Pi_0-1)+\mathcal E^W_0\phi_p(Y_1/Y_0)\Pi_1(\Pi_1-1)\) | eq:nkpc |
| R13 reserve_rate_rule_0 | \(\log(\mathfrak R_1/R^R_0)\) | sección Instrumentos monetarios |
| R14 reserve_quantity_rule_0 | \(\log(\mathfrak M_1/M^{pre}_0)\) | sección Instrumentos monetarios |
| R15 loan_pricing_0 | \(R^L_0-R^R_0-\bar\chi_0\), **solo con cap bancaria holgada** | eq:bankFOCL |
| R16 deposit_pricing_0 | \(R^R_0+(1-\rho_0)\bar\chi_0-(\xi_0-\rho_0)\zeta\Delta\chi_0/2-R^D_0\) | eq:bankFOCD |
| R17 bank_balance_0 | \(\sum_iv_iF_{i1}/R^L_0-[F^B_0/\Pi_0+(\mathfrak h_0^{-1}-1)M^{pre}_0]\) | eq:bankbalance; eq:IBclearing |

Aquí la regla de remuneración se calcula como \(R^R_0=\bar R^R\exp\{0.5\log(\mathfrak R_0/\bar R^R)+0.5[1.5\log\Pi_0+0.125\log(Y_0/\bar Y)]+\epsilon^R_0\}\), en la parametrización ilustrativa de finite_irf.py, y la regla de cantidad utiliza persistencia \(0.5\). Esta representación coincide con la regla del paper **en esa parametrización**, no para parámetros arbitrarios.

En S, la igualdad R06 es una FOC de préstamo **sin dual de colateral** y debe acompañarse de holgura positiva. En B, R06 es una igualdad de cobertura y debe acompañarse de dual positivo. La igualdad R03 tampoco garantiza por sí misma que el dual de H sea positivo: ello se comprueba mediante la FOC reconstruida y los márgenes.

## III. Las 16 filas exactas de fecha 1

| ID y nombre literal del código | Residuo estructural (igual a cero) | Fuente |
|---|---|---|
| R18 firm_budget_1_H | \(c_{H1}+[q_1-\theta_HJ_2/R^L_1]k_{H2}-N_{H1}\) | eq:firmbudget; eq:collateral |
| R19 firm_capital_euler_1_H | \(q_1-\theta_HJ_2/R^L_1-\mathcal E^E_{H1}[MRPK_{H2}+a_\delta q_2-\theta_HJ_2/\Pi_2]\) | eq:capitalFOC; eq:loanFOC |
| R20 firm_budget_1_L | \(c_{L1}+[q_1-\theta_LJ_2/R^L_1]k_{L2}-N_{L1}\) | eq:firmbudget; eq:collateral |
| R21 firm_capital_euler_1_L | \(q_1-\theta_LJ_2/R^L_1-\mathcal E^E_{L1}[MRPK_{L2}+a_\delta q_2-\theta_LJ_2/\Pi_2]\) | eq:capitalFOC; eq:loanFOC |
| R22 common_pledge_1 | \(\log[J_2/(a_\delta\Pi_2q_2)]\) | eq:H; eq:initial_faces_manifold |
| R23 bank_equity_1 | \(\log[F^B_2/(a_BR^L_1F^B_1/\Pi_1)]\) | eq:bankwealth; eq:equityidentity |
| R24 capital_supply_1 | \(q_1-1-\phi_I I_1/K_1\) | eq:q |
| R25 resources_1 | \(C^W_1+\sum_i v_ic^E_{i1}+\Gamma(I_1,K_1)+\mathcal R_1-Y_1\) | eq:resources |
| R26 worker_labor_1 | \(\log[w_1/(\chi_W L_1C^W_1)]\) | eq:household |
| R27 household_euler_1 | \(\log[R^D_1\mathcal E^W_1/\Pi_2]\) | eq:household |
| R28 nkpc_1 | \(1-\varepsilon+\varepsilon m_1-\phi_p\Pi_1(\Pi_1-1)+\mathcal E^W_1\phi_p(Y_2/Y_1)\Pi_2(\Pi_2-1)\) | eq:nkpc |
| R29 reserve_rate_rule_1 | \(\log(\mathfrak R_2/R^R_1)\) | sección Instrumentos |
| R30 reserve_quantity_rule_1 | \(\log(\mathfrak M_2/M^{pre}_1)\) | sección Instrumentos |
| R31 loan_pricing_1 | \(R^L_1-R^R_1-\bar\chi_1\) | eq:bankFOCL, dual bancario nulo |
| R32 deposit_pricing_1 | \(R^R_1+(1-\rho_1)\bar\chi_1-(\xi_1-\rho_1)\zeta\Delta\chi_1/2-R^D_1\) | eq:bankFOCD |
| R33 bank_balance_1 | \(\sum_iv_iF_{i2}/R^L_1-[F^B_1/\Pi_1+(\mathfrak h_1^{-1}-1)M^{pre}_1]\) | eq:bankbalance |

El cálculo de las variables de fecha 2 no constituye otra optimización explícita dentro de estas 33 incógnitas: se cierra mediante las matrices \(P_0\in\mathbb R^{16\times6}\) y \(F_0\in\mathbb R^{6\times6}\) de la continuación local ya auditada. El script compara además con una continuación **no lineal finita apilada** hasta T=640; ninguna de las dos construcciones sustituye por sí sola la prueba de suficiencia del DSGE infinito.

## IV. De la cartera al crédito: signos que requieren condiciones

Del problema bancario, antes de eliminar multiplicadores,

\[
R^L_t-R^R_t=\mathbb E_\omega[\chi_t'(s^B)]+\nu_{L,t}.
\]

R15/R31 imponen \(\nu_L=0\). R16/R32 suponen también el límite de depósitos inactivo, pagos binarios equiprobables \(\omega=\pm\zeta\), solvencia holgada y pendientes \(\chi^\pm\) coherentes con el signo de excedentes. Si falla uno de estos márgenes, el residual reducido ya no es suficiente y debe reabrirse el problema bancario.

Para una firma H con garantía activa, los presupuestos y las KKT permiten reconstruir \(n_H=N_H-c_H\), \(p_H=q-H_H/R^L\) y \(b_H=H_H k'_H/R^L\). En consecuencia,

\[
100\Delta\log k'_{H}=100\Delta\log n_H-100\Delta\log p_H,\qquad
100\Delta\log b_H=100\Delta\log H_H+100\Delta\log k'_H-100\Delta\log R^L.
\]

Ambas igualdades son **identidades evaluadas sobre trayectorias conjuntas**, no efectos causales ceteris paribus. La descomposición numérica reproducible de las dos ramas se obtiene con code/irf/render_mechanism_table.py a partir del reporte financiero T=640. La rama S muestra aumento de capital; la B, caída por contracción dominante de recursos invertibles a pesar de un precio efectivo más bajo.

## V. Auditoría de alcance y reproducción

- El test nuevo verifica, en puntos perturbados **fuera de las raíces** para ambos conjuntos activos, cada una de las 33 fórmulas contra una reconstrucción independiente que reutiliza primitivas de production()/auxiliary(), sin invocar remaining_residuals(). Así detecta errores de orden y diferencias no reconocidas entre S/B.
- El reporte original del solver conserva residuos por nombre, máximo inferior a 1e-10 para la IRF pequeña, y comprobaciones de signo, pago, solvencia y caps.
- El script audit_financial_blocks.py reconstruye KKT de empresas con dual original, depósitos en esquina y dos estados de liquidación bancaria en una trayectoria no lineal finita T=640.
- Las condiciones terminales, óptimos globales de hogar/bancos/minoristas, correspondencia con un proceso estocástico de horizonte infinito, la elección de rama y la cobertura Lean de las 57 afirmaciones **siguen pendientes de auditoría de alcance exacto**.
- El reporte de 33 filas **no** justifica extender resultados a un shock de encaje, cantidad de reservas o corredor sin ejecutar por separado sus respectivas IRF.

**Comandos reproducibles:** python code/irf/audit_prefix_rows.py; python code/irf/audit_financial_blocks.py; python code/irf/render_mechanism_table.py --check; python code/verify.py.
