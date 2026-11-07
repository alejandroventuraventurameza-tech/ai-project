# Atlas matemático de mecanismos y cronología — versión 1

**Propósito:** reunir las ecuaciones mínimas que conectan los agentes del modelo, los instrumentos de política, las restricciones empresariales y las respuestas numéricas. No se declara completo el inventario de FOC ni se sustituyen las pruebas del manuscrito. Cada identificador remite al archivo paper/paper.tex, salvo indicación contraria. El documento acompaña los tres diagramas editables en paper/figures/architecture.

## I. Naturaleza de la economía y variables fundamentales

El modelo distingue cantidades reales de títulos nominales, estados predeterminados de decisiones elegidas y precios monetarios de precios de recursos productivos. Esta separación no es cosmética: la remuneración de reservas altera el rendimiento de un pasivo del banco central, mientras que la inversión genera capital físico por medio del productor de capital. Confundir esos dos márgenes equivaldría a introducir máquinas mediante una operación financiera.

| Símbolo | Significado y unidad | Calendario |
|---|---|---|
| \(t,\ s_t\) | período trimestral ilustrativo; estado agregado Markov | \(s_t\) observado al decidir en t |
| \(A_i,\theta_i,v_i\) | productividad, pignorabilidad y masa de empresas i=H,L | parámetros |
| \(k_{it}\) | capital físico instalado y utilizado para producir | predeterminado en t |
| \(\ell_{it},F_{it}\) | trabajo corriente e insumo producido | elección/realización en t |
| \(k_{i,t+1}\) | capital nuevo a instalar para producir en t+1 | control elegido en t |
| \(N_{it},c^E_{it},a_{it},b_{it}\) | patrimonio corriente, consumo, depósito y principal de préstamo empresarial | patrimonio tras repago; nuevos controles en t |
| \(R^L_t,R^D_t\) | retornos nominales brutos de crédito y depósitos | precios endógenos de contratos nuevos |
| \(R^R_t,\ M_t^{pre},\rho_t,\Delta_t\) | remuneración y cantidad de reservas, encaje y amplitud del corredor | reglas o instrumentos monetarios |
| \(R^F_t,R^W_t\) | rendimiento OTC endógeno y techo de facilidad | determinada por corredor y matching; \(R^W_t=R^R_t+\Delta_t\) |
| \(d^D_{jt},l^B_{jt},m^B_{jt},e_{jt}\) | depósitos, préstamos empresariales, reservas y patrimonio de banco j | cartera anterior a pagos |
| \(\omega_{jt},s^B_{jt},f_{jt},W_t\) | shock de pagos, exceso de reservas, deuda interbancaria y facilidad pública | se realizan y liquidan después de la cartera |
| \(P_t,\Pi_t,w_t,m_t,q_t\) | nivel nominal, inflación, salario real, precio real del insumo y del capital | determinados conjuntamente |
| \(C^W_t,L_t,K_t,Y_t\) | consumo trabajador, empleo, capital agregado y producto corriente | equilibrio del período |
| \(H_{it},\mu_{it},\lambda_{it},\upsilon_{it}\) | garantía por unidad de capital, dual de cobertura, valor del patrimonio y dual normalizado | contrato/KKT; \(\upsilon=\mu/\lambda\) |

Las \(R\) son rendimientos brutos por período, no tasas porcentuales netas ni tasas interbancarias anualizadas. La promesa nominal del nuevo crédito \(b_{it}\) es \(P_t R^L_t b_{it}\); su valor real en t+1 es \(R^L_t b_{it}/\Pi_{t+1}\).

## II. El flujo circular: siete bloques y su contabilidad

**Hogar.** El presupuesto eq:household vincula ingresos laborales, depósitos, bonos y dividendos con consumo y nuevos activos. Su Euler, cuando el depósito está en interioridad, satisface:

\[
1=\mathbb E_t\!\left[\Lambda^W_{t,t+1}\frac{R_t^D}{\Pi_{t+1}}\right].
\]

**Empresas.** Producción eq:production y costo laboral implican \(m_tF_{\ell,i}=w_t\), mientras que eq:wealth determina patrimonio tras rendimiento operativo, reventa de capital y cancelación real de promesas heredadas. El presupuesto eq:firmbudget y la cobertura eq:collateral determinan qué inversión puede financiarse.

**Minoristas y productor de capital.** Los minoristas compran el insumo empresarial, transforman unidades de bien final y fijan precios con ajuste Rotemberg. Su condición de precios está en eq:nkpc. El productor de capital transforma bienes finales en \(I_t\) y determina \(q_t=1+\phi_I I_t/K_t\), bajo interioridad de inversión.

**Bancos comerciales.** El balance eq:bankbalance exige \(l^B+m^B=d^D+x\), con límites de cartera eq:bankcaps. Tras los pagos, el exceso de reservas es \(s^B=m^B-\rho d^D+(R^D/R^R-\rho)\omega d^D\), eq:surplus.

**Interbancario OTC.** Deficitarios y excedentarios negocian reservas, no capital físico. Las fracciones de matching satisfacen eq:IBclearing, y la tasa media de transacciones cumple:

\[
R^F=R^R+(R^W-R^R)v(\vartheta),\qquad \vartheta=S^-/S^+.
\]

La facilidad del banco central cubre déficits no emparejados y eleva reservas posteriores a pagos en la medida de ese crédito. No debe confundirse con un préstamo empresarial.

**Sector público.** El balance del banco central y el presupuesto público consolidado se detallan en eq:gov; \(M^{post}=M^{pre}+W\). La compra de bonos por el banco central cambia propietarios de activos y composición de pasivos: no crea recursos agregados sin contrapartida fiscal.

**Limpieza.** La consolidación elimina contratos financieros internos. La restricción de recursos eq:resources conserva solamente consumo, costos de producción de capital y costos reales de fijación de precios:

\[
C_t^W+\sum_i v_i c^E_{it}+\Gamma(I_t,K_t)+\mathcal R_t=Y_t.
\]

Así, el «flujo circular» no es una metáfora: es el mecanismo que hace que presupuestos, balances y activos se cancelen en la cuenta agregada.

## III. Timing que debe comprenderse antes de derivar KKT

1. Se observa el estado agregado \(s_t\) y se heredan \(k_{it}\) y promesas nominales. La inflación y los precios corrientes se determinan en equilibrio, no están predeterminados.
2. Las firmas contratan trabajo y producen con \(k_{it}\). Se cancelan deudas heredadas y se valoran los activos restantes a precios corrientes; de ello surge \(N_{it}\).
3. Firmas, hogares, bancos y sector público eligen o negocian contratos nuevos y carteras, incluido \(k_{i,t+1}\), \(b_{it}\) y \(m^B\). Los precios de la cartera son simultáneos.
4. Se realizan pagos idiosincráticos, que trasladan depósitos entre bancos y producen \(s^B\). No constituyen una pérdida directa de riqueza agregada del empresario.
5. OTC y facilidad redistribuyen/cubren liquidez. Se cierran reservas posteriores a pagos y se preparan rendimientos y transición a t+1, incluida salida/renovación bancaria.
6. El capital elegido en t se utiliza en producción de t+1; la promesa generada hoy se cancela a través de la inflación de t+1.

Esta cronología impide atribuir la producción corriente \(Y_t\) a una modificación contemporánea de \(k_{i,t+1}\). La intervención puede alterar \(Y_t\) inmediatamente por precios y trabajo, mientras que la reasignación de capital tiene efectos productivos directos desde la fecha siguiente.

## IV. Ecuaciones que sostienen las flechas de política

La regla ilustrativa del banco central determina \(R^R_t\), pero no directamente las tasas del hogar y de la firma:

\[
\log R_t^R=\varrho_R\log R_{t-1}^R+
(1-\varrho_R)\left[\log\bar R^R+\phi_\pi\log\Pi_t+
\phi_y\log(Y_t/\bar Y)\right]+\epsilon_t^R.
\]

La cantidad de reservas sigue una regla separada, mientras que el corredor fija \(R^W_t=R^R_t+\Delta_t\). En el caso de la IRF vigente se perturba \(\epsilon^R_0\); no se altera \(\rho\), \(M^{pre}\) de forma exógena ni \(\Delta\).

La transmisión bancaria exige pasar por la condición de cartera, no saltar directamente de \(R^F\) a \(R^L\):

\[
R^L-R^R=\mathbb E_\omega[\chi'(s^B)]+\nu_L,\quad
R^D-R^R=\mathbb E_\omega[\chi'(s^B)
\{1-\rho+(\xi-\rho)\omega\}]-\nu_D.
\]

Aquí \(\xi=R^D/R^R\) y \(\nu_L,\nu_D\) son duales no negativos. Si esos límites están holgados, desaparecen de las ecuaciones; de lo contrario, omitirlos cambia el modelo.

La etapa empresarial traduce el costo de financiación en elección de capital mediante eq:firmbudget y eq:collateral:

\[
k_{i,t+1}=\frac{N_{it}-c^E_{it}}{q_t-H_{it}/R_t^L},
\]

cuando \(a_{it}=0\), la cobertura está activa y \(q_t>H_{it}/R_t^L\). La derivada parcial con \(N-c,q,H\) fijos es negativa, pero la derivada total de equilibrio combina los cambios simultáneos de patrimonio, consumo, garantía y precio del capital. Esta es la razón formal por la cual la rama B puede tener más crédito y menos inversión.

La última flecha hacia producto corriente no se deriva del capital todavía no instalado: Euler y eq:nkpc determinan precios y consumo, y las condiciones laborales con capital predeterminado dan en el subcaso auditado:

\[
\Delta\log Y_0=\frac13(\Delta\log m_0-\Delta\log C^W_0).
\]

La pérdida asignativa condicional está definida por eq:dynamic_loss_at_optimal_labor y eq:loss_relative_capital_derivative y utiliza la producción del período siguiente. **No representa bienestar ni tiene la misma fecha que \(Y_0\).**

## V. Método que genera la IRF

Para cada rama r del sistema reducido, el prefijo satisface \(F_r(Z,\mathbf v)=0\), con 33 incógnitas expresadas en coordenadas logarítmicas divididas en \(7+10+6+10\) componentes. Un paso de Newton resuelve \(J_r(Z_n)\Delta Z=-F_r(Z_n,\mathbf v)\) y aplica \(Z_{n+1}=Z_n+\alpha_n\Delta Z\), con Jacobiano por diferencias finitas centradas y búsqueda amortiguada. La continuación principal desde t=2 utiliza una gráfica local lineal validada; la comparación no lineal finita emplea Newton disperso hasta T=640.

Los CSV de code/irf/output/main y las figuras de paper/figures son generados por code/irf/reproduce.py. Las tasas se reportan como \(10^4(R_t-R_t^0)\) puntos básicos sin anualizar, y las cantidades positivas como \(100\log(x_t/x_t^0)\). **No** se utilizó stochastic gradient descent ni value function iteration para obtener estas IRF.

## VI. Estado de este atlas

Este primer atlas cubre el circuito completo, la cronología, los instrumentos y las ecuaciones de los mecanismos principales. Faltan todavía el inventario literal de *todas* las KKT individuales, las filas de los 33 residuos y la correspondencia de cada resultado del paper con Lean. El trabajo siguiente es completar esos anexos sin alterar hipótesis y verificar gráficamente que las ecuaciones de las tres figuras coincidan con este texto.
