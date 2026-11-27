# SOURCE-33: producción agregada en la carta logarítmica

**Estatus:** derivación algebraica pendiente de formalización off-root. Las ecuaciones originales fueron cotejadas en EconomicModel.lean y StationaryPrimitivesCandidate.lean. PR #59 prueba únicamente identidad y positividad EN EL ORIGEN y un lema de continuidad CONDICIONAL. No llamar «demostrado en Lean» a las fórmulas siguientes hasta su kernel.

## Definiciones y derivación económica

El modelo estacionario fija \(\alpha=2/5,\beta=1/2,A_t=1\), con productividad de firma \(a_i>0\), capital \(K_{it}>0\), precio del insumo \(m_t>0\) y salario \(w_t>0\). De la definición original:

\[
L_{it}=(\beta m_t A_t a_i K_{it}^{\alpha}/w_t)^{1/(1-\beta)},
\qquad
Y_{it}=A_t a_i K_{it}^{\alpha} L_{it}^{\beta}.
\]

Con los exponentes calibrados:

\[
L_{it}=(m_t a_i K_{it}^{2/5}/(2w_t))^2,\qquad
\boxed{Y_{it}= (m_t/(2w_t))a_i^2 K_{it}^{4/5}}.
\]

El paso por la raíz cuadrada requiere positividad y una prueba explícita con Real.rpow, no simplemente manipulación formal de exponentes.

## Carta SOURCE: índices Fin 33, cero-basados

En la fecha 0, el capital corriente es heredado y no se desplaza con las 33 coordenadas. El precio m0 es z11 y el salario w0 es z10. En la fecha 1, K_H y K_L son z0 y z1, m1 es z27 y w1 es z26.

Así, las identidades propuestas fuera de la raíz son

\[
\boxed{Y_0(z)/\bar Y=\exp(z_{11}-z_{10})},
\]

\[
\boxed{Y_1(z)/\bar Y
=\exp(z_{27}-z_{26})
\bigl(s_H\exp(\tfrac45 z_0)+s_L\exp(\tfrac45 z_1)\bigr)}.
\]

Aquí \(s_i=\omega_i\bar Y_i/\bar Y>0\), con \(\omega_i\) masa estacionaria de la firma; \(s_H+s_L=1\). La masa \(\omega_i\) NO es el precio del insumo \(m_t\).

## Derivadas en la raíz (propuestas, no formalizadas)

Para cualquier dirección \(h\in\mathbb R^{33}\):

\[
D\log(Y_0/\bar Y)(0)[h]=h_{11}-h_{10},
\]
\[
D\log(Y_1/\bar Y)(0)[h]
=h_{27}-h_{26}+\tfrac45(s_Hh_0+s_Lh_1).
\]

La regla de reservas usa estas expresiones multiplicadas por
\((1-\rho_R)\phi_Y\), con fecha y orden de coordenadas propios.
No atribuir estas derivadas a reglas de encaje, rama S, frontera 34,
continuación P0 perturbada o la implementación Python.

## Comp puertas de auditoría

1. Demostrar en Lean la identidad económica de cada firma bajo la positividad y los exponentes reales fijados.
2. Sustituir la carta fuente y demostrar exactamente ambos cocientes Y_t/Ybar fuera de la raíz.
3. Demostrar s_H+s_L=1 y positividad de los pesos, a partir de las masas originales.
4. Obtener continuidad y Fréchet derivadas, verificar el kernel y #print axioms sin sorryAx.
5. Conectar el resultado al puente monetario del PR #58; conservar como pendientes el Jacobiano completo, su inversa y SOURCE--Python.
