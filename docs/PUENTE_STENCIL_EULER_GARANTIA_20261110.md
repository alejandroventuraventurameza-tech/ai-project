# Auditoria de la igualdad de Euler y de la identidad nominal de garantia

**Fecha:** 10 de noviembre de 2026. **Estado:** IDENTIDAD ALGEBRAICA demostrada manualmente; contraste NUMERICO en 16 filas del evaluador de Python; candidato de Lean pendiente de compilation y audit de axiomas. **Importante:** la primera comparacion directa de Jacobianos en la revision 4955501667 fallo. No era legitimo declarar ese fallo sin examinar el cambio de representacion de las ecuaciones. La segunda auditoria [GitHub Actions #42916061120](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42916061120) aprobo la equivalencia numerica bajo una operacion de fila invertible.

## 1. Diferencia entre las dos expresiones: no son errores economicos

El sistema Python de 16 filas, en codigo code/irf/finite_irf.py, conserva independiente el rostro nominal unitario de la garantia J_(t+1). Su restriccion contractual establece

\[
 J_{t+1}=(1-\delta)\Pi_{t+1}q_{t+1},\qquad
 g=\log\frac{J_{t+1}}{(1-\delta)\Pi_{t+1}q_{t+1}}.
\]

Para una firma i con coeficiente de pignorabilidad theta_i y factor de descuento marginal positivo m_i, la condicion empresarial sobre capital, escrita SIN sustituir la ecuacion de rostro, es

\[
 f_i^{raw}=q_t-\frac{\theta_i J_{t+1}}{R_t^L}
 -m_i\left(u'_{ki}+(1-\delta)q_{t+1}
       -\frac{\theta_i J_{t+1}}{\Pi_{t+1}}\right).
\]

El stencil derivado a mano en code/v0m/cotas_2026_10_15/inputs/hand_linearization.py ya utilizo la identidad nominal de rostro para simplificar el rendimiento de continuacion:

\[
 f_i^{red}=q_t-\frac{\theta_i J_{t+1}}{R_t^L}
 -m_i\left(u'_{ki}+
           (1-\theta_i)(1-\delta)q_{t+1}\right).
\]

El termino de diferencia NO es un error de derivacion una vez que se considera la fila contractual de rostro:

\[
 f_i^{raw}-f_i^{red}
 =m_i\theta_i\left(\frac{J_{t+1}}{\Pi_{t+1}}
                  -(1-\delta)q_{t+1}\right)
 =m_i\theta_i(1-\delta)q_{t+1}(e^g-1).
 \tag{A}
\]

La igualdad es algebraica para denominadores no nulos y estados positivos que permiten g; no es una aproximacion.

## 2. Equivalencia EXACTA de sistemas de residuos en esta subestructura

Se define h(g)=integral desde cero hasta uno de exp(s*g) ds. Entonces exp(g)-1=h(g)*g para todo g real. El multiplicador

\[
 a_i(x)=m_i(x)\theta_i(1-\delta)q_{t+1}(x)h(g(x))
\]

es suave bajo las hipotesis de dominio economico. Reemplazar cada fila Euler reducida f_i^red por f_i^raw equivale a sumar a su fila la cantidad a_i(x)*g(x). La matriz triangular de transformacion tiene

\[
 T(x)=I+a_H(x)e_2e_4^\top+a_L(x)e_3e_4^\top,\qquad
 (T(x)-I)^2=0,\quad T(x)^{-1}=2I-T(x).
\]

La indexacion corresponde a las filas (0 presupuesto H, 1 presupuesto L, 2 Euler H, 3 Euler L, 4 rostro nominal). En todo x del dominio positivo,

\[
 F_{raw}(x)=T(x)F_{red}(x),\qquad
 F_{raw}(x)=0\Longleftrightarrow F_{red}(x)=0,
\]

si las demas 13 filas conservan sus definiciones. Esta equivalencia es sobre el par de residuales financieros con la ecuacion de rostro comun: no afirma aun que los 34 residuales SOURCE completos esten identificados.

En el estacionario x0 que es raiz, D(TF_red)(x0)=T(x0) DF_red(x0). Ademas, m_i(x0)=beta_E y (1-delta)q(x0)=J. Por tanto

\[
 Df_i^{raw}(x_0)-Df_i^{red}(x_0)
 =\lambda_i\,Dg(x_0),\qquad
 \lambda_i=\beta_E\theta_i J.
 \tag{B}
\]

Los valores de la parametrizacion son lambda_H=0.142155 y lambda_L=0.379080. La diferencia entre filas se distribuye entre las columnas del rostro nominal, inflacion futura y precio futuro de capital: en este orden, (+lambda_i,-lambda_i,-lambda_i). La primera auditoria observo solo el mayor desajuste en una de ellas y produjo provisionalmente un diagnostico incompleto; el chequeo de todas las columnas llevo a (B).

## 3. Verificacion reproducible y alcance

Codigo nuevo: code/irf/audit_stencil_nonlinear_16_rows.py. Ejecuta directamente la funcion recurrente no lineal binding_period_residual, diferenciando numericamente las 16 variables logaritmicas corrientes y futuras. Obtiene el stencil de coeficientes de 80 cifras a partir del modulo verificador y aplica exactamente la misma permutacion de filas (0,2,1,3,4,...,15) antes de cotejarlo.

| Criterio | Valor |
|---|---:|
| Residuo de las 16 filas en el estacionario | 3.55e-15 |
| Maxima diferencia entre derivadas sin row shear | 0.3790800000014 |
| Maxima diferencia despues de row shear | 3.86330612e-9 |
| Maxima discrepancia de la identidad (A), aun FUERA de g=0 | 1.36717894e-16 |
| Factores estacionarios lambda_H y lambda_L | 0.142155, 0.379080 |

El programa usa diferencias centrales con pasos 1e-6 y 5e-7 y exige tolerancia absoluta 2e-5 despues de la operacion de fila. Conserva el error crudo y exige que permanezca mayor que 0.1; asi la auditoria no puede aprobar simplemente porque se hayan debilitado sus cotas. El resultado de CI aprobado esta en #42916061120, SHA c9893632e27c7378e7b13ad0b0e2af0bf2f1866d, artefacto pinned-stencil-matrix-bridge.

**Estado de formalizacion — COMPROBADO POR EL KERNEL:** el modulo [HandStencilPledgeRowEquivalenceCandidate.lean](../lean/candidates/Ventura26LiquidityAllocation/HandStencilPledgeRowEquivalenceCandidate.lean) fue compilado satisfactoriamente con el toolchain fijado de Lean 4 y Mathlib en [GitHub Actions #42918395877](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42918395877), correspondiente al commit `4a0dfb524527f505ac2e00fb288a1d5078e6f778`. Los cuatro teoremas imprimen unicamente los axiomas fundacionales `propext`, `Classical.choice`, `Quot.sound` y **no** `sorryAx`. Sus enunciados prueban la identidad algebraica, la igualdad de Euler al imponer la garantia, la equivalencia del conjunto de ceros por shear de filas y una simplificacion de la definicion fuente literal `localReducedFirmCapitalEulerResidual`. **No** formalizan una matriz de 16 derivadas en Lean ni transfieren las 34 filas del operador economico original a Python.

## 4. Que SI se obtiene y que NO

El descubrimiento rescata la representacion lineal del stencil para la rama binding del evaluador Python: la diferencia de filas es explicable por una transformacion invertible y no requiere modificar P0/F0 por ese motivo. Esto no exime de probar las correspondencias matematicas de las restantes filas y la derivada del operador original Lean, ni reemplaza la verificacion de las 34 condiciones SOURCE, pagos contingentes, optimizacion bancaria y transversalidad.

## 5. Contrato de indexacion de 33 filas y ecuacion 34 separada

El conjunto de 33 etiquetas fuente y el evaluador Python comparten los mismos nombres de ecuaciones pero no el mismo orden de las primeras seis filas. La permutacion fuente -> Python de las seis filas empresariales iniciales es `(0,3,1,4,2,5)`, y de las cinco empresariales al comienzo de fecha uno es `(17,19,18,20,21)`. Ninguna igualdad de Jacobianos puede darse por probada a partir de la igualdad de sus indices numericos: debe aplicarse la permutacion verificada y justificar las diferencias algebraicas y de escala de residuos.

El auditor `code/irf/audit_python_lean_prefix_row_permutation.py` inspecciona las 33 ramas fuente `localPrefixEquationOfIndex`, comprueba que cada una aparece en `localReducedPrefixResidual`, enlaza sin duplicados las 33 etiquetas literales de `PREFIX_ROW_NAMES` de Python y exige una permutacion biyectiva. Tambien comprueba que el operador ampliado `augmentedBoundaryZeroResidual` contiene **33 residuos y una condicion distinta**: `localNormalizedCollateralDualL P (localPrefixLogChart Z0 z)`. Este ultimo residuo no aparece en el evaluador Python original de 33 filas.

La comprobacion es **SINTACTICA**, no un teorema de equivalencia semantica de las 34 ecuaciones. Su salida es `code/irf/output/lean_python_33_row_permutation.json`.

**Compuerta siguiente:** establecer la equivalencia economica fila por fila (con transformaciones invertibles y factores de escala positivos, cuando corresponda) entre el operador fuente de 34 condiciones y un ejecutor que incluya explicitamente la condicion de dual; obtener derivadas bajo dominio positivo y cuantificar el radio de continuacion no lineal. Sin ello no hay certificado de equilibrio infinito ni conclusion sobre crecimiento permanente.
