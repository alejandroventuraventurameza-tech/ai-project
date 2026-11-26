# IE Project 18 — cierre verificable de la compuerta Euler y política (11-XI-2026)

## Revisión y ejecuciones

Revisión del código auditado: `90734f2a2f4eee0266eaa36bfa8c9b3bf59940f1`.

| Compilación | Run | Estado observado |
|---|---|---|
| `build`, Python `verify.py` y cuatro PDFs | [43050717824](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050717824) | success / success |
| `editorial-qa`, sintaxis y auditoría LaTeX | [43050718052](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050718052) | success / success |
| Lean stationary policy/payment | [43050718068](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050718068) | success |
| Lean pledge-row equivalence | [43050717837](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050717837) | success |
| Lean paper claims | [43050717944](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050717944) | success |
| Source/stencil transition bridge | [43050717963](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050717963) | success |
| Same-predecessor nonlinear tail | [43050718278](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050718278) | success |
| Lean boundary proof gate | [43050718262](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43050718262) | cancelled: no verdict in this run |

La revisión enumera resultados CI del SHA; un `success` no prueba automáticamente contenido económico más amplio que los enunciados efectivamente compilados y las hipótesis de cada módulo. Una cancelación no es fallo matemático ni prueba exitosa.

## Correspondencia funcional empresarial

Las dos filas Euler de fecha uno satisfacen la *identidad transcrita condicional*:

`F_i(z) = G_i(z) + theta_i A_2(z) q_i(z) expm1(g(z))`,

`q_i(z) = 1/R^L_1(z) - m_i(z)/Pi_2(z)`, `g(z)=log(J_2(z)/A_2(z))`.

Equivalente:
`F_i=G_i+a_i(z)g`, con `a_i(z)=theta_i A_2 q_i h(g)` y `h(g)=expm1(g)/g`, `h(0)=1`.

En un punto de raíz común, `g=0`:

`DF_i = DG_i + a_i Dg`.

Fuera de raíz:
`DF_i = DG_i + a_i Dg + g Da_i`.

El script `code/irf/audit_source_firm_budget_euler_shear.py` ahora coteja la identidad funcional y su derivada de coeficiente variable en las dos ramas y 33 direcciones. La corrida de `build` comprueba ese script como parte de `verify.py`.

## Fronteras aún no probadas

1. Identidad literal de las 33 funciones SOURCE respecto de las 33 funciones Python bajo una única carta y datos `LocalPrefixDateData` compartidos, en un entorno abierto.
2. Equivalencia del jacobiano SOURCE/Python completo, inversibilidad certificada de `DF` y radio de validez.
3. Reconciliación completa de 34 relaciones KKT, optimalidad intertemporal y condición de transversalidad.
4. Equilibrio de horizonte infinito y efectos de crecimiento permanentes.
5. Comparación de raíces S/B distintas con el mismo estado heredado, separada del experimento `make_boundary`.

**Conclusión de fase:** las auditorías parciales de Euler, pagos y compilación pasan en `90734f2`; no publicar «equilibrio completo demostrado». PR #2 sigue en borrador, `main` sin fusionar.
