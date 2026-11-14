# IE Project: compuerta de Fréchet en carta SOURCE (13 de noviembre de 2026)

## Estado exacto de los objetos

El SOURCE conservado en `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean` define:

- `LocalPrefixEquation` con 33 constructores; `localPrefixEquationOfIndex : Fin 33 → LocalPrefixEquation` asigna los indices 0–32 en orden sin duplicados. Filas de Euler de fecha uno: 19 (H) y 20 (L); pignoracion comun: 21.
- `localPrefixLogChart Z0 z`: los 33 niveles originales multiplicados, coordenada a coordenada, por `exp(z_j)`.
- `localReducedPrefixLogResidualVector`: EXACTAMENTE la composicion del residuo economico SOURCE `localReducedPrefixResidual` con esa carta y con `localPrefixEquationOfIndex`.
- `LocalReducedPrefixLogJacobianCertifiedAt`: el certificado fuerte usado en la proposicion del paper. Exige positividad de todos los niveles de `Z0`, un radio estrictamente positivo de diferenciabilidad del SOURCE original en una bola de la carta logaritmica, y un inverso continuo lineal `Jinv` del `fderiv` SOURCE en `z=0`, que es simultaneamente inverso izquierdo y derecho y satisface la cota estricta `‖Jinv‖ < inverseNormBound`. El certificado no se obtiene postulando una matriz numerica.

## Lo demostrado antes de esta compuerta

Los modulos SOURCE anteriormente compilados prueban algebraicamente la cizalla doble en todas las 33 filas, su inversa explicita, equivalencia de ceros, y la identidad diferencial fila a fila sobre trayectorias diferenciables en una raiz de pignoracion. El puente hacia `localPrefixLogChart` esta kernel-verificado en el commit `85831489ba61d6cf2ea17e0cb08c51f0a53feb6a` (workflow `43482563726`).

## Compuerta actual de indexacion

`SourceEulerLogChartRowIndexCandidate.lean`, incluido en el commit `da2f46879d0fa6eae021875cdaf16a7332d35c25`, busca verificar dentro de Lean que `localPrefixEquationOfIndex` es biyectiva y que la equivalencia de ceros es valida en los vectores `Fin 33 → ℝ` exactos. Esta prueba no se clasifica como demostrada hasta el SUCCESS del workflow que la compila.

## Siguiente teorema economico que falta

Sea `F(z) = localReducedPrefixLogResidualVector ... z` y `Ftilde(z) = sourceNominalPledgeShearedLogResidualVector ... z` para el MISMO `P`, `I`, `Z0`, `dateOne`, `recurrent` y `tail`. Sea `zstar` una raiz genuina SOURCE, con `F(zstar)=0`. Se busca demostrar, bajo regularidad economica suficiente en una vecindad,

```text
fderiv R Ftilde zstar = L(aH(zstar), aL(zstar)) ∘L fderiv R F zstar
```

donde `L` es la operacion lineal real de filas probada previamente, correctamente reindexada a `Fin 33`. Para justificarlo hay que aportar una demostracion de `DifferentiableAt`/ `HasFDerivAt` de las 33 funciones SOURCE, asi como la regularidad de los coeficientes y de la regla de continuacion `tail`. Las pruebas direccionales previas proporcionan la identidad necesaria en cada linea pero **no eliminan** esas hipotesis.

Una vez establecida la igualdad de `fderiv`, la biyectividad se transporta por la inversa explicita de `L`; **eso no produce** una cota estricta `‖Jinv‖` de manera automatica. La cota requiere un inverso certificado de `fderiv R F 0`, con enclosure dirigido, y una desigualdad submultiplicativa para la nueva inversa, si se quiere un certificado del sistema transformado.

## Brechas economicas independientes

1. Identidad completa del operador SOURCE con el programa Python, incluyendo primitivas, rama, normalizaciones y extension recurrente exacta de `tail`; no se infiere de igualdad de nombres ni de un test numerico.
2. Regularidad positiva, de denominadores y de las condiciones de complementariedad a lo largo de la bola usada por el teorema de funcion implicita.
3. Certificado de inversa de la matriz de Fréchet real de `localReducedPrefixLogResidualVector` y de cota estricta verificada.
4. Existencia de una solucion real y compatibilidad de la continuacion completa (no solo sistema local reducido), y luego calculos de IRF y crecimiento reproducibles.

## Regla de reporte

- **DEMOSTRADO**: teorema Lean compilado y auditoria de axiomas del objeto exacto.
- **NUMERICO**: ejecucion trazable bajo parametros, entorno y tolerancias identificados.
- **PENDIENTE**: puente SOURCE/Python, regularidad y certificado de inversa economica que no han sido completados.

No fusionar PR #2 a `main` ni anunciar equilibrio infinito hasta superar las obligaciones.
