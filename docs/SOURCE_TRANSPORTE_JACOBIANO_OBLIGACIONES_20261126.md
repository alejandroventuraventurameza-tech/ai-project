# Transporte de Jacobianos SOURCE–targetizado: obligación siguiente

**Corte:** 26 de noviembre de 2026. **Estado:** DERIVACIÓN MATEMÁTICA CONDICIONAL; **NO** formalizada todavía en Lean.  
**Predecesor probado:** PR #20, `CurrentSourceTwoDateBankTargetization.lean`, teorema `targetizedPrefix33_eq_fullEconomicBankShear`.

## 1. Identidad de partida y dominio

Sobre un abierto `U` de una carta de coordenadas logarítmicas válida, fijadas las primitivas, el estado heredado, los parámetros recurrentes y terminales, escribimos

`G(z) = E(z) F(z)`,

donde `F` es el prefijo SOURCE de 33 residuos, `G` el prefijo targetizado y `E` es la transformación triangular exacta del PR #20. En la formalización actual, la identidad requiere `P.matchingIntensity = Real.log 2` y `TargetBankAdmissible` en ambas fechas. No está probado que estas condiciones definan un entorno abierto alrededor del candidato numérico; en particular la condición no estricta `tightness ≤ 1` exige tratar explícitamente la posible frontera.

## 2. Lema de transporte local (prueba matemática)

**Hipótesis adicionales por acreditar en SOURCE:** (i) `F : U → ℝ³³` y `E : U → GL(33,ℝ)` son diferenciables en `z₀`; (ii) `F(z₀)=0`; (iii) `z₀` pertenece al interior del dominio donde se obtuvo la identidad. Entonces, por la regla del producto,

`DG(z₀)[h] = DE(z₀)[h] F(z₀) + E(z₀) DF(z₀)[h] = E(z₀) DF(z₀)[h]`.

Por tanto, `DG(z₀) = E(z₀) DF(z₀)`. Si `E(z₀)` es invertible, `DG(z₀)` es invertible si y solo si `DF(z₀)` es invertible. Siempre que ambas lo sean,

`(DG(z₀))⁻¹ = (DF(z₀))⁻¹ (E(z₀))⁻¹`.

En una norma matricial submultiplicativa, esto implica

`||(DG(z₀))⁻¹|| ≤ ||(DF(z₀))⁻¹|| · ||(E(z₀))⁻¹||`,

pero **ninguna de las normas del lado derecho ha sido certificada numéricamente para el Jacobiano SOURCE 33×33**.

**Advertencia:** fuera de la raíz, el término `DE(z)[h]F(z)` NO desaparece. No es válido afirmar `DG=E DF` en toda una bola ni transportar cotas sin controlar ese término. Para `z` arbitrario en la bola,

`DG(z)[h]=DE(z)[h]F(z)+E(z)DF(z)[h]`.

## 3. Compatibilidad de coordenadas y parámetros

Antes de reutilizar una matriz construida en Python, comprobar la igualdad **funcional** de los 33 residuos, el orden de filas y columnas, los signos, las convenciones de pagos y el punto de evaluación. Si las coordenadas están relacionadas por una carta diferenciable `z=φ(x)`, debe incluirse el factor de cadena `Dφ(x₀)`. Igualmente, con variables exógenas `p`, el transporte de derivadas parciales respecto de política incluye `∂pE · F`, que se anula solo sobre una raíz común y con las otras coordenadas fijadas de manera coherente.

## 4. Comp puertas Lean y numéricas pendientes

1. Probar continuidad y diferenciabilidad de `E` y `F` en un abierto genuino de la carta SOURCE, sin ocultar las condiciones de dominio.
2. Formalizar el lema de producto y su simplificación en una raíz y auditar `#print axioms` de la proposición exacta.
3. Verificar para un mismo candidato SOURCE: `F(z₀)=0` o un procedimiento de inclusión validado, `TargetBankAdmissible` en las dos fechas e invertibilidad cuantitativa del Jacobiano real, con residuos/cotas e identificadores de versión.
4. Cotejar las 23 filas restantes y la definición concreta de `finite_irf.py`; ninguna equivalencia Python–SOURCE se deduce del PR #20.
5. Recién después evaluar la reducción escalar de Proposición 3.1, el sistema aumentado de 34 condiciones y las ramas S/B del equilibrio dinámico. La invertibilidad por sí sola no crea una raíz.

## 5. Clasificación de evidencia

- **DEMOSTRADO en Lean (PR #20):** identidad no lineal exacta y equivalencia de ceros SOURCE–SOURCE targetizado, condicionadas al dominio y parametrización.
- **DERIVADO matemáticamente aquí, bajo hipótesis nuevas:** identidad de Jacobianos en una raíz, equivalencia de rango e inversas.
- **PENDIENTE:** todas las nuevas hipótesis de regularidad para el operador SOURCE concreto, certificado del Jacobiano y existencia de raíz, validación oficial `PaperContribution` y equilibrio dinámico.

Este documento no modifica `paper/paper.tex`, las IRF, la calibración ni las pruebas Lean existentes. No es una afirmación de cierre del proyecto.
