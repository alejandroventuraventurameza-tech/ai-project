# Lema 4.3 — diferenciación de capital agregado y producción ajustada desde las funciones fuente

**Fecha de trabajo:** 8 de noviembre de 2026. **Rama:** `work/lean-ci-validation-otc-20261106`.  
**Criterio de evidencia:** la demostración escrita y las **nueve declaraciones nuevas** de derivadas/participaciones/regla compuesta, cuota de output físico y log cociente de capitales fueron validadas en corridas Lean con `#print axioms` sin `sorryAx`: #42503513399, #42503571340 y #42504364485. Sumadas a 28 auxiliares previos, hay **37 teoremas verificados** sobre 4.3. La equivalencia formal del enunciado económico íntegro, y la validación del equilibrio dinámico, permanecen pendientes.

## 1. Objetivo y alcance

El objetivo es cerrar el segmento diferencial del Lema 4.3 de `paper/paper.tex`, a saber,

```text
d Loss = alpha (kappa_H - omega_H) d log(k_H / k_L)
```

partiendo de la función de pérdida **ya vinculada a la producción física** en los módulos anteriores y diferenciando los mapas fuente de capital agregado `K` y producción ajustada `G`.

La proposición se entiende sobre una trayectoria real `t -> (k_H(t),k_L(t))`, diferenciable en el instante considerado, con `k_i(t)>0`, masas `v_i>0`, productividades `A_i>0`, elasticidades comunes `alpha>0`, `0<beta<1` y `d=1-alpha-beta>0`. Las masas y las productividades no dependen del parámetro de trayectoria; no se presupone que el capital total sea fijo.

## 2. Definiciones de la tecnología original

```text
gamma = alpha/(1-beta)
c_i   = v_i A_i^(1/(1-beta))
g_i(t)= A_i^(1/(1-beta)) k_i(t)^gamma
K(t)  = v_H k_H(t) + v_L k_L(t)
G(t)  = c_H k_H(t)^gamma + c_L k_L(t)^gamma
ZA    = v_H A_H^(1/d) + v_L A_L^(1/d)
```

De las pruebas previas de productividad y empleo óptimo,

```text
Y(t)=L(t)^beta G(t)^(1-beta),
Yeff(t)=K(t)^alpha L(t)^beta ZA^d,
Loss(t)=alpha log K(t)+d log ZA-(1-beta)log G(t).
```

La última igualdad tiene que entenderse con empleo óptimo y dotaciones positivas. El empleo total `L(t)` puede variar: su contribución logarítmica se cancela, por lo que la pérdida condicional termina siendo función de los capitales y de la productividad fija.

## 3. Derivación de K(t) y G(t)

La linealidad produce la derivada real

```text
K'(t)=v_H k_H'(t)+v_L k_L'(t).
```

La derivada de la potencia real en argumentos positivos produce, sin imponer desde fuera la derivada de `G`,

```text
G'(t)=gamma [c_H k_H(t)^(gamma-1) k_H'(t)
             +c_L k_L(t)^(gamma-1) k_L'(t)].
```

Con las participaciones `kappa_H=v_H k_H/K` y `omega_H=c_H k_H^gamma/G`, las identidades fuente de presupuesto y la regla de la cadena implican

```text
(log K)' = kappa_H (log k_H)' + (1-kappa_H)(log k_L)'
(log G)' = gamma [omega_H(log k_H)' + (1-omega_H)(log k_L)'].
```

Las identidades requieren `k_i,K,G>0`; el paso de `k^(gamma-1)` a `k^gamma/k` no es válido sin controlar el punto `k=0`.

## 4. Resultado de la cadena

Diferenciar la identidad de producción/pérdida, con masas y `A_i` fijos, da

```text
Loss' = alpha (log K)' - (1-beta)(log G)'.
```

Sustituir las fórmulas de participaciones y `(1-beta)gamma=alpha` entrega

```text
Loss'(t)=alpha (kappa_H-omega_H)
          [k_H'(t)/k_H(t)-k_L'(t)/k_L(t)].
```

El lado derecho coincide con

```text
alpha (kappa_H-omega_H) (d/dt) log(k_H(t)/k_L(t)).
```

En consecuencia, el signo marginal es negativo si `alpha>0`, `omega_H>kappa_H` y `d log(k_H/k_L)>0`. Esta es una proposición **condicional sobre una trayectoria de capital**: no identifica qué shock monetario provoca ese movimiento ni su trayectoria de equilibrio.

## 5. Identificación de la cuota de producto

En el reparto óptimo de empleo

```text
ell_i(t)=L(t) g_i(t)/G(t),
Y_i(t)=A_i k_i(t)^alpha ell_i(t)^beta
      =(L(t)/G(t))^beta g_i(t).
```

De modo que

```text
(v_H Y_H)/(v_H Y_H+v_L Y_L)=v_H g_H/G=omega_H.
```

Esta es una **obligación semántica independiente**: la prueba diferencial utiliza la cuota `v_H g_H/G`; su identificación como cuota productiva debe apoyarse en la igualdad desde `Y_i` originales.

## 6. Módulos de formalización y compuertas

- `PaperSourceDifferentiationCandidate.lean`: cuatro declaraciones `HasDerivAt`, dos para `K,G` y dos para sus logaritmos.
- `PaperSourceDifferentialSharesCandidate.lean`: dos identidades que relacionan las derivadas calculadas con `kappa_H,omega_H` construidos de las funciones fuente.
- `PaperSourceLossChainRuleCandidate.lean`: una declaración compuesta de `HasDerivAt Loss`, para cualquier trayectoria diferenciable positiva, conectada a la igualdad de coeficientes ya verificada.
- `PaperSourceOutputShareCandidate.lean`: una declaración que identifica `omega_H` con la cuota original de producción en empleo óptimo.

El workflow `.github/workflows/lean-focused-paper-claims.yml` copia los módulos en la versión fijada de Lean/Mathlib, compila y ejecuta `#print axioms`. No promover un teorema nuevo a `kernel_verified` hasta que el run exacto termine en verde **y** no muestre `sorryAx`. Si falla CI, corregir en un nuevo commit y conservar la trazabilidad.

## 7. Exclusiones del resultado

Este lema no demuestra por sí solo: (i) la existencia de equilibrio competitivo estocástico del sistema completo de 34 ecuaciones; (ii) la selección de una rama S/B después de un shock de encaje o remuneración de reservas; (iii) la identificación causal de una IRF; (iv) un efecto positivo de crecimiento sostenido. La prueba de mecanismo productivo es necesaria, pero no suficiente, para esas proposiciones.

## 8. Verificación final de esta campaña diferencial

La CI focalizada [#42504364485](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42504364485), commit `eaa08a328974c9462e8b5cdaa85a33f0dd88546b`, mostró:

```text
COMPILED PaperSourceLossChainRuleCandidate
COMPILED PaperSourceOutputShareCandidate
COMPILED PaperSourceLogCapitalRatioCandidate
PASS focused Lean kernel and axiom audit
```

Los tres `#print axioms` fueron aceptados sin `sorryAx`. La identidad diferencial fuente, la correspondencia con cuota de producción física y la derivada de `log(kH/kL)` están **DEMOSTRADAS** bajo las hipótesis exactas de los archivos Lean. No declarar equivalencia literal plena con los 57 resultados hasta cotejar y corregir los predicados del checkpoint; en especial, una prueba estática de reasignación no proporciona una IRF de política monetaria ni crecimiento de largo plazo.
