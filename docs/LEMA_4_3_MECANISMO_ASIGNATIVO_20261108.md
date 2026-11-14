# Lema 4.3 — pérdida asignativa y producto marginal del capital

**Propósito:** reconstruir las dos identidades del paper, diferenciar
resultados matemáticos de resultados numéricos y registrar exactamente qué
puede certificar Lean. Es una auditoría de la **pérdida de producto
condicional**, no una afirmación sobre utilidad o crecimiento permanente.

**Fuente interna:** `paper/paper.tex`, Lema
`lem:allocation_loss_identity` y ecuación
`eq:loss_relative_capital_derivative`.
**Prueba auxiliar verificada:** `PaperAllocationLossElasticityCandidate.lean`
compiló y pasó `#print axioms` sin `sorryAx` en
[Lean focalizado 42458449121](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42458449121),
commit `1e797f886dea03a6fdea135338e6408a3e8ab91b`.
No se ha probado el Lema 4.3 integral.

## 1. Problema que se maximiza

Hay dos tipos `i∈{H,L}`, con masas `v_i>0`,
capital individual `k_i>0`, trabajo individual `ell_i>0`,
y tecnología

    y_i = A_i k_i^alpha ell_i^beta,
    A_i>0, alpha>0, beta>0, d=1-alpha-beta>0.

Los agregados ponderados por masas son

    K = sum_i v_i k_i >0,
    L = sum_i v_i ell_i >0,
    Y = sum_i v_i y_i.

En esta primera etapa se fija el capital por tipo y se permite
redistribuir **solo trabajo** manteniendo `L` constante.
Para una solución interior, el producto marginal de trabajo es común:

    beta A_i k_i^alpha ell_i^(beta-1) = lambda.

Despejando y usando `sum_i v_i ell_i = L`, se obtiene

    gamma = alpha/(1-beta),
    g_i = A_i^(1/(1-beta)) k_i^gamma,
    G = sum_i v_i g_i,
    ell_i = L*g_i/G.

Como `beta<1`, el objetivo es estrictamente cóncavo en cada trabajo
individual y el resultado interior es el máximo condicional.
Al sustituir la asignación anterior,

    Y = L^beta G^(1-beta).

El empleo total `L` puede variar entre fechas: su contribución se
cancelará en el cociente de pérdidas.

## 2. Referente eficiente con capital y trabajo reasignables

Si se permite también la distribución del capital a `K`
agregado dado, los productos marginales de ambos factores se igualan.
Defínase

    Z_A = sum_i v_i A_i^(1/d),   d=1-alpha-beta.

Una asignación óptima es

    k_i* = K A_i^(1/d)/Z_A,
    ell_i* = L A_i^(1/d)/Z_A.

La concavidad de `A_i k_i^alpha ell_i^beta` para
`alpha+beta<1` y el soporte de primer orden en la
asignación interior prueban que ninguna alternativa factible
produce más. Por tanto

    Yeff = K^alpha L^beta Z_A^d.

La pérdida condicional de producto se define como

    Loss = log(Yeff/Y)
         = alpha log K + d log Z_A - (1-beta) log G ≥ 0.

La desigualdad final requiere **demostrar la optimalidad** del
referente eficiente y la factibilidad de la asignación observada;
no se puede deducir solo de escribir las potencias.

## 3. Diferencial exacto de la pérdida para cualquier variación suave

Con masas, productividad y elasticidades fijas:

    kappa_H = v_H k_H/K,
    omega_H = v_H y_H/Y = v_H g_H/G.

Las participaciones de L son `1-kappa_H` y
`1-omega_H`. La regla de la cadena produce

    d log K = kappa_H d log k_H
                +(1-kappa_H) d log k_L,
    d log G = gamma omega_H d log k_H
                +gamma(1-omega_H) d log k_L.

Dado que `(1-beta)*gamma = alpha`, la variación de
`d log Z_A` es cero cuando las productividades son fijas:

    d Loss
      = alpha d log K - (1-beta) d log G
      = alpha (kappa_H-omega_H)
              (d log k_H - d log k_L)
      = alpha (kappa_H-omega_H) d log(k_H/k_L).

El paso de `d log` a `d` es diferencial sobre una trayectoria
diferenciable **en un punto con capitales estrictamente positivos**.
No exige fijar `K`, `L` o los capitales propios individualmente;
sí exige que en cada punto se conserve la asignación óptima de trabajo
y las primitivas del referente no cambien.

Una variación del tamaño agregado de capital común a ambos tipos
deja `d log(k_H/k_L)=0`, por tanto no modifica este índice de
**mala asignación relativa** en el margen.

## 4. Cuándo mover capital hacia H mejora la asignación

Con elasticidad de capital `alpha>0` común, el producto marginal
físico de capital del tipo i es

    MPK_i = alpha y_i/k_i.

Si los dos capitales y niveles de producto son positivos:

    omega_H > kappa_H
       <=> y_H/k_H > y_L/k_L
       <=> MPK_H > MPK_L.

El primer paso compara las participaciones normalizadas: al
multiplicar por los agregados positivos se cancelan las masas.
Por tanto:

    omega_H > kappa_H y d log(k_H/k_L)>0
          => d Loss <0.

La condición **no** se deduce de `A_H>A_L` a secas.
Capital instalado, trabajo, precios y riqueza endógena
determinan los productos marginales. Además, aumentar
crédito a H no equivale a aumentar el cociente de capital:
la restricción activa puede absorber recursos endógenos.

## 5. Correspondencia de pruebas con el modelo fuente

| Objeto | Estado real |
|---|---|
| `allocationLossIdentitySpec` en `PaperInterface.lean` | Especificación formal del referente y `Loss≥0`, pero **no contiene la derivada ni la comparación de MPK** |
| `allocation_loss_log_differential_algebra` | **DEMOSTRADO en Lean**, como álgebra de coeficientes si los pesos de `d log K` y `d log G` ya se han obtenido |
| `output_share_gt_capital_share_iff_productivity` | **DEMOSTRADO en Lean** para masas y niveles positivos: equivalencia exacta de participaciones y cocientes `y_i/k_i` |
| `loss_direction_negative_of_reallocation` | **DEMOSTRADO en Lean**: signo negativo dado `alpha>0`, `omega_H>kappa_H` y desplazamiento relativo positivo |
| `lem:allocation_loss_identity` entero | **PENDIENTE**: recuperar la fórmula laboral desde FOC, optimalidad global del referente, desigualdad `Loss≥0` y derivadas de agregadores Cobb–Douglas como tales |

La corrida verde de estos tres teoremas **no** convierte toda la
especificación económica o el Lema 4.3 del paper en demostrados
por Lean; solo verifica los fragmentos matemáticos especificados.
La comparación de las cifras impresas en la tabla de derivadas
entrega `dLoss/dLogRatio = -0.0115529615840` en S y
`-0.0115529612567` en B, una discrepancia relativa
aproximada de `2.83e-8` debida al redondeo reportado.
Este último cotejo lo reproduce `code/audit_allocation_loss_table.py`;
no reestima parámetros ni ejecuta de nuevo el solucionador dinámico.

## 6. Aplicación a las ramas S y B

El producto marginal favorece a H cuando `omega_H>kappa_H`.
Con esta condición local y las dos ramas numéricas del paper,
un aumento de `log(k_H/k_L)` en S baja la pérdida,
mientras una disminución en B la eleva. Ambas respuestas se
obtienen con un mismo shock inicial de remuneración de reservas,
pero son resultados de una solución conjunta del sistema reducido,
no de un contraste causal que mantenga todos los precios fijos.

No está demostrado que cada raíz reducida sea equilibrio competitivo
infinito, que el encaje tenga el mismo efecto, ni que la
descomposición pruebe una diferencia en crecimiento de largo plazo.
