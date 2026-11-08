# Prueba global de eficiencia en el Lema 4.3: puente AM–GM y obligaciones Lean

**Estado:** el argumento matemático analítico de esta nota es
**demostración condicional** bajo sus hipótesis. La implementación
`PaperAllocationEfficiencySupportCandidate.lean` es **candidata**
hasta que el kernel y la auditoría de axiomas terminen satisfactoriamente.
El mapeo de variables normalizadas al `allocationLossIdentitySpec`
del checkpoint aún no está completamente formalizado.

## 1. Objeto económico y agregados

Sea `i ∈ {H,L}`, `v_i>0`, `A_i>0`, `k_i>0`,
`ell_i>0` y exponente Cobb–Douglas común `a>0`, `b>0`,
`d=1-a-b>0`. La producción y los agregados son

```text
y_i = A_i * k_i^a * ell_i^b,       Y = sum_i v_i y_i,
K = sum_i v_i k_i,                L = sum_i v_i ell_i,
z_i = A_i^(1/d) > 0,              Z = sum_i v_i z_i > 0.
```

La referencia que asigna ambos factores proporcionalmente a la
productividad ajustada es

```text
k_i*   = K*z_i/Z,
ell_i* = L*z_i/Z.
```

Ambas restricciones de recursos se satisfacen:

```text
sum_i v_i k_i* = K,     sum_i v_i ell_i* = L.
```

Un nuevo teorema Lean
`efficient_candidate_clears_resources` prueba la igualdad
algebraica por separado, sin suponer óptimo bancario.

## 2. Normalización que permite demostrar suficiencia global

Definir participaciones de masa-productividad y cantidades relativas:

```text
w_i = v_i*z_i > 0,
x_i = k_i/k_i* = k_i*Z/(K*z_i) > 0,
t_i = ell_i/ell_i* = ell_i*Z/(L*z_i) > 0.
```

Por los balances de factores,

```text
sum_i w_i*x_i = Z,         sum_i w_i*t_i = Z,
sum_i w_i = Z.
```

La identidad de potencia `d+a+b=1` da, para cada tipo,

```text
v_i*y_i
  = v_i*A_i*k_i^a*ell_i^b
  = (K^a * L^b / Z^(a+b)) * w_i*x_i^a*t_i^b.
```

Las igualdades anteriores se consideran **obligaciones de puente**
entre la fuente Cobb–Douglas y las coordenadas normalizadas;
no están todavía presentes como teorema kernel-checked.

## 3. Desigualdad global (no solo FOC)

Para cada tipo, la desigualdad media geométrica–aritmética
ponderada de **tres** factores, con pesos `a,b,d ≥ 0` y
`a+b+d=1`, implica

```text
x_i^a * t_i^b * 1^d ≤ a*x_i + b*t_i + d.
```

Multiplicar por `w_i ≥ 0` y sumar da

```text
sum_i w_i*x_i^a*t_i^b
  ≤ a*sum_i w_i*x_i + b*sum_i w_i*t_i + d*sum_i w_i
  = (a+b+d)*Z = Z.
```

Así, una vez demostrados los puentes de normalización,

```text
Y ≤ (K^a*L^b/Z^(a+b))*Z
  = K^a*L^b*Z^d
  = Yeff.
```

La candidata eficiente usa `x_i=t_i=1` y por tanto
**alcanza la cota** con igualdad, no solamente satisface
las Euler interiores. La prueba vale también frente a
alternativas no negativas de frontera (con las convenciones de
`Real.rpow`) siempre que los exponente sean no negativos.

El módulo propuesto implementa exactamente la desigualdad
de la suma normalizada bajo las restricciones de agregados
en el teorema `normalized_two_type_output_le_benchmark`;
`normalized_benchmark_attained` verifica la igualdad
en `x_H=x_L=t_H=t_L=1`.

## 4. Pérdida de producto condicional

Si el producto es positivo, el logaritmo es creciente:

```text
0 < Y ≤ Yeff
=> log Y ≤ log Yeff
=> Loss = log Yeff - log Y ≥ 0.
```

En variables normalizadas el módulo Lean propone
`normalized_log_loss_nonneg`, que es la desigualdad
`log Z - log(sum_i w_i*x_i^a*t_i^b) ≥ 0`.
El término de escala común de `Y` y `Yeff`
se cancela; esta cancelación y la igualdad de las
expresiones de producción aún precisan un puente
de potencias y logaritmos en Lean.

**Advertencia interpretativa:** `Loss≥0` mide
**ineficiencia asignativa condicional en producto**.
No demuestra pérdida de bienestar, causalidad de
instrumentos monetarios, persistencia ergódica,
crecimiento sostenido ni equilibrio competitivo pleno.

## 5. Matriz de cierre de esta proposición

| Paso | Matemática escrita | Estado Lean |
|---|---|---|
| Pesos positivos y `a+b+d=1` | Hipótesis explícitas | Hipótesis explícitas |
| Cota global normalizada AM–GM | Sí | Candidato `normalized_two_type_output_le_benchmark` |
| Cota alcanzada en `x_i=t_i=1` | Sí | Candidato `normalized_benchmark_attained` |
| No negatividad de la pérdida normalizada | Sí | Candidato `normalized_log_loss_nonneg` |
| Recursos de la asignación propuesta | Sí | Candidato `efficient_candidate_clears_resources` |
| Puente de potencias `A_i=z_i^d` y producción `Y` | Sí | **PENDIENTE** |
| Derivación del reparto óptimo de trabajo y `G` | Sí, en paper | **PENDIENTE** |
| Prueba literal del `allocationLossIdentitySpec` | Implícita analíticamente | **PENDIENTE** |
| Derivada `dLoss/d log(kH/kL)` desde las funciones originales | Sí, en paper | **PENDIENTE**; álgebra de coeficientes auxiliar ya verificada |
