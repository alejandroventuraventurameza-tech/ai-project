# IE project — Lema 4.3: cotejo semántico y teorema integrador de fuente

**Fecha:** 8 de noviembre de 2026.  
**Rama:** `work/lean-ci-validation-otc-20261106`.  
**Objeto de verificación:** `paper/paper.tex`, `lem:allocation_loss_identity` y la antigua interfaz `allocationLossIdentitySpec`.

> **Estado verificado:** los dos teoremas integradores y el predicado fuente unificado de once afirmaciones pasaron compilación y `#print axioms` sin `sorryAx` en CI #42505059048, #42505126404 y #42505264161. **40 declaraciones formales relacionadas con 4.3** (37 previas, tres integradoras). No se presume equivalencia con el checkpoint original ni equilibrio dinámico.

## 1. Las siete cláusulas estáticas del teorema candidato

Con masas `v_H,v_L>0`, tecnologías `Y_i=A_i k_i^alpha ell_i^beta`, `A_i,k_i>0`,
`L>0`, `alpha,beta>0`, `d>0` y `alpha+beta+d=1`, se define

```text
g_i = A_i^(1/(1-beta)) k_i^(alpha/(1-beta))
G   = v_H g_H+v_L g_L
K   = v_H k_H+v_L k_L
ZA  = v_H A_H^(1/d)+v_L A_L^(1/d)
ell_i*= L g_i/G
Y    = sum_i v_i A_i k_i^alpha (ell_i*)^beta
Yeff = K^alpha L^beta ZA^d.
```

Las conclusiones que deben aparecer **simultáneamente** bajo las mismas hipótesis son:

1. `ell_i*>0` y presupuesto físico `sum_i v_i ell_i*=L`.
2. La identidad de producción derivada de fuentes: `Y=L^beta G^(1-beta)`.
3. Para toda asignación física no negativa de `k_i,ell_i` con presupuestos agregados `K,L`, la producción original no excede `Yeff`. El cuantificador incluye esquinas.
4. El par eficiente `k_i^*=K A_i^(1/d)/ZA,` `ell_i^*=L A_i^(1/d)/ZA` alcanza `Yeff` evaluado en las **tecnologías originales**.
5. La pérdida `log Yeff-log Y` es no negativa.
6. Esa pérdida coincide exactamente con `alpha log K+d log ZA-(1-beta)log G`.
7. Con el capital original fijo, ninguna asignación de trabajo no negativa con suma ponderada `L` supera la producción con `ell_i^*`.

Las siete conclusiones se componen en `PaperLemma43StaticIntegratedCandidate.lean`; no son definiciones redundantes de `Y` o `Yeff`.

## 2. Las cuatro cláusulas diferenciables integradas

Sea `t -> (k_H(t),k_L(t))` una trayectoria diferenciable con `k_i(t)>0` al evaluar el resultado. Las masas, productividades y exponentes permanecen constantes. Tomamos `L>0` al evaluar las cuotas físicas y `gamma=alpha/(1-beta)`.

Las conclusiones de `PaperLemma43DynamicIntegratedCandidate.lean` son:

1. `HasDerivAt` de la pérdida fuente `Loss(t)=alpha log K(t)+d log ZA-(1-beta)log G(t)`, con derivada `alpha(kappaH-omegaH)(kH'(t)/kH(t)-kL'(t)/kL(t))`.
2. `HasDerivAt` de `log(kH(t)/kL(t))` con derivada exactamente `kH'/kH-kL'/kL`.
3. Identidad `omegaH = v_H Y_H/Y` con **producto físico** evaluado al empleo óptimo.
4. Equivalencia `omegaH>kappaH` si y solo si `alpha (Y_H/k_H)>alpha (Y_L/k_L)`, que coincide con el producto marginal físico del capital Cobb–Douglas cuando `alpha>0`.

No se supone constante el capital agregado: puede variar a lo largo de la trayectoria. El término de empleo agregado se cancela en la pérdida **condicional**, pero el teorema no establece el mecanismo que genera la trayectoria.

## 3. Defecto semántico documentado en la interfaz antigua

El antiguo `allocationLossIdentitySpec` cuantifica `v,A,k,labor,alpha,beta : FirmType -> ℝ`, pero:

- Solo impone `alpha H>0` y `beta H>0`; utiliza las elasticidades **de H** al definir `G,Y,Yeff`, sin cuantificar explícitamente su igualdad con las de L.
- Declara `Y := L^beta G^(1-beta)` y `Yeff := K^alpha L^beta ZA^d`; las dos igualdades correspondientes son definicionales. **No demuestra, por esa sola definición, que Y se obtenga sumando las producciones físicas originales.**
- La conclusión exige únicamente las dos igualdades anteriores y `0<=loss`; no incluye ni la optimalidad global de empleo, ni la cota global de asignación conjunta, ni la derivada de `Loss`, ni la equivalencia de productos marginales.
- Por ello, incluso una prueba del **tipo literal** `allocationLossIdentitySpec` no sería una prueba de equivalencia con todo el Lema 4.3 de `paper/paper.tex`.

La reparación correcta consiste en **añadir una interfaz candidata de fuente** y probarla, documentar la correspondencia exacta con el manuscrito y el checkpoint, y cambiar los estados del ledger solo después de una auditoría semántica. No sobrescribir silenciosamente el predicado original del checkpoint.

## 4. Regla de evidencia y próxima obligación

Las pruebas auxiliares anteriores son `kernel_checked` en sus corridas históricas fijadas. Los integradores nuevos **NO** incrementan el contador hasta recibir CI focalizada verde, revisar `#print axioms` y vincular SHA exacto. Una CI editorial verde no sustituye la validación Lean.

Una vez cerrada esta interfaz, quedarán fuera del alcance del lema estático: definición de equilibrio monetario estocástico con horizonte infinito, continuidad, KKT financieros, raíces de ramas S/B, respuesta causal a instrumentos del banco central, IRF reproducibles, y demostración de crecimiento persistente. Ninguna de esas afirmaciones debe inferirse del teorema de eficiencia.

## 5. Auditoria verde de la especificacion nueva

- `PaperLemma43StaticIntegratedCandidate.lean`: [run #42505059048](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505059048), commit `0cb2bb636836e67d54f4f02819756a49662529c5`.
- `PaperLemma43DynamicIntegratedCandidate.lean`: [run #42505126404](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505126404), commit `5f40787041c96d96b980e87e72fb9cf5b181501a`.
- `PaperLemma43SourceCompleteCandidate.lean`: [run #42505264161](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505264161), commit `b132b91df59eb3e64b6aefb77621bd62084c8054`.

Las tres corridas verificaron los teoremas citados en el kernel, sin `sorryAx`. Una nueva interfaz de fuente no subsana por identidad nominal la brecha del `allocationLossIdentitySpec` del checkpoint, ni implica optimalidad bancaria intertemporal.
