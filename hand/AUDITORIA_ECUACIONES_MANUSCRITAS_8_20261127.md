# Auditoría de los ocho resultados manuscritos del artículo compacto

**Objeto cotejado:** `hand/ai-ieproject.pdf`, 12 páginas, PDF Annotator.  
**Integridad del original:** SHA-256 `14b081edf35c52882bd433021980a8beb12cdf805733aa4b4bca5839d9fcb8a1`; Git blob `7cc7b4378dabda89fd28eb623fa6c034c47a6ef4`; 3,363,589 bytes.  
**Manuscrito original, sin recomprimir ni sustituir:** [abrir PDF](ai-ieproject.pdf).  
**Artículos fuente cotejados:** `paper/paper.tex` (Prop. 3.1), `paper/appendix_eight_results.tex` (A.1.1–A.1.4), `paper/body_compact_after.tex` (5.1–5.3).  
**Tipo de auditoría:** inspección visual de las 12 páginas y contraste de ecuaciones, hipótesis, signos y alcance con los ocho enunciados del artículo. No equivale a formalización completa de todos ellos en Lean.

## Veredictos por resultado

| Resultado del PDF compacto | Páginas originales | Cotejo del razonamiento manuscrito | Obligación externa y alcance |
|---|---:|---|---|
| Prop. 3.1, dos soluciones locales escalares | 1–3 | **COHERENTE BAJO HIPÓTESIS**: \(M_s(0,0)=b<0\), \(M_h(0,0)=a_R<0\). El signo de \(M(0,h)\) para \(h<0\), la rama de frontera \(s=0\), el IFT \(s'(0)=-a_R/b<0\) y la monotonía que excluye una tercera raíz local coinciden con el paper. | **PENDIENTE** demostrar desde el modelo económico que la reducción escalar real es \(C^1\), cumple los signos y permite recuperar el resto de las 33 variables. No implica dos equilibrios infinitos. |
| Lema A.1.1, repago robusto | 3–4 | **COHERENTE BAJO HIPÓTESIS**: de \(R^Lb/\Pi'\le\theta_i(1-\delta)q'k'\) se deduce \(N'\ge \pi^{op}{}'+(1-\theta_i)(1-\delta)q'k'+R^Da/\Pi'\ge0\); si \(k'>0\) o \(a>0\), la cota es estricta. | No implica solvencia bancaria agregada ni condiciones de recursos/consumo adicionales. |
| Lema A.1.2, ahorro y endeudamiento no simultáneos | 4–5 | **COHERENTE BAJO HIPÓTESIS**: resta de las dos FOC interiores; el término \(\beta_E E[V'_N(R^L-R^D)/\Pi']\) es estrictamente positivo y \(\mu R^L\ge0\), contradiciendo cero. | La conclusión es de incompatibilidad de posiciones interiores bajo las FOC necesarias; no acredita por sí sola existencia/suficiencia global de un óptimo. |
| Prop. A.1.3, capital máximo financiable | 5 | **COHERENTE BAJO HIPÓTESIS**: del presupuesto y el límite de garantía obtiene \((q-H/R^L)k'\le n\), máximo alcanzable y derivada \(-nH/[(R^L)^2(q-H/R^L)^2]<0\) manteniendo \(n,q,H\) fijos. | Capacidad financiable parcial, no capital óptimo de equilibrio. |
| Lema A.1.4, pérdida por mala asignación | 6–8 | **COHERENTE BAJO HIPÓTESIS**: distribuye empleo \(\ell_i=Lg_i/G\), construye \(K_i^*,\ell_i^*\) con \(Z_A\), obtiene \(Y=L^\beta G^{1-\beta}\), \(Y^{eff}=K^\alpha L^\beta Z_A^d\) y \(d\mathscr L=\alpha(\kappa_H-\omega_H)d\log(k_H/k_L)\). La comparación \(\omega_H>\kappa_H\iff MPK_H>MPK_L\) coincide con el paper. | Las hipótesis \(d=1-\alpha-\beta>0\), masas y parámetros fijos y empleo óptimamente distribuido son esenciales. No inferir \(MPK_H>MPK_L\) solo de \(A_H>A_L\). |
| Prop. 5.1, decaimiento matricial | 9 | **ARGUMENTO ANALÍTICO VÁLIDO CON PREMISAS NUMÉRICAS**: \(k=48m+r\), \(F_0^k=(F_0^{48})^m F_0^r\), submultiplicatividad e iteración de las normas \((24/25),(61/10)\). | La hoja **no contiene** los 36 coeficientes de \(F_0\) ni las operaciones racionales que prueban las dos cotas estrictas; se verificaron con `code/irf/exact_linear_tail_power_certificate.py` y se encuentran también probadas en Lean mediante `prop51_unconditional_exact`, para esa matriz decimal exacta y no para el Jacobiano SOURCE. |
| Lema 5.2, robustez matricial | 10–11 | **ARGUMENTO ANALÍTICO VÁLIDO CON PREMISAS NUMÉRICAS**: identidad telescópica no conmutativa \(A^n-F_0^n=\sum_{j=0}^{n-1}F_0^{n-1-j}(A-F_0)A^j\), mayorante recursivo \(a_n\), descomposición \(k=48m+r\). | Las verificaciones \(a_{48}<49/50\) y \(\max_{r<48}a_r<7\) **no se calculan explícitamente en las hojas**; fueron reejecutadas mediante certificado racional reproducible y están además probadas en Lean mediante `lemma52_decimal_current_exact`, para toda matriz 6×6 de la clase definida; esto no prueba estabilidad del equilibrio infinito. |
| Prop. 5.3, cuña de precios efectivos | 11–12 | **COHERENTE BAJO HIPÓTESIS**: con garantía vinculante \(p_i^{eff}=q-\theta_iJ/R^L\), luego \(W=(\theta_L-\theta_H)J/R^L>0\). La derivada parcial manuscrita \(\partial W/\partial R^L=-(\theta_L-\theta_H)J/(R^L)^2<0\) es correcta **manteniendo \(J\) fijo**. | Si \(J\) varía endógenamente, la derivada total cambia; el resultado no prueba una respuesta causal o de bienestar. |

## Verificación global y hallazgos

- **8/8 resultados:** se pudieron identificar y cotejar visualmente con las definiciones y demostraciones del artículo compacto. La numeración manuscrita concuerda con 3.1, A.1.1–A.1.4, 5.1–5.3.
- **6/8:** la secuencia manuscrita contiene un argumento algebraico, de condiciones de primer orden o de función implícita que coincide con la demostración del artículo **bajo sus hipótesis expresas**. Esto incluye la Proposición 3.1 como *teorema condicional escalar*, no como existencia macroeconómica global.
- **2/8 (5.1 y 5.2):** sus deducciones a partir de cotas son correctas, pero las cotas numéricas estrictas no son demostradas por las páginas manuscritas en sí. El certificado racional es un archivo y una ejecución **separados**.
- **8/8 con auditoría de coherencia manuscrito–paper realizada.** Esta revisión manuscrita no genera por sí misma teoremas Lean. Ya existen certificados en el kernel para la Proposición 5.1 y el Lema 5.2 en la matriz decimal real 6×6, y para la conclusión escalar condicional de la Proposición 3.1. Falta la correspondencia integral de todos los ocho resultados con SOURCE económico; véase `paper/lean_formalization_matrix_8.md`.
- El manuscrito conserva anotaciones correctivas en rojo que restringen explícitamente el alcance de la Proposición 3.1 a dos **raíces escalares locales**.
- El objetivo de transcripción/aprobación oral **no** permite afirmar que las 33 ecuaciones del sistema SOURCE, su Jacobiano y un equilibrio infinito estén certificados.
- **No es necesario rehacer las notas a mano** para la cobertura documental. Para un dictamen formal completo, se deben verificar los insumos racionales y las pruebas Lean correspondientes al enunciado exacto.

## Compuertas técnicas y de custodia

El workflow `.github/workflows/ie-handnotes-math-audit.yml` verifica:
1. tamaño, SHA-256 y Git blob exactos del PDF conservado en `hand/ai-ieproject.pdf`;
2. recálculo independiente, con `fractions.Fraction`, de las cotas del grafo decimal de potencia \(48\), sus mayorantes y sus insumos hash;
3. los ocho resultados declarados, fuentes LaTeX, hipótesis financieras, aleatorizaciones reproducibles y alineamiento básico del paper, mediante `code/verify_compact_paper.py`.

El script reproduce resultados sobre los objetos que define y **no prueba** que el Jacobiano económico de 33×33 tenga la misma transición 6×6, ni que el modelo dinámico completo sea un equilibrio competitivo infinito.

**Cronología:** documento manuscrito recibido y archivado **después** de las 22:00 (Lima, 26/11/2026); la incorporación al repositorio es una adenda posterior al cierre inicial, no una corrección retroactiva del sello de entrega.


## Certificación racional reejecutada después del cotejo

GitHub Actions [ejecución 45933840987](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45933840987), resultado `success`, ejecutó `code/irf/exact_linear_tail_power_certificate.py` y `code/verify_compact_paper.py`:

- SHA-256 de la matriz fuente decimal fija: `d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94`.
- Cota superior dirigida para \(\|F_0^{48}\|_\infty\): `0.955246892194` (estrictamente menor que \(24/25=0.96\)).
- Máximo dirigido de \(\|F_0^r\|_\infty\), \(0\le r<48\): `6.097821698407` (estrictamente menor que \(61/10=6.1\)).
- Mayorante robusto de 48 pasos: `0.972103438403` (estrictamente menor que \(49/50=0.98\)).
- Pico transitorio en potencia 7.
- Verificación de ocho resultados reportada como `passed_eight_result_scoped_checks_not_a_lean_proof`.

**Clasificación:** prueba de la implicación algebraica desde las cotas en manuscritos y prueba **numérica exacta** de esas cotas en el objeto racional definido por el script. Estas verificaciones **no** certifican la igualdad entre esa matriz y el Jacobiano dinámico SOURCE ni la formalización Lean de los ocho resultados.


## Reconciliación con pruebas Lean preexistentes

El cotejo manuscrito es distinto de la certificación del kernel. Los siguientes resultados matemáticos ya estaban demostrados en sus objetos y dominios precisos:

- **Prop. 3.1:** `CurrentCompactProp31C1Bridge.lean`, `prop31_scalar_from_only_C1_hypotheses`: dos raíces complementarias locales para un mapa escalar abstracto \(M\) bajo \(C^1\) y signos. [Actions #45874767483](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45874767483). Pendiente identificar ese mapa con la reducción del SOURCE económico.
- **Prop. 5.1:** `CurrentCompactBlock48Tail.lean`, `prop51_unconditional_exact`: 36 entradas decimales literales de \(F_0\), normas reales inducidas, potencias de todo horizonte. [Actions #45865176408](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45865176408).
- **Lema 5.2:** `CurrentCompactRobustFiniteCertificate.lean`, `lemma52_decimal_current_exact`: las tres cláusulas del lema para toda matriz real 6×6 dentro de la bola de radio \(10^{-4}\) respecto de \(F_0\). [Actions #45871289804](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45871289804).

Según sus controles especializados, sus teoremas fueron auditados con `#print axioms` sin `sorryAx`. Esto **no prueba** que \(F_0\) sea la derivada económica del sistema SOURCE completo, ni que los otros cinco resultados tengan una equivalencia literal paper–Lean íntegra. No presentar ocho manuscritos como ocho teoremas nuevos en Lean.
