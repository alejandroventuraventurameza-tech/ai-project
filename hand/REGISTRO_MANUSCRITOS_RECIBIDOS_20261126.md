# Manuscritos auténticos recibidos — IE project

**Fuente original:** `ai-ieproject.pdf` (PDF Annotator; 12 páginas A4 horizontales, escaneadas).  
**Copia preservada en Drive (privada):** https://drive.google.com/file/d/1fq4tjuBwCBGerDX6sNwDeCPP89VuaXWv/view?usp=drivesdk  
**SHA-256 del PDF original:** `14b081edf35c52882bd433021980a8beb12cdf805733aa4b4bca5839d9fcb8a1`  
**Tamaño:** 3,363,589 bytes. **Páginas:** 12.  
**Recepción:** tras el cierre inicial del repositorio del 26/11/2026; la subida a Drive quedó registrada a las 03:07:17 UTC del 27/11 (22:07:17, Lima, 26/11). **No describir como recibido antes de las 22:00.**

**Estatus de custodia:** PDF auténtico manuscrito recibido en la conversación y preservado en Drive. **No está incorporado como archivo binario dentro de `main`**; este índice conserva referencia, hash, paginación y tabla de cotejo. La URL de Drive es privada y requiere permisos de acceso del propietario. No presentar el enlace privado como descarga pública válida para evaluadores.

## Concordancia con los ocho resultados del artículo compacto

| Etiqueta LaTeX | Número en PDF compacto | Rótulo manuscrito/histórico | Páginas del PDF manuscrito | Verificación de presencia | Validación matemática |
|---|---|---|---:|---|---|
| `prop:local_macro_multiplicity` | Prop. 3.1 | Prop. 3.1 / «dos soluciones locales»; en guías históricas Prop. 4.2 | 1–3 | Presente: hipótesis, monotonicidad y solución frontera/interior | Por cotejar rigurosamente |
| `lem:repayment` | Lema A.1.1 | Lema A.1.1 (garantía robusta) | 3–4 | Presente: restricción de repago por estado | Por cotejar rigurosamente |
| `lem:v0m_original_6_2` | Lema A.1.2 | Lema A.1.2 (no ahorro y deuda simultáneos) | 4–5 | Presente: condición de primer orden y argumento de signo | Por cotejar rigurosamente |
| `prop:v0m_original_6_3` | Prop. A.1.3 | Prop. A.1.3 (capacidad financiable) | 5 | Presente: límite k y derivada respecto de R^L | Por cotejar rigurosamente |
| `lem:allocation_loss_identity` | Lema A.1.4 | Lema A.1.4 (pérdida de asignación) | 6–8 | Presente: referente eficiente, pérdida y diferenciales | Por cotejar rigurosamente |
| `prop:compact_exact_tail_power` | Prop. 5.1 | Prop. 5.1 (decaimiento por bloques) | 9 | Presente: división euclidiana 48m+r y cota | Verificar fuente racional para las constantes |
| `lem:compact_robust_tail_power` | Lema 5.2 | Lema 5.2 (robustez) | 10–11 | Presente: identidad telescópica y mayorante matricial | Verificar fuente racional para las constantes |
| `prop:compact_source_collateral_effective_wedge` | Prop. 5.3 | Prop. 5.3 (cuña financiera) | 11–12 | Presente: capital financiable, costos efectivos y derivada de cuña | Por cotejar rigurosamente |

**Resultado del control documental:** **8/8 resultados con material manuscrito recibido; 0/8 calificados aquí como demostraciones matemáticamente auditadas.** La cobertura documental no equivale a la aceptación formal de cada prueba.

## Observaciones de auditoría para el cotejo

- **Prop. 3.1 (p. 1–3):** la prueba distingue la raíz de frontera y la interior; el signo de \(s(h)\) para \(h<0\) se obtiene con derivada negativa. Verificar que las hipótesis \(\partial_s\mathcal{M}<0\), \(\partial_h\mathcal{M}<0\) y la complementariedad tienen el alcance local enunciado. No inferir dos equilibrios macroeconómicos globales.
- **A.1.1 (p. 3–4):** documenta la suficiencia de la garantía robusta para cobertura del repago por estado. No inferir automáticamente solvencia bancaria agregada.
- **A.1.2 (p. 4–5):** argumento con condiciones de primer orden que excluye ahorro y deuda simultáneos cuando los parámetros de tasas satisfacen la desigualdad exigida. No confundir condición necesaria con suficiencia global.
- **A.1.3 (p. 5):** fórmula \(k^{\max}=n/(q-H/R^L)\) y derivada negativa respecto de \(R^L\) bajo dominio positivo. Es capacidad financiable, no capital óptimo general.
- **A.1.4 (p. 6–8):** asignación eficiente condicional a recursos, identidades de pérdida y diferenciales. Diferenciar productividad marginal parcial de variación con empleo endógeno; comprobar los pesos y signos.
- **5.1 (p. 9):** manuscrito usa los valores \(24/25\), \(61/10\) y una descomposición en bloques de 48; las desigualdades matriciales numéricas necesitan la auditoría exacta independiente.
- **5.2 (p. 10–11):** manuscrito incluye expansión telescópica no conmutativa y cota \(7(49/50)^{\lfloor k/48\rfloor}\). Verificar recursión y certificado racional. No interpretar la matriz congelada como equilibrio dinámico general.
- **5.3 (p. 11–12):** cuña de costos \(W=(\theta_L-\theta_H)J/R^L\) y derivada parcial negativa en tasa a \(J\) fijo. Bajo shock conjunto, \(J\) es endógeno y ese signo aislado no fija el signo de la respuesta total.

## Política editorial y de transparencia

- El manuscrito fue **aportado por el autor**, no fabricado ni transcrito como si fuera escritura humana por IA.
- Esta documentación **corrige el estado anterior «0/8 recibidos»**. Conservamos el historial y anotamos que el cotejo matemático profundo sigue pendiente.
- El PDF se preserva en Drive por ahora. Para satisfacer una entrega que requiera archivos presentes físicamente en GitHub, se necesita subir el binario al repositorio; este índice por sí solo **no sustituye esa subida**.
- Distinguir la recepción del archivo de la hora límite del 26/11/2026, 22:00 Lima; el registro de Drive fue posterior.
