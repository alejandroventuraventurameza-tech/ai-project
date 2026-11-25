# Guía de estudio para tres resultados adicionales del cuerpo principal

**No es una nota manuscrita del autor.** Esta es una guía tipografiada, complementaria a las primeras cinco pruebas solicitadas en el iPad. Está basada exactamente en \`paper/body_compact_after.tex\` de la revisión 25/11/2026. Los tres resultados se inventariaron en \`paper/compact_extra_results_3.json\`, sin alterar el ledger original de 57.

## A. Decaimiento por bloques: \`prop:compact_exact_tail_power\`

**Hipótesis.** Sea \(F_0\) una matriz \(6\times6\), con coeficientes racionales definidos por los decimales exactos del insumo; la auditoría aritmética verifica

\[
\|F_0^{48}\|_\infty<\frac{24}{25},
\qquad
\max_{0\le r<48}\|F_0^r\|_\infty<\frac{61}{10}.
\]

**Derivación que debe reproducirse.**

1. Para \(k\ge0\), aplicar división euclidiana: \(k=48m+r\), \(m=\lfloor k/48\rfloor\), \(0\le r<48\).
2. Escribir \(F_0^k=(F_0^{48})^mF_0^r\).
3. Aplicar submultiplicatividad: \(\|F_0^kx\|_\infty\le\|F_0^{48}\|_\infty^m\|F_0^r\|_\infty\|x\|_\infty\).
4. Sustituir las dos cotas (las desigualdades estrictas dan una cota no estricta suficiente) y obtener

\[
\boxed{\|F_0^kx\|_\infty\le
\frac{61}{10}\left(\frac{24}{25}\right)^{\lfloor k/48\rfloor}\|x\|_\infty.}
\]

**Verificación distinta de la prueba algebraica:** los valores numéricos estrictos provienen de \`code/irf/exact_linear_tail_power_certificate.py\`, que utiliza \`fractions.Fraction\`; no los vuelve verdaderos un argumento abstracto de submultiplicatividad. Contrastar los coeficientes exactos del script y su resultado de CI.

## B. Robustez de la gráfica lineal: \`lem:compact_robust_tail_power\`

**Hipótesis.** Sea \(A\in\mathbb R^{6\times6}\) tal que \(\|A-F_0\|_\infty\le10^{-4}\).

1. Demostrar, por telescopado, que para \(n\ge1\):

\[
A^n-F_0^n=
\sum_{j=0}^{n-1}
F_0^{n-1-j}(A-F_0)A^j.
\]

   **Cómo demostrar:** comprobar \(n=1\) y pasar de \(n\) a \(n+1\), o insertar y sustraer \(F_0^{n}A\). No omitir el orden de factores: las matrices, en general, NO conmutan.

2. Aplicar norma inducida:

\[
\|A^n\|_\infty\le
\|F_0^n\|_\infty+
10^{-4}\sum_{j=0}^{n-1}\|F_0^{n-1-j}\|_\infty\|A^j\|_\infty.
\]

3. Definir \(a_0=1\) y
\[
a_n=\|F_0^n\|_\infty+10^{-4}
\sum_{j=0}^{n-1}\|F_0^{n-1-j}\|_\infty a_j.
\]
   Por inducción, \(\|A^n\|_\infty\le a_n\).

4. Separar la **auditoría aritmética** de la **demostración universal**: el script verifica, con fracciones exactas, \(a_{48}<49/50\) y \(\max_{r<48}a_r<7\). La prueba no supone que el autor multiplicó a mano 48 matrices; sí exige comprender la recursión, los signos y qué acredita el script.

5. Usar \(k=48m+r\), submultiplicatividad y las cotas del paso 4 para obtener

\[
\boxed{\|A^kx\|_\infty\le
7\left(\frac{49}{50}\right)^{\lfloor k/48\rfloor}\|x\|_\infty.}
\]

**Limitación que escribir:** esta es una cota sobre una matriz próxima al mapa lineal fijado; no prueba por sí sola existencia, estabilidad global ni transversalidad del sistema económico no lineal.

## C. Cuña financiera entre H y L: \`prop:compact_source_collateral_effective_wedge\`

**Hipótesis:** mismo \(R_t^L>0\) para ambas firmas; \(0\le\delta<1\), \(\Pi_{t+1}>0\), \(q_{t+1}>0\) y \(\theta_H<\theta_L\). El texto del paper exige \(\delta<1\); comprobar y declarar adicionalmente la condición económica \(\delta\ge0\).

Definir

\[
J_{t+1}=(1-\delta)\Pi_{t+1}q_{t+1}>0,\qquad
p_{i,t}^{eff}=q_t-\frac{\theta_iJ_{t+1}}{R_t^L}.
\]

Restar:

\[
\begin{aligned}
W_t&=p_{H,t}^{eff}-p_{L,t}^{eff}\\
&=\left(q_t-\frac{\theta_HJ_{t+1}}{R_t^L}\right)
-\left(q_t-\frac{\theta_LJ_{t+1}}{R_t^L}\right)\\
&=\frac{(\theta_L-\theta_H)J_{t+1}}{R_t^L}>0.
\end{aligned}
\]

Para \(W,J,R^L>0\), tomar logaritmos:

\[
\boxed{\Delta\log W_t=\Delta\log J_{t+1}-\Delta\log R_t^L.}
\]

**Interpretación condicionada:** una menor tasa bruta, a \(J\) fijo, *aumenta* la diferencia de precios efectivos H versus L; para el shock monetario real \(J\) también se mueve. En rama S, L tiene holgura: su precio pignorable calculado aquí no es necesariamente el costo marginal efectivo de inversión. No equiparar la cuña con bienestar.

## Protocolo de escritura y cotejo

El autor deberá escribir en el iPad hipótesis, ecuaciones intermedias, justificación algebraica y veredicto personal, citando la etiqueta de cada resultado. Para las cotas de matrices, contrastar el script racional y separar el paso algorítmico del supuesto cuantitativo: no atribuir una prueba universal del equilibrio a un verificador de una matriz congelada.

**Cobertura hasta hoy:** 0 pruebas manuscritas realmente recibidas. La primera tanda del autor contiene cinco demostraciones; las tres aquí descritas son una segunda tanda pendiente.
