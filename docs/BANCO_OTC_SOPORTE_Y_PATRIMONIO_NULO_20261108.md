# IE Project — frontera de patrimonio nulo y soporte probabilístico

Fecha: 2026-11-08. Estado: **propuesta matemática pendiente de formalización en Lean**. Este documento no acredita teoremas ni resultados de equilibrio.

## Punto de partida certificado condicionalmente

El módulo `PaperBankConditionalOTCTransitionIdentityCandidate.lean` usa:
- aversión al riesgo logarítmica;
- consumo positivo en toda historia;
- patrimonio de la política full-retention estrictamente positivo en **toda** historia conjunta;
- patrimonio agregado positivo en toda historia agregada;
- una cota condicional exógena para el factor OTC descontado.

La identidad de transición propuesta es una igualdad de sumas finitas. La demostración actual usa divisiones por patrimonios y por consumo, por lo que sus hipótesis estrictas no pueden eliminarse mediante mera simplificación sintáctica.

## Proposición a formalizar: restricción al soporte

Sean \\(H_n\\) las historias conjuntas de estados y shocks de pagos hasta \\(n\\); \\(p_n(h)\\geq0\\) sus probabilidades primitivas; \\(e_n(h)\\geq0\\) el patrimonio bancario y \\(m_n(h)\\geq0\\) el SDF acumulado. Sea
\\[
M_n = \\sum_{h\\in H_n}p_n(h)m_n(h)e_n(h).
\\]
Defínase el soporte \\(H_n^+ = \\{h:p_n(h)>0\\}\\). Si \\(p_n(h)=0\\), los términos de \\(M_n\\) se anulan sin necesidad de definir factores de retorno en esos nodos. Para nodos con \\(p_n(h)>0\\) y \\(e_n(h)>0\\), puede emplearse la identidad multiplicativa del retorno del banco, siempre que consumo agregado e individual sean positivos.

Para nodos con \\(p_n(h)>0\\) y \\(e_n(h)=0\\), hace falta probar una propiedad de **absorción**:
\\[
e_n(h)=0\\quad\\Longrightarrow\\quad e_{n+1}(h,s,\\omega)=0
\\]
para **todo hijo con probabilidad condicional positiva**. De lo contrario, es falso representar el patrimonio hijo mediante \\(e_n(h)G_n(h,s,\\omega)\\) con factor finito. Una recapitalización externa o transferencias adicionales destruyen esta implicación.

Bajo absorción, la contribución de cada padre con patrimonio cero y la de sus hijos con peso positivo es cero. Los hijos de transición nula tampoco contribuyen. Así, basta imponer la identidad de evolución en los padres de soporte positivo con patrimonio estrictamente positivo; se evita dividir por cero.

## Cota condicional: versión con soporte

Defínase \\(W_n(h)=p_n(h)m_n(h)e_n(h)\\geq0\\).
En nodos activos \\(A_n=\\{h:p_n(h)>0, e_n(h)>0\\}\\), sea
\\[
g_n(h)=\\sum_{s,\\omega} P(s,\\omega\\mid h) G_n(h,s,\\omega).
\\]
Si la transición exacta admite la descomposición
\\[
M_{n+1}=\\sum_{h\\in A_n} W_n(h)g_n(h),
\\]
y \\(g_n(h)\\leq\\bar g\\) para todo nodo activo, entonces
\\[
0\\leq M_{n+1}\\leq\\bar g M_n.
\\]
No se necesita independencia estocástica entre patrimonio histórico y retorno OTC; la cota es **condicional a la historia**.

Con probabilidad de supervivencia bancaria \\(1-\\psi_B\\geq0\\), si
\\[
0\\leq q=(1-\\psi_B)\\bar g<1
\\]
y \\(V_0\\leq C\\), resulta \\(0\\leq V_n\\leq Cq^n\\), por lo que \\(V_n\\to0\\) y \\(\\sum_n V_n<\\infty\\).

## Obligaciones de prueba y alcance económico

1. **Definiciones**: verificar en el código fuente que cada peso de Markov y de pagos es no negativo, y que la masa del hijo es peso del padre por transición condicional. No confundir historia con probabilidad cero y patrimonio cero.
2. **Absorción**: buscar el teorema fuente de patrimonio nulo y comprobar que cubre la **misma** política full-retention y todos los hijos soportados, sin recapitalización. Si no, formularlo como hipótesis explícita.
3. **Descomposición por casos**: particionar cada suma finita por peso nulo, peso positivo/patrimonio nulo y peso positivo/patrimonio positivo. Evitar redefinir una razón \\(0/0\\) como retorno económicamente significativo.
4. **Consumo**: para SDF con utilidad logarítmica se requiere consumo estrictamente positivo por lo menos a lo largo de historias con soporte positivo; preservar definición fuente si está codificada en todo el dominio.
5. **Cota OTC**: demostrar \\(g_n(h)\\leq\\bar g\\) para los precios OTC que realmente satisfacen equilibrio y restricciones bancarias; no asumirla a partir de la mera observación de IRF.
6. **Óptimo**: la TVC de una trayectoria full-retention no establece ni Bellman optimal, ni la solución KKT de todas las ramas, ni existencia/unicidad del equilibrio competitivo.
7. **Política y crecimiento**: no promover un efecto favorable de reasignación condicional a crecimiento de largo plazo sin probar la transición de capital/TFP y una trayectoria de equilibrio.

## Siguiente módulo Lean sugerido

`PaperBankSupportedConditionalOTCCandidate.lean`, inicialmente con lemas abstractos de sumas finitas que no importan supuestos de equilibrio; luego adaptar los lemas a `continuationTransitionWeight`, `continuationPaymentWeight`, `sourceFullRetentionCandidate` y `bankCumulativeSDFAt`. Agregar `#print axioms` y registrar el SHA exacto del workflow antes de llamar **demostrado** a cualquier resultado.

**No sustituye** el módulo exacto previo: conserva trazabilidad y evita elevar hipótesis más débiles de manera no justificada.
