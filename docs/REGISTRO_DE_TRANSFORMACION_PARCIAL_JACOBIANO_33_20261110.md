# IE Project — transformación parcial de las 33 filas del Jacobiano

**Fecha:** 10 de noviembre de 2026. **Alcance:** conversiones locales algebraicas entre residuos SOURCE (Lean) y residuos del evaluador Python. **No es un certificado de igualdad de los Jacobianos 33×33**. Los estados y controles se indexan en coordenadas logaritmicas positivas, y las 34 condiciones SOURCE del problema de frontera no pueden identificarse con las 33 ecuaciones que definen cada rama interior.

## 1. Lema general y signo de las normalizaciones

Sean $F(z)>0$ y $C(z)>0$ diferenciables en una vecindad de $z_*$, donde $F(z_*)=C(z_*)$. Defina
\[
 f(z)=F(z)-C(z),\qquad g(z)=\log(F(z)/C(z)).
\]
Hay una identidad exacta, incluso lejos de la raiz:
\[
 f(z)=C(z)\bigl(e^{g(z)}-1\bigr).
 \tag{J1}
\]
Diferenciando en la raiz, el término $D C(z_*)\cdot(e^{g(z_*)}-1)$ desaparece y
\[
 Dg(z_*)=\frac{1}{C(z_*)}Df(z_*).
 \tag{J2}
\]
Para la Euler de depositos con $r(z)>0$, la fuente emplea $f(z)=1-r(z)$ y Python $g(z)=\log r(z)$. Por tanto
\[
 f(z)=1-e^{g(z)},\qquad
 Dg(z_*)=-Df(z_*)\quad\text{cuando }r(z_*)=1.
 \tag{J3}
\]
**Esta fila tiene signo negativo**. En cambio, el caso de empresa L holgada usa $f=r-1$ y $g=\log r$, con $Dg(z_*)=Df(z_*)$. Distinguir estos casos evita confundir el signo del jacobiano con una discrepancia economica.

Las igualdades de conjuntos de ceros correspondientes a las filas de regimen vinculante y holgado, la garantia comun y las condiciones fuente de colateral ya fueron comprobadas por Lean, con 17 teoremas verificados en total. Los tres lemas fuente para patrimonio bancario, oferta laboral y Euler del hogar **ya compilan en el kernel Lean** sin `sorryAx`, con axiomas fundacionales solamente ([Actions #42924055334](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42924055334), SHA `a5b146321e728a4ded7b82d1491303e75093a4e8`). El bloque contiene **20 teoremas comprobados**. El cálculo específico de factores del Jacobiano completo y la identificación de las demás filas permanecen PENDIENTES.

## 2. Matriz de coeficientes conocida, SIN completar filas pendientes

Denote $\mathcal F$ los residuos SOURCE, $\mathcal G$ los de Python y $P$ la permutacion SOURCE→Python auditada en \`code/irf/audit_python_lean_prefix_row_permutation.py\`. Solo algunas filas satisfacen de manera demostrada o estructuralmente identificada una normalizacion escalar. En lo que sigue $d$ indica la fecha de origen, $\widehat B_{d+1}=a_B R_d^L B_d/\Pi_d$, $C^w_d=\chi_W C_{W,d}^{\sigma_W}L_d^\varphi$, $J_{d+1}=(1-\delta)\Pi_{d+1}q_{d+1}$ y $K_{i,d+1}$ es el capital proyectado.

| Fila SOURCE → Python | Rama/fecha | Factor candidato de $D\mathcal G$ respecto de la fila $D\mathcal F$ en una raiz | Estatus y restriccion |
|---|---|---|---|
| 4→2 | H vinculante, $d=0$ | $1/(\theta_H J_1 K_{H,1})$ | cero fuente probado; factor por (J2), requiere positividad |
| 5→5 | L vinculante, $d=0$ | $1/(\theta_L J_1 K_{L,1})$ | cero fuente probado; factor por (J2) |
| 5→5 | L holgada, $d=0$ | $+1$ | fuente usa $r-1$, Python $\log r$, con $r=1$ |
| 6→6 | rostro nominal bancario, $d=0$ | $1/\widehat B_1$ | nuevo lema candidato de cero-set |
| 9→9 | trabajo, $d=0$ | $1/C^w_0$ | lema candidato; además $\sigma_W=\varphi=1$ en la implementación Python |
| 10→10 | Euler del hogar, $d=0$ | $-1$ | lema candidato; signo invertido imprescindible |
| 21→21 | garantía nominal común, $d=1$ | $1/J_2$ | cero-set probado por Lean |
| 22→22 | rostro bancario, $d=1$ | $1/\widehat B_2$ | mismo lema fuente genérico de la fila 6 |
| 25→25 | trabajo, $d=1$ | $1/C^w_1$ | mismo lema fuente genérico de la fila 9 |
| 26→26 | Euler del hogar, $d=1$ | $-1$ | mismo lema fuente genérico de la fila 10 |

Estas filas suman **nueve indices SOURCE distintos** (la fila 5 tiene dos formulas alternativas segun la rama). Los otros 24 indices SOURCE **no** se declaran identificados. En especial, las Euler empresariales no deben tratarse como diagonales: la diferencia entre las formulaciones reducida y no reducida exige sumar un múltiplo de la fila de garantía (operación de fila triangular invertible), que ya se cotejó numéricamente en 16 filas.

## 3. Que falta antes de inferir un Jacobiano SOURCE invertible

Una version **HIPOTETICA** de la identidad buscada seria
\[
D\mathcal G(0)=P\,T(x_*)\,
D\mathcal F(x_*)\,D\psi(0),
\tag{J4}
\]
donde $\psi$ alinea los dos espacios de coordenadas logaritmicas, $P$ reordena filas y $T$ contiene los factores de (J2) y (J3), las operaciones de fila de las Euler y las transformaciones **AUN DESCONOCIDAS** de las otras 24 filas. **J4 NO ES UN TEOREMA DEL MODELO** hasta construir $\psi$ y demostrar cada componente de la igualdad funcional cerca de la raiz.

Para trasladar una cota $\|D\mathcal G(0)^{-1}\|$ a SOURCE hace falta probar que $P$, $T(x_*)$ y $D\psi(0)$ existen, son invertibles y estan representados por matrices certificadas sobre el MISMO dominio. Una cota de estabilidad de la matriz lineal de 6 estados no implica automaticamente ese rango 33×33.

La condicion SOURCE n.º 34 es $\mu_{L,0}$ y su igualdad a cero se impone en el **problema de frontera** S/B. En el interior de B, $s_L=0$ y $\mu_L>0$ son compatibles con complementariedad; añadir $\mu_L=0$ al sistema de B lo sobreidentificaria economicamente. La equivalencia numérica de esa fila con el diagnóstico Python no constituye una prueba de que las 34 ecuaciones se anulen en B.

## 4. Evidencia numerica y protocolo de cierre

En las 160 transiciones por rama y sus bases se verificaron con errores $\sim10^{-16}$ las identidades nivel/log de rostros empresariales y garantia comun, ademas de la ecuacion 34. La auditoria posterior \`code/irf/audit_remaining_log_rows.py\` verifica las filas SOURCE 0, 3 y 4 del bloque de once, aplicadas a ambos periodos y ramas, **tambien con perturbaciones positivas fuera de la raiz**. Su archivo \`remaining_log_rows_audit.json\` se obtiene y archiva en GitHub Actions; las pruebas principales de Python pasaron en la ejecucion \`42923540337\`. Ello comprueba la conversion de los residuos de esas funciones, no sus 33 derivadas estructurales simultaneas.

**Compuerta siguiente:** formalizar el factor jacobiano de cada fila en la carta de 33 coordenadas Lean, construir $T$ y $\psi$ exactos, probar una equivalencia funcional de operadores (no solo igualdad de ceros) y pasar las matrices inversas por aritmetica intervalar dirigida. Solo entonces intentar un teorema de funcion implicita en SOURCE, un grafo $C^1$ invariante con radio cuantitativo y, finalmente, la prueba independiente de optimalidad y transversalidad de equilibrio infinito.


## 5. Ledger numerico de escalas sin sobrecertificacion

`code/irf/audit_partial_jacobian_row_scales.py` genera, desde CSV/metadata regenerados y el mapa de permutacion verificado, un JSON de coeficientes **candidatos** para los nueve indices de la tabla anterior, distinguiendo B y S en la fecha cero. Comprueba que los factores son finitos y no nulos y que los residuos base correspondientes son practicamente cero, pero **no** eleva ese subbloque a matriz 33×33 fuente. El archivo `code/irf/output/partial_source_jacobian_row_scale_ledger.json` conserva el conjunto de los **24 indices desconocidos** y tres interruptores de estado en `false` para equivalencia de operador, inverso jacobiano y carta entre espacios.
