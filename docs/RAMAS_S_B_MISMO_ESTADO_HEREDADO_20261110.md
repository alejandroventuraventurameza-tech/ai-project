# Ramas S/B con el mismo estado heredado: certificado local, candidatos y limite dinamico

**Fecha de auditoria:** 10 de noviembre de 2026. **Referencia numerica exacta:** commit 46494bf60837d7c1c7da8c248dadbb64fe9ef4cf, job Python syntax de [GitHub Actions #42912681195](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42912681195). Se aprobo la nueva auditoria focalizada; artifact name: same-predecessor-branch-diagnostic, artifact ID 13808585718. La compilacion adicional de la nueva tabla de respuestas y su integracion en build requiere una verificacion CI propia de ese SHA: no heredar semaforos de otros commits.

**Clasificacion:** NUMERICO (raices del prefijo, margenes financieros y KKT necesarias), EXACTO-RACIONAL (cota algebraica en transcripcion independiente de formulas), NO DEMOSTRADO (existencia de equilibrios competitivos infinitos y multiplicidad economica).

## 1. Cronologia, objeto y estados

Partimos del mismo estado predeterminado
\(X_0=(k_{H0},k_{L0},F_{H0},F_{L0},F^B_0,\mathfrak R_0,\mathfrak M_0)\),
construido mediante frozen_stationary_seed(s), identico en las ramas S y B y en todos los shocks. La matriz de cierre local P0 (16 por 6) y las innovaciones anunciadas para fecha 1 permanecen invariantes.

- B: H y L tienen el colateral activo en fecha 0.
- S: H activo y L holgado en fecha 0, con multiplicador L igual a cero.
- En fecha 1 ambas ramas usan el cierre de colateral activo.

Para cada rama se comprueban los mismos 33 residuos no lineales, el presupuesto de firmas, la FOC de capital, la FOC de prestamo con dual original reconstruido, no negatividad del dual y del saldo no pignorable, complementariedad, esquina de depositos empresariales, holgura de topes bancarios, signos de pagos OTC y solvencia en los dos estados idiosincraticos. Son **condiciones necesarias**; no prueban optimos globales de bancas y hogares ni valor descontado de horizonte infinito.

## 2. Obstruccion local exacta de S alrededor del estado B

De la regla de remuneracion y corredor estacionarios en finite_irf.py, RD=100/99, be=24/25, Delta=1/50, rho=1/10, zeta=1/5, aa=tight=1/2.

Como (11/9)^2 < 3/2, se tiene sqrt(3/2)>11/9, de donde vv<9/20. Esto permite cminus<29/2000, cplus<9/4000, cbar<67/8000 y 0<cdiff<29/2000. Puesto que el argumento de la raiz del remunerado es menor que (RD)^2 + 2 RD zeta (29/2000) < (1013/1000)^2, se sigue que el tipo bruto de credito estacionario satisface

\[
 R^L < \frac{RD+1013/1000}{2}+\frac{67}{8000}
       =\frac{807781}{792000}<\frac{51}{50}.
\]

Nota: el script de certificacion de partida aplica una **cota aun mas conservadora**, R^L<41/40, y concluye lo siguiente sin depender de la mejora anterior.

La FOC de prestamo para la firma L con colateral holgado es \(R^L_0 \beta_E c_{L0}/(c_{L1}\Pi_1)=1\); equivalentemente, el dual normalizado es cero:

\[
 \upsilon_L=\frac{1}{R^L_0}
               -\frac{\beta_E c_{L0}}{c_{L1}\Pi_1}=0.
\]

En las coordenadas logaritmicas del prefijo,

\[
 \upsilon_L(z)=\frac{e^{-z_{15}}}{\overline R^L}
        -\frac{24}{25}e^{z_8-z_{24}-z_{28}}.
\]

En toda la bola cerrada de supnorma \(r=1/500\), usando \(e^{-r}\ge 1-r\) y \(e^{3r}\le 1/(1-3r)\), la cota conservadora de tipos \(R^L<41/40\) implica

\[
 \upsilon_L(z)\ge\frac{40}{41}(1-r)
   -\frac{24/25}{1-3r}
 =\frac{4006}{509425}>0.
\]

Por contradiccion, **ninguna raiz de la fila de prestamo L holgado puede encontrarse en esta bola** bajo ninguna perturbacion del vector de los cuatro instrumentos, manteniendo el antecesor usado. Esta afirmacion es algebraica y local; no prueba inexistencia global de S ni es aun un teorema reflejado contra las definiciones literales del kernel Lean.

## 3. Hallazgo numerico: dos candidatos KKT del mismo prefijo

La auditoria encontró UNA raiz B y UNA raiz S admisibles respecto de las condiciones **necesarias implementadas** para cada escenario: sin shock y los cuatro shocks individuales negativos de magnitud 1e-5. Las innovaciones de remuneracion y de cantidad de reservas estan expresadas en logaritmos; los cambios de encaje y ancho de corredor son niveles de sus parametros.

| Metrica en fecha cero sin shock | B (H y L atan) | S (L holgada) |
|---|---:|---:|
| Producto contemporaneo Y0 | 2.7335756723 | 2.8192602725 |
| Capital elegido H para fecha uno | 11.6738296186 | 11.7876931188 |
| Capital elegido L para fecha uno | 19.3943407704 | 19.4315872306 |
| Credito nuevo H | 1.7080596941 | 1.7102579361 |
| Credito nuevo L | 7.5671692655 | 7.4385534872 |
| Dual normalizado de L | 0.0280951952 | aproximadamente 0 |
| Holgura relativa de colateral de L | 0 | 0.01058455 |
| Norma infinito de z respecto al estacionario B | 0 | 0.10436879 |

Las raices tienen residuos maximos de 33 filas inferiores a 5e-14. Las comprobaciones de complementariedad para H y L, depositos de esquina, margenes de caps bancarios, signos de pagos y solvencia resultaron compatibles con el conjunto activo declarado en los dos primeros periodos.

**Advertencia fuerte:** la candidata S no es un segundo estado estacionario. Es una trayectoria de prefijo bajo un cierre de fecha dos local-lineal que se ha construido a una distancia de aproximadamente 0.104 de la raiz estacionaria B. No se ha probado que P0 sea una aproximacion valida a esa distancia, ni que la raiz S pueda prolongarse a una trayectoria no lineal de horizonte infinito. Por ello NO se declara multiplicidad economica estructural.

## 4. Shocks comparados con sus propios basales, no entre basales

Para cada instrumento, se resuelve la rama afectada y se compara con la **solucion sin shock de esa misma rama**. Todas comparten el mismo antecesor original, aunque las soluciones de base de S y B difieran.

| Shock de -1e-5 | Cambio logaritmico % Y0, B | Cambio logaritmico % Y0, S | Cambio logaritmico % k_H1, B | Cambio logaritmico % k_H1, S |
|---|---:|---:|---:|---:|
| Remuneracion de reservas (innovacion log) | -0.004238422 | -0.000183524 | -0.001095096 | +0.000108386 |
| Cantidad de reservas (innovacion log) | +0.000010230 | +0.000000587 | +0.000002641 | -0.000000210 |
| Coeficiente de encaje (nivel) | -0.000058618 | +0.000012114 | -0.000015160 | +0.000006190 |
| Amplitud de corredor (nivel) | -0.001554682 | +0.000264241 | -0.000400666 | +0.000149300 |

Estos cambios son **derivaciones numericas**, no multiplicadores estructurales certificados. No tienen unidad homogenea entre las dos innovaciones en log y los dos cambios en nivel. La inversion de signos entre ramas en producto y capital H bajo varios instrumentos muestra por que la seleccion del conjunto activo es decisiva; no determina que rama sera seleccionada en un equilibrio completo.

Tampoco es licito llamar a la diferencia Y_S-Y_B un beneficio de la relajacion del colateral: produccion, trabajo y precios cambian conjuntamente, no se ha demostrado que S sea optimo dinamicamente ni que las dos soluciones correspondan a una politica realizable.

## 5. Cadena de reproduccion y siguientes compuertas

- Fuente de ecuaciones: code/irf/finite_irf.py (prefix_residual, period_metrics, auxiliary, decode_prefix).
- Construccion del estado heredado invariante: code/irf/frozen_stationary_prefix_audit.py.
- Auditor por ramas, cota racional y cotejo de todas las soluciones: code/irf/frozen_same_predecessor_branch_audit.py.
- Ejecucion: python code/irf/frozen_same_predecessor_branch_audit.py desde la raiz del repositorio. El informe generado es code/irf/output/same_predecessor_branch_audit.json. La version nueva genera las diferencias de shocks dentro de la misma rama y los desplazamientos por bloques de coordenadas; validar su **SHA** antes de citar datos nuevos.
- Reproducibilidad: el workflow editorial-qa.yml conserva el JSON en un artifact, y build.yml lo archiva tambien cuando code/verify.py termina sin errores.

**Compuertas avanzadas en esta sesion:** se han medido los desplazamientos por bloques de coordenadas y se ha resuelto la continuacion FINITA no lineal con horizonte hasta 160; ver la seccion 6. Permanecen **PENDIENTES**: demostrar convergencia de la sucesion de problemas truncados cuando T tiende a infinito, cotejar todos los presupuestos y dualidades con el MODELO FUENTE de 34 filas, probar factibilidad bancaria completa y optimalidad global de firmas/hogar/banco bajo historias soportadas, cerrar la TVC y estudiar crecimiento solo despues de contar con equilibrios genuinamente comparables.

**Veredicto:** existe evidencia NUMERICA de dos soluciones algebraicas distintas del reducido, con KKT necesarias y continuacion finita no lineal compatibles. **No** se ha probado existencia de dos equilibrios economicos infinitos. Mantener PR #2 draft y main intacta.

## 6. Auditoria nueva de continuaciones no lineales T=8 a 160

**Codigo:** code/irf/frozen_same_predecessor_nonlinear_tail_probe.py, commit e7270ab348984400f79e6950a2e21ec323968474. **Fuente del ejecutor apilado:** compare_nonlinear_tail.py, clase StackedPath, cuyo constructor original se corrige antes de resolver: se sustituye make_boundary() por frozen_stationary_seed(), de modo que el antecesor y las promesas heredadas son exactamente iguales para S y B. **Compilacion reproducible:** [GitHub Actions #42913297654](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42913297654), exitoso en el SHA anterior. **Artifact:** same-predecessor-nonlinear-tail. No es un certificado Lean.

Se ensayan cinco horizontes (8, 20, 40, 80, 160), dos cierres terminales (controles fijados en el grafo P0 o controles terminales nulos respecto del estacionario), dos ramas (S/B) y dos condiciones de politica (sin shock y un shock de -1e-5 de remuneracion de reservas). **40 de 40 ejecuciones** encontraron raices con residuos del sistema apilado inferiores a 1e-8 y todos los margenes necesarios inspeccionados sin incumplimientos.

### Resultados comparables de producto: misma rama y mismo antecesor

| T | Delta log Y0 (%) B, grafo lineal | Delta log Y0 (%) S, grafo lineal | Delta log Y0 (%) B, controles finales fijos | Delta log Y0 (%) S, controles finales fijos |
|---:|---:|---:|---:|---:|
| 8 | -0.004238270 | -0.000203689 | -0.003659450 | -0.002055196 |
| 20 | -0.004238085 | -0.000203308 | -0.003765125 | -0.001136748 |
| 40 | -0.004238080 | -0.000203167 | -0.002349569 | -0.003403936 |
| 80 | -0.004238080 | -0.000203166 | -0.003743752 | -0.001416144 |
| 160 | -0.004238080 | -0.000203166 | -0.004202156 | -0.000304313 |

El cierre del grafo da respuestas estables conforme T aumenta en estas pruebas. El cierre con controles terminales fijos muestra sensibilidad importante y no monotona en horizontes intermedios; sus respuestas de T=160 se acercan a las del grafo, sin prueba de que su limite coincida. Para S a T=160, la respuesta del capital siguiente de H es +0.000101904% bajo grafo y +0.000069288% bajo controles terminales fijos. Ambos valores son respuestas numericas del **prefijo condicional**.

### Diagnostico del radio de continuacion

La norma maxima de las 33 coordenadas del prefijo en la raiz S sin shock es aproximadamente 0.10414. Sin embargo, el desplazamiento de las **seis variables de estado al inicio de la continuacion, fecha dos**, es solo aproximadamente 0.00363 y la desviacion maxima de estados durante la cola con grafo es aproximadamente 0.00462. El alejamiento del prefijo no implica que la condicion inicial del grafo P0 este a distancia 0.104 de la estacionariedad. La extension no lineal finita mitiga parte de esa inquietud, pero no certifica el radio de un teorema implicito ni la cola infinita.

**Se mantienen abiertas** las pruebas de suficiencia del equilibrio economico original, las condiciones terminales estocasticas, las restricciones OTC y decisiones de valor bancario en todo el arbol, la compatibilidad literal Lean-Python de 34 filas y la seleccion endogena de la rama. Ni 40 raices truncadas ni la estabilidad de T=160 permiten llamar demostrada la multiplicidad de equilibrios o el efecto permanente sobre la tasa de crecimiento.
