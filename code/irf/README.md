# IRF internas de pagos finitos

Desde la raíz del repositorio:

```sh
python -m pip install -r code/requirements.txt
python code/irf/reproduce.py
```

La reproducción completa del proyecto usa `python code/verify.py`: conserva el
laboratorio estático, los seis bloques V0-M y después ejecuta este reproductor.
No necesita rutas de Ubuntu, registros privados, agentes ni datos externos.

## Salidas

- `output/main/finite_irf_paths.csv`: niveles, referencias y desviaciones,
  períodos 0–160, ambas ramas.
- `output/main/finite_irf_validation.json`: parámetros, residuos, márgenes y límites.
- `output/delivery_audit.json`: impacto, contabilidad y sensibilidad.
- `output/tight_tolerance/`, `output/long_horizon/`: tolerancia 1e-13 y horizonte 320.
- `output/shock_1bp/`: sensibilidad fallida esperada del umbral de aproximación.
- `../../paper/figures/irf_*.pdf` y `.png`: figuras científicas para artículo y exposición.
- `../../paper/irf_impact_table.tex`: tabla generada; no editar cifras a mano.

## Experimento y unidades

Innovación adicional −1e-5 en el log de la regla de remuneración de reservas
(aproximadamente −0.1 pb), con iguales posiciones heredadas y anuncios posteriores.
La respuesta total de la tasa también incorpora la regla endógena. Referencia:
trayectoria de frontera del prefijo y continuación estacionaria, no todo un
estado estacionario. S significa que L pide crédito con holgura inicial; B que
ambas firmas están restringidas inicialmente. H permanece restringida.

Las tasas se muestran como 10000 veces la diferencia de tasas brutas por período,
sin anualizar; cantidades como 100 log(x/x_referencia). Capital elegido en t
se instala para t+1. La pérdida condicional usa producción de t+1 y sus recursos
agregados: 100 veces la diferencia de log(Y_eficiente/Y). No es bienestar ni una
medida empírica directa de fricción financiera.

## Método y límites

Prefijo de dos fechas no lineal, seguido de una continuación recurrente local
lineal. Parámetros ilustrativos, pagos binarios ±0.2 equiprobables y sin nuevas
innovaciones agregadas después del choque anunciado. Una compilación, un residuo
pequeño o una recursión de valor no prueban optimalidad dinámica ni equilibrio
completo. El certificado externo posterior de existencia reducida no está
integrado aquí como prueba Lean ni como trayectoria no lineal regenerada.

`illustrative_two_M_bond_proxy` retiene un diagnóstico del experimento original;
no asigna deuda pública ni demuestra el cierre fiscal. El nivel de deuda pública
permanece sin calibrar. La producción cae inicialmente y se auditan sus
identidades laborales y de recursos; su interpretación estructural sigue sujeta
al cierre económico.

## Procedencia de entradas

`finite_irf.py` adapta el reproductor interno previo sin cambiar sus ecuaciones.
Los scripts económicos de `../v0m/` mantienen sus hashes originales. `inputs/`
conserva una copia fija de la gráfica racional y sus dos certificados originales:
reproducir los certificados V0-M puede sobrescribir sus salidas con pequeñas
variaciones de plataforma. Separar estos insumos mantiene fijo el experimento
IRF y evita usar accidentalmente matrices nuevas con diagnósticos antiguos.
Las figuras se regeneran con Matplotlib; sus bytes pueden cambiar por versión
de fuentes/librerías. Las desigualdades y cifras, no la identidad binaria de un
PDF entre plataformas, son el criterio de reproducción.


## Diagnóstico de producción al impacto

`python code/irf/diagnose_impact.py` comprueba las identidades laborales y la
curva de Phillips, descompone el ajuste y ejecuta cuatro sensibilidades acotadas.
Los resultados están en `output/impact_diagnosis/REPORT.md` y `diagnosis.json`.
La reproducción general también ejecuta este diagnóstico después de generar
las IRF principales. No modifica el modelo ni convierte identidades de equilibrio
en una descomposición causal. La comparación con una continuación no lineal
independiente permanece pendiente.


## Comparación no lineal de la continuación

`python code/irf/compare_nonlinear_tail.py` resuelve conjuntamente las ecuaciones
no lineales reducidas hasta T-1, para T=20,40,80,160,320,640. Usa Newton con
Jacobiano disperso por bloques y búsqueda de paso; requiere SciPy. Compara el
cierre de gráfica lineal en T con controles terminales en sus valores de referencia
para T>=80. También resuelve la referencia con la misma condición terminal.
El segundo cierre no fija el estado terminal y no impone controles económicos
nulos, sino desviaciones logarítmicas nulas. No es una condición terminal exacta.

Los resultados se guardan en `output/nonlinear_tail_comparison/REPORT.md` y
`REPORT.json`, con trayectorias CSV separadas. Se comprueban residuos, la
consistencia del prefijo con el reproductor original, derivadas direccionales
del Jacobiano ensamblado y márgenes de régimen en los períodos calculados.
`python code/verify.py` ejecuta también esta comparación.

La solución finita reutiliza las ecuaciones económicas existentes: es una
comparación del método de continuación, no una auditoría independiente de todo
el modelo ni prueba de optimalidad. Las IRF principales no se sobrescriben.
Los cierres terminales pueden contaminar fuertemente horizontes cortos; comparar
horizontes y reportar la diferencia restante es parte de la interpretación.


## Trazabilidad del mecanismo

`python code/irf/trace_transmission.py` reconstruye las identidades de la regla
monetaria, formación de tasas bancarias, Euler del hogar, Phillips y producción
sobre la solución reducida no lineal T=640. Guarda las trayectorias y contribuciones
contables en `output/transmission_trace/`. Requiere primero la comparación no lineal;
la entrada general `python code/verify.py` ejecuta los pasos en ese orden.
Las contribuciones no son contrafactuales causales independientes; la suficiencia
económica y la formalización completa siguen pendientes.


## Auditoría de condiciones empresariales y bancarias

`python code/irf/audit_financial_blocks.py` reconstruye el patrimonio desde
producción y repagos heredados, los multiplicadores empresariales, las KKT
sin eliminar el dual, la esquina sin depósitos y los dos pagos de cada banco.
Comprueba solvencia, encaje posterior, caps, clearing esperado y renovación
sobre la solución no lineal T=640. Incluye una correspondencia de las 33 filas
con etiquetas del artículo; esa trazabilidad no es prueba de suficiencia.
Los resultados y las identidades de crédito y capital de H están en
`output/financial_blocks_audit/`. La reproducción general también lo ejecuta.

Más crédito no equivale a más inversión ni a menor multiplicador: el diagnóstico
conserva explícitamente esos resultados y sus diferencias entre S y B.
No certifica por sí solo optimalidad dinámica, equilibrio completo o bienestar.
