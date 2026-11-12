# IE Project 18 — normalizacion de las nueve derivadas escalares en la raiz congelada (12-XI-2026)

## Evidencia previa

El run [43267504901](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43267504901) para la revision `6fe9d5b84554030a6ca3f020b63de45865e2ffac` termino `success` en `build`. El archivo `code/irf/output/frozen_33_source_shaped_candidate_partition.json` fue generado tras comprobar una particion exacta de 33 posiciones fuente en los grupos disjuntos de 8, 16 y 9, todos con el mismo estado congelado y `P0`.

El diagnostico de las nueve filas de nivel/log registro `max_exact_nonlinear_level_transform_error = 5.997806418189811e-16` en rama `binding` y `8.418829869349942e-17` en `slack`. Su error de comparacion de filas logaritmicas es cero por construccion de la transcripcion. Nada de esto ejecuta las expresiones originales del operador economico Lean.

## Nueva prueba numerica de derivadas en raiz

Se anadio `code/irf/audit_frozen_nine_root_jacobian_normalization.py`, ejecutado desde `code/verify.py` y archivado desde `build.yml`.

Para las nueve filas escalares de indices SOURCE `4,5,6,9,10,21,22,25,26`, se considera en la rama `binding` la raiz estacionaria `z=0`, intervenciones de politica monetaria `(0,0,0,0)`, mismo `frozen_stationary_seed(steady_case())` y `P0` 16×6. No se sustituye por la raiz `make_boundary(s)` ni se considera que la rama `slack` tenga raiz estacionaria demostrada.

La identidad condicional transcrita entre un residuo en niveles `s(z)` y su residuo logaritmico `g(z)` tiene la forma

`s(z) = epsilon * d(z) * expm1(g(z))`,

con `epsilon=+1` en filas de diferencias positivas y `epsilon=-1` para las dos Euler del hogar, y con `d(z)>0`. Por diferenciacion formal:

`Ds(z)[v] = epsilon * (Dd(z)[v] * expm1(g(z)) + d(z) * exp(g(z)) * Dg(z)[v])`.

En una raiz comun `g(0)=0`, desaparece el primer termino y queda

`Dg(0)[v] = epsilon / d(0) * Ds(0)[v]`.

El nuevo auditor contrasta numericamente esta igualdad y la expresion completa de la regla del producto para 33 perturbaciones coordenadas y tres tamanos de paso central `2e-5`, `2e-6`, `2e-7`. Los nueve multiplicadores `epsilon/d(0)` se registran en JSON, con valores propios de esta raiz, no de la antigua frontera switching.

## Limites y criterio de reporte

El nuevo test exige que los errores de normalizacion y regla del producto sean inferiores a `5e-7`; guarda hashes SOURCE, Python, P0 y codigo de transcripcion. **Estado: PENDIENTE DE CI** hasta observar `build=success` del SHA que incorpora la comprobacion. Un error de diferencias finitas bajo el umbral no es un encierro de error matematico riguroso.

El nuevo reporte no ejecuta `fderiv` de Lean, no transporta todavia las 33 derivadas a una sola matriz original SOURCE, no certifica una inversa y no establece la equivalencia de la continuacion terminal `tail` con el grafo Python `P0`. El exito de 33/33 filas SOURCE-shaped candidatas tampoco es prueba de igualdad funcional con las 33 filas originales SOURCE.

## Proximo bloque

Especificar un operador de transformacion **funcional** `T(z)` en la misma carta, recogiendo los nueve factores no lineales, las dos cizallas Euler dependientes del estado y las dieciseis filas restantes; auditar que la transformacion y `psi` sean diferenciables, con matrices invertibles en la raiz. Solo entonces intentar conectar `D F_py` al Jacobiano SOURCE y crear un certificado riguroso de inversa.

PR #2 continua draft, sin fusionar main.
