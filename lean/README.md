# Estado de formalización y alcance de esta entrega

**Actualización SOURCE (10 de noviembre de 2026):** el certificado literal del sistema reducido, incluidos ambos signos del residual y la brecha financiera heredada, superó compilación y auditoría de axiomas en el [gate #42902110667](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42902110667), para el commit `3c881026`. El alcance y las limitaciones constan en [SOURCE_CERTIFICATE_STATUS_2026-11-10.md](SOURCE_CERTIFICATE_STATUS_2026-11-10.md). Este certificado no prueba la existencia de un equilibrio dinámico con estado heredado fijo ni la totalidad de las afirmaciones del manuscrito.

**La descripción de la campaña preliminar que sigue es histórica** y se refiere a otro alcance y otras revisiones de código; no invalida ni amplía el certificado específico SOURCE anterior.

La campaña preliminar en un clon aislado de AppliedModelingLib produjo pruebas
auxiliares y construcciones condicionales. Se trabajó sobre la fuente anterior
SHA256 `a89e83f02cb8745a6c59eeb3c047bcb335033a18eae4b0ea538ce47a61cf7764`.
El artículo actual incorpora IRF y una revisión editorial posterior: no debe
atribuirse automáticamente a esa campaña cobertura de la fuente modificada.

El último bloque inspeccionado del modelo Lean tiene SHA256
`d5e9bb95aad09ff515cc1418778c241d1b91ca3095c02b31eb369f496ea38d86`.
Compiló y recibió revisión acotada, pero no cierra la instancia de ambas ramas.
Se ha preparado una copia de los módulos y dependencias en `checkpoint/`,
con rutas de reconstrucción y huellas digitales. Es una instantánea preliminar
para revisión; no constituye la integración de la campaña oficial del curso.

## Separación de evidencias

- Pruebas auxiliares: política bancaria por historia, implicaciones de
  factibilidad, identidades de presupuesto, liquidación y SDF, construcciones
  condicionales de la asignación de la rama con holgura.
- Certificados externos: existencia local del sistema reducido y cotas por
  intervalos. No son por sí mismos teoremas Lean.
- Pendientes: conexión comprobada de la secuencia exacta y las cotas con todas
  las hipótesis, condiciones terminales concretas, optimalidad dinámica,
  equilibrio completo y resultado bancario para leyes generales de pagos.

Ninguno de los 57 resultados del inventario se promueve aquí a cobertura Lean
completa y fiel a la fuente por tener un lema finito o condicional relacionado.
La tabla del artículo registra cobertura integrada, no niega trabajo preliminar.

El procedimiento oficial todavía exige revisar e integrar el artículo, fijar
su commit e identidad y usar el workflow de AppliedModelingLib según el issue.
La integración o publicación requieren la revisión del autor. Una salida cero,
IRF o comprobación numérica no reemplaza ese procedimiento.

## Archivos preparados para continuidad

El punto de entrada es `../CONTINUE_IN_CHAT.txt`. La tarea inicial acotada se
encuentra en `first_target.txt`; registra el argumento que debe comprobarse,
las declaraciones reutilizables y el criterio de cierre.

`checkpoint/README.txt` explica cómo se relaciona la instantánea con
AppliedModelingLib y qué falta para reconstruirla en un compilador remoto.
`checkpoint/checkpoint_manifest.json` identifica cada archivo copiado y sus
dependencias. Se preservan los endpoints incompletos y su alcance explícito.

Los bytes de la fuente privada fijada, notas de exposición, reportes internos,
registros de sesión y cachés permanecen fuera de esta propuesta. La preparación
no vuelve a compilar módulos sin cambios ni acredita nuevas pruebas. La rama
de continuidad está pendiente de revisión antes de cualquier subida.


## Precierre del paper — 25/11/2026

La fuente científica y la versión PDF de referencia se fijan inicialmente en el commit `c52cabde53e67a6a70500b52318c0f1fe84f42f7`. En ese commit, GitHub identifica `paper/paper.tex` con Git blob `033dfbd41ff30eb1c167a4d468cb3751d6fe2d46`. Esta huella **no** es un SHA-256 de los bytes ni un comprobante de nueva ejecución del formalizador oficial. La rama `release/ie-project-entrega-20261125` contiene cambios documentales que no modificaron las proposiciones, el código de simulación ni los archivos Lean de ese commit.

**Inventario de cobertura:** la matriz `paper/lean_crosswalk_57.json` conserva 57 resultados inventariados; 24/57 cuentan con comparación semántica dirigida y 0/57 tienen equivalencia literal completa promovida. Los tres enunciados independientes de `paper/body_compact_after.tex` se registran adicionalmente en `paper/compact_extra_results_3.json` y **no** están cubiertos por la matriz original. Esto impide declarar una formalización integral de los 60 resultados del PDF. La existencia de lemas Lean condicionales compilados sigue siendo evidencia válida exclusivamente para sus enunciados y supuestos.

**Obligación oficial pendiente:** ejecutar o acreditar nuevamente el protocolo de `AppliedModelingLib` desde la versión del paper efectivamente entregada, conservar el commit fijo formalizado y el registro del comando `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast`. Presentar en la tabla del artículo un estado por resultado: demostrado literalmente, demostrado con hipótesis adicionales (especificarlas), o abierto (bloqueo concreto). Si se modifica un enunciado, fijar un nuevo commit y revisar la correspondencia. No presentar las candidatas previas como si fueran una ejecución nueva del flujo oficial.
