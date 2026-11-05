# Estado de formalización y alcance de esta entrega

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
