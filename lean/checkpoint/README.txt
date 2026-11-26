CHECKPOINT LEAN PARA CONTINUIDAD — PROPUESTA PARA REVISIÓN
Autor: Alejandro Ventura. Preparado el 5 de noviembre de 2026.

Esta carpeta conserva los módulos preliminares de nuestro proyecto dentro de
AppliedModelingLib. No es una formalización completa ni una nueva corrida oficial.
La copia no altera los bytes de los módulos y no modifica el clon original.

CONTENIDO
- modules/Ventura26LiquidityAllocation/: FinancialCore, EconomicModel,
  MainTheorems, Assumptions, PaperInterface y ProofInterface.
- module_root.lean: import raíz original. Importa ProofInterface, que mantiene
  endpoints abiertos; no usar su mera compilación como prueba de cierre.
- dependencies/: toolchain, revisiones de dependencias y registro Lake original.
- checkpoint_manifest.json: ruta de restauración y SHA256 de cada copia.
- UPSTREAM_LICENSE: licencia del repositorio base.

RECONSTRUCCIÓN FUTURA EN UN EJECUTOR
Base: https://github.com/nikhgarg/AppliedModelingLib
Commit: 194edcc95df74806a39b961d10dedddc6e730cce
Toolchain: leanprover/lean4:v4.30.0-rc2
La base upstream no contiene nuestros módulos, que eran cambios locales.
Se debe reconstruir el clon fijado y copiar únicamente las rutas explícitas
del manifest a sus destinos. Esta carpeta no contiene todo AppliedModelingLib,
Mathlib ni los artefactos compilados, y no es un proyecto Lake autónomo.
El registro Lake incluye otros targets upstream: una comprobación acotada debe
seleccionar expresamente el módulo del proyecto, sin lanzar el build global.
No se ha instalado ni configurado un ejecutor remoto en este paso.

ALCANCE
El último checkpoint inspeccionado registra pruebas auxiliares, construcción
literal de la rama S e implicaciones de factibilidad bajo premisas explícitas.
La secuencia exacta y cotas externas todavía deben conectarse con esas premisas.
Permanecen abiertos terminalidad aplicada, suficiencia dinámica, instancia
completa de equilibrio y el resultado de pagos con leyes generales.
Se conservan ambas ramas; el caso finito es el alcance numérico autorizado.
ProofInterface conserva 56 ocurrencias de sorry en esta instantánea. Eso no
invalida automáticamente los helpers que no los importan, ni acredita cobertura
completa del artículo. Los resultados y sus cierres de axiomas requieren una
comprobación dirigida con Lean, no un conteo textual de huecos.

FUENTE
La campaña preliminar usó una fuente fija distinta del artículo actualizado
con IRF. Su SHA256 se conserva en el manifest; los bytes de la fuente privada
no se exportan. paper/paper.tex es el artículo de desarrollo disponible aquí,
pero no debe atribuirse a él la cobertura de aquella fuente sin una comparación.
Los reportes de revisión y registros de sesión privados tampoco se exportan.

ESTADO DE ESTA PREPARACIÓN
Se comprueban identidad de copias y configuración, no se repiten pruebas ni
se promueve ningún resultado a demostrado. La publicación sigue pendiente de
revisión del autor. No hubo commit, push, PR ni integración en main en este paso.
