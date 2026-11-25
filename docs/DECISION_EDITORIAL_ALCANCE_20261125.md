# Decisión editorial de alcance para el paper (candidato, 25/11/2026)

**No ejecutada:** no se cambió paper/paper.tex, paper/paper.pdf ni la formalización Lean. La consigna oficial requiere derivaciones manuscritas de todos los resultados que permanezcan en el paper y una tabla Lean por resultado numerado.

## Diagnóstico

El PDF actual tiene 12 páginas de cuerpo dentro del límite de 8–20, pero 145 páginas totales por un dossier histórico. Contiene 57 resultados del inventario original y 3 resultados propios añadidos al cuerpo compacto: **60 resultados distintos**. Las cinco derivaciones manuscritas iniciales no cubren todo lo exigible.

## A. Conservar el dossier de 60 resultados

Ventaja: no se pierde nada del artículo histórico. Desventaja: exigiría mucho material manuscrito adicional y cotejos Lean que no se han realizado; antes del 26 de noviembre sería razonable anticipar una entrega parcial con brechas explícitas y no presentarla como completa.

## B. Alternativa recomendada: paper compacto evaluable + archivo histórico separado

1. Archivar íntegra la versión de 145 páginas como material histórico distinto del paper sometido, con sus fuentes y hashes, sin borrar la investigación.
2. Mantener el cuerpo compacto de 12 páginas con la Proposición 4.2 y los tres resultados de paper/body_compact_after.tex.
3. Incorporar un apéndice acotado con cuatro resultados del dossier histórico que corresponden a las notas del iPad: Lemmas 3.1 y 3.2, Proposición 3.3 y Lema 4.3. Así el paper tendría **ocho** resultados únicos: cuatro del cuerpo y cuatro del apéndice. La Proposición 4.2 está ya en el cuerpo.
4. Añadir tabla Lean de ocho filas y registro de IA, cada prueba marcada como demostrada, demostrada bajo hipótesis adicionales o abierta, con bloqueo y commit específicos.
5. Incorporar manuscritos auténticos de los ocho resultados, incluidos los tres adicionales del cuerpo, sin equiparar una guía tipografiada con un escaneo real.
6. Regenerar desde LaTeX el PDF definitivo, verificar el límite de páginas del cuerpo y revisar la atribución correcta del capítulo 3 de Céspedes et al. (2016).
7. Ejecutar las compuertas finales de código, PDF y Lean que se puedan acreditar sin agotar presupuesto; registrar los límites no comprobados. Fusionar solo un candidato coherente en main antes del plazo.

## Precauciones

El resultado de dos raíces es **condicional y escalar**, no una prueba de dos equilibrios SOURCE infinitos. La posibilidad de archivar pruebas históricas fuera del paper no convierte las ocho pruebas nuevas en Lean kernel-verified por defecto.

Esta propuesta queda **sin adoptar** porque cambiar el alcance del artículo exige recompilación y correspondencia de fuentes, además de preservar la versión histórica. No se subirá un PDF recortado manualmente que no corresponda a paper.tex.
