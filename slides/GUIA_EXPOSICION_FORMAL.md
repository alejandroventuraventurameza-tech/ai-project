# Guion formal de exposicion - revision tecnica (7 de noviembre de 2026)

**Duracion documentada:** la pauta historica en `slides/topic-notes.md` fue 18 minutos de exposicion y 2 de preguntas para el 7 de octubre. No establece por si sola la duracion vigente de esta defensa. El Beamer nuevo tiene **21 diapositivas**, de las cuales las dos ultimas estan en el anexo: se prepara una version expositiva completa y un recorte si el tiempo vigente sigue siendo de 18 minutos.

## Recorrido completo (diapositivas principales)

1. Problema: la remuneracion de reservas opera por mercado OTC, cartera bancaria y restricciones del capital. Definir desde el inicio que no se modifica rho.
2. Modelo y cronologia: stocks nominales heredados y capital instalado no se confunden con capital elegido para t+1.
3. Firma: derivar presupuesto, colateral robusto y papel de los precios contingentes en la cobertura.
4. Banco y liquidacion: balance pre-pago, exceso despues del pago, mercado interbancario y facilidad.
5. Formacion de tasas: derivar el spread desde el corredor, matching y pendientes chi; explicar por que RL y RD son endogenas.
6. Antecedentes: separar contribucion propia de trabajos que ya conectan dinero, bancos, heterogeneidad y mala asignacion.
7. Experimento: definir S/B, estado de referencia, pago binario, innovaciones futuras, parametros ilustrativos.
8. Regla monetaria: derivar exactamente los coeficientes 0.5, 0.75 y 0.0625 y distinguir shock v_0 de cambio total de RR_0.
9. Sistema reducido: 33 variables y complementariedad escalar; identificar los objetos a_R<0 y b<0 sin afirmar prueba de equilibrio global.
10. IRF financiera: leer tasas y credito por rama, con unidades de puntos basicos o log porcentual. No interpolar con imagenes ficticias.
11. IRF real: capital H, produccion corriente y medida asignativa del periodo siguiente.
12. KKT conjunta: mostrar perturbacion bilateral dk=RL deps, db=Gamma deps, estacionariedad y multiplicador; separar dual construido del almacenado.
13. Tabla de impacto: explicar diferencias S/B y escalas; la respuesta de S en produccion es particularmente pequena.
14. Euler, Phillips y produccion: mostrar ecuaciones encadenadas, signo del termino futuro y la identidad laboral.
15. Produccion al impacto: capital instalado fijo, menor precio del insumo relativo al salario y demanda laboral.
16. Robustez: cambiar T, cierre terminal y tolerancias, sin confundir numeros pequenos con prueba de optimalidad.
17. Alcance: enumerar chequeos numericos, Lean por candidatos y faltas de correspondencia con equilibrio.
18. Conclusion: mismo shock y respuestas asignativas opuestas, pero afirmacion condicionada al sistema reducido.

Las diapositivas finales del **anexo** profundizan en el presupuesto de H y la geometria de los dos conjuntos activos. Usarlas ante preguntas o si el turno final permite mas desarrollo.

## Tres demostraciones esenciales para la defensa

**Banco central -> tasas.** El shock exogeno aparece solo en la regla de RR. El interbancario obedece a la posicion relativa de deficits y excedentes; RL=RR+chi_bar en el regimen interior. El signo total de RL debe verificarse sobre la solucion, no imponerse.

**Tasacion del colateral -> inversion H.** Con restriccion activa, RL*b=Gamma*k y sin deposito, k_next=(N-c)/(q-Gamma/RL). Diferenciar la identidad muestra que credito y capital pueden moverse en sentidos opuestos, especialmente si cambian N-c y el valor pignorable.

**Precios y empleo.** La regla de depositos entra a Euler; la dinamica futura de precios entra a NKPC; la condicion laboral entrega Delta log Y_0=(Delta log m_0-Delta log Cw_0)/3. Las contribuciones cuantitativas son contables sobre una solucion conjunta; no experimentos causales separados.

## Objeciones que hay que contestar

- El shock es a **remuneracion de reservas**, no a encaje obligatorio.
- Se trata de parametros ilustrativos y un choque muy pequeno; no es una estimacion del Peru.
- Los 71 candidatos Lean certificados no prueban los 57 enunciados exactos del paper ni el equilibrio dinamico completo.
- El cierre T=640 es una comparacion finita; no es una condicion terminal analitica exacta.
- Las respuestas del capital elegido t+1 y de la produccion corriente t no miden el mismo margen.
- La cantidad de credito puede aumentar mientras la restriccion se endurece economicamente; atender al dual y a recursos propios.
- No se ha demostrado un criterio unico para seleccionar S o B. Un grafico no prueba multiplicidad formal.

**Ensayo:** cronometro y revision visual de todas las paginas PDF en pantalla o proyector. Mantener en reserva las diapositivas tecnicas, no eliminar demostraciones por intuicion.
