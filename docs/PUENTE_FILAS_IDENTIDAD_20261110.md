# Puente parcial: dieciseis filas de identidad SOURCE/Python (10-XI-2026)

**Alcance:** `code/irf/audit_source_identity_row_candidates.py` coteja expresiones **transcritas** de ocho familias de `localReducedRemainingResidual`, cada una en fecha 0 y fecha 1. Son 16 posiciones distintas en el vector de 33. Este informe no declara equivalencia economica completa de los operadores Lean y Python.

## 1. Contrato matematico

Sea `F_source` el vector literalmente definido en `EconomicModel.lean`. Sea `G_python` el prefijo de `finite_irf.py`. Para indices `I`, la afirmacion fuerte pendiente es

```text
G_python(z, v)[p(i)] = F_source(psi(z), v)[i], para i en I
```

en una vecindad positiva, con correspondencia `psi` de estados, historia, parametros, agregados, pagos y precios. **Esto no esta demostrado.** El auditor prueba una afirmacion mas debil:

```text
G_python(z, v)[p(i)] ~= F_transcrito(z, v)[i]
```

`F_transcrito` esta implementado separadamente de `remaining_residuals`, pero llama a las mismas funciones `auxiliary`, `production` y `steady_case`. Comparte supuestos y posibles errores de esos auxiliares. La coincidencia de valores y diferencias centrales no prueba igualdad de operadores SOURCE reales.

## 2. Dieciseis filas candidatas

| Familia | SOURCE (t=0, t=1) | Python (t=0, t=1) | Identificacion aun necesaria |
|---|---|---|---|
| Oferta de capital | 7, 23 | 7, 23 | inversion y capital agregado |
| Recursos | 8, 24 | 8, 24 | masas, producto, ajuste y costes |
| Phillips Rotemberg | 11, 27 | 11, 27 | SDF y coeficiente 150 |
| Regla tasa reservas | 12, 28 | 12, 28 | rezagos, persistencia, innovacion |
| Regla cantidad reservas | 13, 29 | 13, 29 | cantidades y calendario |
| Precio OTC credito | 14, 30 | 14, 30 | pendiente media OTC |
| Precio OTC depositos | 15, 31 | 15, 31 | pagos, pendiente y ratio de reserva |
| Balance bancario | 16, 32 | 16, 32 | prestamos, depositos, patrimonio |

Las 16 posiciones son **candidatas de factor +1**, no teoremas de equivalencia del operador. Se prueban cinco intervenciones de cuatro instrumentos, tres coordenadas (incluidas dos perturbaciones fuera de la raiz), ambas ramas y todas las 33 columnas mediante diferencias centrales. Las pruebas no ejecutan Lean.

En combinacion con las nueve filas de escalas previas `{4,5,6,9,10,21,22,25,26}`, hay **25 de 33 posiciones con candidato de transformacion**, pero ninguna matriz 33x33 completa certificada. Las ocho pendientes son `{0,1,2,3,17,18,19,20}`: presupuestos y Euler de empresas. Exigen correspondencia de riqueza, rostros, garantias y operaciones de fila, no simple factor +1.

## 3. Reproduccion y obligaciones

Ejecutar desde raiz:

```bash
python code/irf/audit_source_identity_row_candidates.py
```

El reporte `code/irf/output/source_identity_row_candidates.json` registra SHA-256, errores numericos, conteos y banderas expresas de certificaciones NO establecidas. Estatus: **NUMERICO/CONDICIONAL**, incluso con CI verde.

Proximas compuertas: (a) identificar `LocalPrefixDateData` contra `auxiliary`, parametrizacion y distribucion de shocks; (b) demostrar la correspondencia de las 16 filas SOURCE; (c) construir shears de las ocho filas de firmas y carta `psi`; (d) certificar el jacobiano completo e inverso en un dominio; (e) demostrar optimalidad, TVC y equilibrio dinamico completo independientemente. La ecuacion 34 del dual L es de frontera S/B, no una condicion del interior vinculante.

**No fusionar PR #2 a main**. El resultado solo se declara ejecutado al observar CI del SHA exacto.
