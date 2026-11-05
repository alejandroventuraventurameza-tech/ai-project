# Política monetaria, liquidez bancaria y asignación de capital

**Alejandro Ventura · AI Econ Modeling, UP 2026-II · Track B**

Repositorio público: https://github.com/alejandroventuraventurameza-tech/ai-project

Consigna: https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7

## Pregunta y entorno actual

¿Cuándo una intervención monetaria que pasa por liquidación interbancaria y
bancos comerciales facilita capital a empresas productivas, y cuándo empeora
la asignación? V0-M es una economía neokeynesiana cerrada con dos tipos de
empresarios, acumulación de capital y patrimonio, promesas nominales, garantía
robusta a estados futuros y riesgo agregado recurrente acotado. El banco central
dispone de remuneración y cantidad de reservas, encaje y amplitud del corredor.

Se conserva la multiplicidad: una misma expansión y los mismos estados
heredados admiten dos ramas locales. Las dos soluciones reducidas del experimento reducen la tasa de préstamo y
aumentan crédito de H; la pérdida asignativa disminuye en S y aumenta en B
en el testigo y bajo las hipótesis declaradas. Los resultados son locales y
condicionales. No se infiere bienestar de la pérdida de producción condicional.

El laboratorio estático A y los modelos de dos fechas conservan sus propios
supuestos. Su costo bancario cuadrático es una simplificación propia, no una
ecuación atribuida a Bianchi y Bigio. El antecedente principal de firmas es
González, Nuño y Thaler, **enero de 2026, tres autores**. La relación general
entre política monetaria y mala asignación ya existe en esa literatura; no se
presenta como nuestra novedad.

## Archivos y estado

| Componente | Estado |
|---|---|
| `paper/paper.tex` y `paper/paper.pdf` | Versión extensa para revisión, con estructura oficial; aún sin compactar |
| `paper/result_ledger.json` | 57 resultados retenidos; campaña Lean preliminar separada, sin cobertura integrada completa |
| `code/verify.py` | Reproduce el laboratorio A, seis bloques V0-M e IRF de ambas ramas |
| `code/v0m/` | Cálculos, entradas matemáticas y certificados; sin datos reales |
| `proposal/` y `slides/topic.*` | Entrega histórica del tema, integrada mediante PR #1 |
| `slides/final.*` | Borrador de exposición NK con IRF internas y pendientes explícitos |
| `lean/` | Estado y límites de campaña preliminar; integración oficial pendiente |
| Apéndice manuscrito personal | Pendiente del autor |
| IRF internas | Reproducibles en `code/irf/`; equilibrio completo aún no validado |
| Calibración y validación externa | Pendientes; sin datos reales |

La reducción al rango final de páginas se hará después de revisar el contenido.
La revisión interna acotada de 30 argumentos, incluidos los 14 del cuerpo,
no equivale a una auditoría integral o cobertura formal de los 57 resultados.

## Reproducción

Con Python 3.12 o posterior:

```sh
python -m pip install -r code/requirements.txt
python code/verify.py
```

La ejecución falla si un certificado o la correspondencia del inventario con
el artículo no pasa. Los alcances se detallan en `code/v0m/README.md`.
Son comprobaciones internas; no constituyen pruebas Lean o evidencia causal.

Compilación desde `paper/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

Los PDF de la plantilla se versionan. El flujo oficial
`.github/workflows/build.yml` se conserva sin cambios. La revisión del artículo
y su PDF precede a cualquier nueva integración y a fijar el commit para
AppliedModelingLib. La guía de exposición y los registros personales de trabajo
permanecen fuera del repositorio. El enlace público ya fue publicado en el
issue; la preparación actual sigue pendiente de revisión.

## Entrega con IRF internas — 2 de noviembre

- [Artículo y figuras](paper/paper.pdf): sección de respuestas dinámicas internas.
- [Diapositivas](slides/final.pdf): borrador para revisión y ensayo.
- [Reproducción y unidades](code/irf/README.md).
- [Auditoría numérica](code/irf/output/delivery_audit.json).

El ejercicio usa una innovación de −0.1 pb en la regla de remuneración de reservas,
prefijo no lineal y cola local lineal. Conserva ambas ramas. La pérdida asignativa
cae en S y sube en B; la producción cae inicialmente en ambas. Son resultados
condicionales del sistema reducido con parámetros ilustrativos, no evidencia
causal ni IRF de un equilibrio completo ya verificado. El cierre fiscal literal,
las condiciones terminales y la optimalidad siguen en proceso de integración.
Las afirmaciones generales y pruebas escritas del desarrollo deben distinguirse
del alcance comprobado del ejercicio computacional.
