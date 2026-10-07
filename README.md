# Reservas bancarias, colateral y asignación de capital

**Alejandro Ventura · AI Econ Modeling, UP 2026-II · Track B (modelo de tesis)**

Repositorio público: https://github.com/alejandroventuraventurameza-tech/ai-project
Consigna: https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7
Tema: 7 de octubre, 08:20 (Lima); entrega en main antes de 07:30.
Presentación final: 30 de octubre, 07:30 (Lima). Artículo: 26 de noviembre, 22:00.

## Pregunta y modelo

¿Cuándo una expansión de reservas mejora la asignación de capital entre empresas
heterogéneas en productividad, patrimonio y colateral? A es el núcleo estático
demostrable; B es la extensión objetivo de la presentación final. Ambos siguen Track B.

Un banco elige crédito B y depósitos D, con B+m=D+E y costo propio
C=cB+κ(δD−m)₊²/2. Las empresas maximizan Aᵢkᵢ^α−tbᵢ+ρ(nᵢ−xᵢ),
sujeto a Rkᵢ=xᵢ+bᵢ, 0≤xᵢ≤nᵢ y tbᵢ≤hᵢ. R ajusta para k_H+k_L=K.
Supuestos: A_H>A_L>0, 0<α<1, nᵢ,hᵢ,K>0, t>ρ>0, κ>0,
0<δ<1, c≥0, E≥0 y balance bancario factible. El costo cuadrático es una
simplificación propia, inspirada por la importancia de la liquidez bancaria,
sin atribuir su forma a Bianchi y Bigio.

## Resultados candidatos y condiciones

En liquidez escasa, más reservas reducen t dentro de los regímenes estudiados,
incluyendo la respuesta endógena del crédito. Con reservas abundantes son neutrales.
Si H está estrictamente limitada y L se autofinancia en el interior, una caída
local de t eleva k_H y producto y reduce la brecha de MRPK y la pérdida 1−Y/Y*.
Se mantienen K y primitivas y no se cambia de régimen.

Si ambas están estrictamente limitadas,
k_H=K(tn_H+h_H)/[t(n_H+n_L)+h_H+h_L]. Al caer t, H recibe más capital
si y solo si h_H/n_H>h_L/n_L. Eso mejora eficiencia únicamente si H estaba
subcapitalizada y la intervención no sobrepasa la asignación eficiente.
La igualdad de ratios es neutral; el orden inverso cambia el signo.

El antecedente principal es González, Nuño y Thaler (enero de 2026), que reconoce
el aporte previo de Albrizio. Ya estudia política monetaria y mala asignación.
La novedad del cierre particular sigue bajo revisión. EEA/ENAHO
son motivación descriptiva: no identifican efectos monetarios causales.

## Estado y reproducción

| Componente | Estado |
|---|---|
| Propuesta y slides de tema | Preparadas para revisión; fuentes y PDF en proposal/ y slides/topic.* |
| Simulaciones | `python code/verify.py`; biblioteca estándar, semilla fija y errores fatales |
| Artículo y slides finales | Borradores propios preliminares, no entrega final de 8–20 páginas |
| Lean | Pendiente de fijar artículo en commit y ejecutar AppliedModelingLib |
| Apéndice manuscrito | Pendiente de elaboración personal |
| Integración y comentario del issue | Pendientes de revisión de PDF y Actions verde |

Compilar desde cada carpeta con `pdflatex` (o `latexmk -pdf`), usar `bibtex`
en propuesta y artículo y repetir `pdflatex` dos veces. Los cuatro PDF se
versionan. `.github/workflows/build.yml` conserva el flujo oficial.
El plan Lean y sus controles están en `lean/README.md`. Las fuentes y el alcance
de la búsqueda bibliográfica están en `research-audit.md`; los prompts originales
y respuestas relevantes permanecen en `prompts.md`.
