# Cotejo provisional del Lema A.1.4 — fuente vigente frente a formalización histórica

**Artículo sometido:** `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`, `paper/appendix_eight_results.tex` líneas 115–145, etiqueta `lem:allocation_loss_identity`.

**Módulo histórico localizado:** `lean/candidates/Ventura26LiquidityAllocation/PaperLemma43SourceCompleteCandidate.lean`; `sourceLemma43CompleteSpec` y `sourceLemma43CompleteSpec_proved`. **Compilación kernel real:** GitHub Actions [#45847597337](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847597337), paso `COMPILED PaperLemma43SourceCompleteCandidate`. `#print axioms`: `[propext, Classical.choice, Quot.sound]`; sin `sorryAx`.

## Comparación material de las cláusulas

| Enunciado del PDF | Qué acredita el módulo histórico |
|---|---|
| Cobb-Douglas de dos tipos `Y_i=A_i k_i^α ℓ_i^β`, masas positivas, `α,β,d>0` y `α+β+d=1` | Define `Y_H,Y_L` a partir de capital, empleo y productividades de cada tipo con esos mismos dominios |
| Empleo óptimamente asignado y agregado `G` | Cláusulas 1, 2 y 7: empleo positivo, satisface recurso laboral, domina todas las distribuciones laborales factibles y genera `Y=L^βG^(1−β)` |
| Referente eficiente `Yeff=K^α L^β ZA^d` | Cláusulas 3 y 4: es cota global para toda reasignación factible de capital y trabajo, con construcción que la alcanza |
| Pérdida `ℒ=log(Yeff/Y)≥0` | Cláusulas 5–6: `0≤log Yeff − log Y` y fórmula desarrollada del log de pérdida. **Puente autónomo ya demostrado:** `log(Yeff/Y)=log Yeff−log Y` y no negatividad para `0<Y≤Yeff`, en `lean/current/CurrentCompactLogLossBridge.lean`, compilado en [Actions #45855571576](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45855571576) sin `sorryAx` |
| `dℒ=α(κ_H−ω_H)d log(k_H/k_L)` para trayectorias diferenciables positivas | Cláusulas 8–9: derivadas de la expresión de pérdida y del logaritmo de la razón de capitales, con derivadas de ambas trayectorias al instante estudiado |
| `ω_H>κ_H` si y solo si `MPK_H>MPK_L` al empleo óptimo | Cláusulas 10–11: identifica la proporción física de producto de H y su equivalencia con `αY_H/k_H>αY_L/k_L` |

## Veredicto delimitado

Existe **una integración histórica de alcance muy cercano al lema vigente y compilada por Lean**, no únicamente identidades auxiliares. Debe corregirse cualquier diagnóstico que diga que *solo* estaban formalizados la identidad algebraica del diferencial y la ordenación de MPK.

**Todavía no declarar equivalencia fuente–Lean íntegra ni un quinto resultado formalizado:** el sublema logarítmico cuenta ahora con `currentCompactLogLossSpec` y `currentCompactLogLoss_exact` verificados en Lean, pero **aún falta integrarlo formalmente con las once cláusulas históricas en un Spec del lema A.1.4 que reproduzca el enunciado compacto**, además de confirmar nombres, hipótesis y estructura fuente mediante auditoría independiente. Tampoco acredita dos equilibrios dinámicos ni causalidad de la IRF.

La matriz general `lean/RECONCILIACION_ACTUAL_8_20261126.md` debe leerse junto con esta actualización más precisa.
