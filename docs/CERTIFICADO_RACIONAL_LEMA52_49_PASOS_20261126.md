# Lema 5.2: certificado racional de 49 pasos

**Fuente congelada:** `paper/body_compact_after.tex` en `bac3c6255da39cd1169a965df35bb5e9a230e6e8`, `lem:compact_robust_tail_power`.
**Matriz:** 36 cadenas decimales de `code/irf/inputs/rational_preconditioners.json`, SHA256 `d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94`.

## Construcción exacta

Fijar `S=10^12`, `D=10^4`, `F=F0`. Para cada `0≤n≤48` calcular, con fracciones exactas:

```
M_n = floor(S * ||F^n||_infinity) + 1
B_0 = S
B_n = M_n + ceil(sum_{j<n}(M_j*B_{n-1-j}) / (D*S)), 1≤n≤48
```

Se obtienen las desigualdades **racionales estrictas** `||F^n||∞<M_n/S` y las desigualdades enteras de recurrencia

```
D*S*B_n ≥ D*S*M_n + sum_{j<n} M_j*B_{n-1-j}.
```

Los enteros del certificado están en `lean/current/CurrentCompactRobustFiniteCertificate.lean`; el script independiente `code/irf/check_lean_robust_majorants.py` recalcula las 98 cifras desde las cadenas de origen y rechaza cualquier discrepancia. Las 49 potencias se multiplican como fracciones: **no se utilizan flotantes para aceptar resultados**.

| Variable | Cota estricta |
|---|---:|
| `||F0^48||∞` | `<0.955246892194` |
| `B_48/S` | `0.972103438404<49/50` |
| `max_{r<48} B_r/S` | `6.105134003467<7`, en `r=7` |

## Argumento general de robustez

Si `||A−F||∞≤1/10000`, la identidad no conmutativa telescópica implica

```
||A^n||∞ ≤ ||F^n||∞ +
  (1/10000)*sum_{j<n} ||F^j||∞ * ||A^(n−1−j)||∞.
```

Una inducción fuerte **únicamente para 0≤n≤48** da `||A^n||∞≤B_n/S`. Entonces, usando `k=48m+r` y la submultiplicatividad, se sigue

```
||A^k x||∞ ≤ 7*(49/50)^floor(k/48)*||x||∞.
```

No se necesita extender artificialmente la tabla de mayorantes a horizontes infinitos; 49 potencias bastan.

## Evidencia y obligaciones

**DEMOSTRADO previamente en Lean:** identidad telescópica, desigualdad de norma y decaimiento por bloques condicionado a cotas finitas, en [Actions #45866200744](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45866200744).

**NUMÉRICO exacto:** listas de 49 valores `M_n` y `B_n` verificadas contra el JSON original por Python; el efecto del redondeo solo ensancha cotas.

**Compuerta matemática CUMPLIDA:** `finiteSourceRowsVerified`, `finiteRobustStepVerified`, `finiteRobust48Verified` y `finiteRobustTransientVerified` aprobaron `decide +kernel`. La inducción y el traslado a norma real respaldan `lemma52_decimal_finite_norms` y `lemma52_decimal_current_exact`; [Actions #45871289804](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45871289804), sin `sorryAx`, únicamente axiomas fundacionales. **No** equivale a resolver la identidad del Jacobiano SOURCE.

**No demostrado por esta cota:** que F0 sea exactamente el Jacobiano de las 34 filas SOURCE, existencia de equilibrio infinito, TVC, crecimiento permanente o la correspondencia paper-scoped oficial. Los ocho handnotes personales auténticos siguen sin incorporarse.
