# Research audit — 7 October 2026

Author: Alejandro Ventura. Names in inherited notes do not determine authorship.

**Selected baseline:** January 2026 manuscript, as explicitly requested by
Alejandro after attaching the new version. Local PDF: 173 pages, authors
González, Nuño and Thaler; acknowledges Albrizio's earlier contribution.
SHA-256: `51d37bd1d02dfc9411f0c6c3bea6c4faf5a87e56f1082a97369898b834d527ff`.
All active equations/proposition citations refer to this version: eq. (4),
printed p. 7 (PDF p. 8); eq. (6), printed p. 8 (PDF p. 9); Proposition 1,
printed p. 19 (PDF p. 20); Proposition 2, printed pp. 20–21 (PDF pp. 21–22);
proofs B.7.1–B.7.2 (B.7 starts on printed p. 65, PDF p. 66).
The 2023/2021 material below is historical search context, not the active baseline.

## Course and repository

- Read issue #7 in full: https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7
- Official schedule confirms the topic slot on 7 October, 08:20–08:40 Lima,
  and the final slot on 30 October, 07:30–08:15. The issue's special 07:30
  deadline on 7 October overrides the general evening-before rule.
- Initial local HEAD: chore/install-course-template, 1887d692567123863c27121f90de4d3ee016e2b2.
  Working tree clean. main and feat/topic-presentation initially at 58103dc.
- Official template provenance in the inherited prompts: 06d219c1c1aae587616b13a938c1b33ad2884e37.
  feat/topic-presentation was fast-forwarded to the installed template. main was not edited.
- Public repository ai-final-project was renamed ai-project via GitHub API;
  origin was updated. Initial issue-comment audit found no submission URL from
  the author. Comment must be posted after approved merge and verification of main.

## Sources actually inspected

1. Initially local González, Nuño, Thaler and Albrizio manuscript: first version October
   2020, inspected version October 2023, 114 PDF pages. Printed pp. 7–8:
   eq. (4), q_t k_t ≤ γ q_t a_t, and static profit problem (6); pp. 20–21:
   Propositions 1 and 2 (distribution slope at fixed cutoff and cutoff at fixed
   distribution). Proofs are in Appendix B.8; page numbers refer to the 2023 version.
   These are conditional dynamic statements; our static propositions are not
   advertised as reproductions of them. Local path remains outside this repo.
   Public version: https://www.bis.org/publ/work1148.pdf
   During this session the research PDF at the same local path changed to the
   January 2026 manuscript (173 pages, three authors; modified at 03:40 Lima).
   The initial 2023 text extraction was retained in the parent temporary folder.
   Following the user's steering, active academic citations now use January 2026.
   Earlier 2023 locations are kept only as the search history.
2. BdE Working Paper 2145, 2021: title/abstract and mechanism contrast from the
   official paper and official 2022 research summary. No comprehensive audit
   of the 2021 appendices was performed.
   https://www.bde.es/f/webbde/SES/Secciones/Publicaciones/PublicacionesSeriadas/DocumentosTrabajo/21/Files/dt2145e.pdf
3. January 2026 revision: title, abstract, introduction, author/version note,
   firm problem (4)–(6), Propositions 1–2 and their proofs B.7.1–B.7.2.
   Three authors: González, Nuño and Thaler. The note acknowledges Albrizio's
   contribution to an earlier empirical version, removed in this revision.
   The author's research page lists revision requested at JPE, not a published
   article. Do not conflate versions or transfer page numbering.
   https://www.galonuno.com/uploads/1/3/4/6/134687692/aer_2026.pdf
   https://www.galonuno.com/research.html
4. Local Bianchi–Bigio file in published_papers is actually the March 2021
   manuscript (74 PDF pages). Section 2, printed p. 6 (PDF p. 7), eqs. (2)–(3)
   describes portfolio budgeting and capital requirements; the following
   balancing stage describes deposit transfers settled with reserves.
   Published reference: Econometrica 90(1), 2022, pp. 391–454,
   https://doi.org/10.3982/ECTA16599.
   Our quadratic shortfall cost is our own approximation. It is not their cost
   function, a replication of their OTC equilibrium or their pass-through proposition.
5. Related/citing literature search located A tale of two margins: Monetary
   policy and capital misallocation, European Economic Review (2026).
   https://www.sciencedirect.com/science/article/pii/S001429212600022X
   The introduction explicitly relates to González et al. This source was
   screened for scope, not exhaustively derived. Citation search remains partial.

## Scope of contribution and empirical evidence

Monetary policy and misallocation already occur in the closest paper. Proposed
contribution: transparent conditions for liquidity-cost transmission to relative
capital under terminal-payment collateral, fixed aggregate capital and two
financial regimes. No claim of exhaustive novelty verification.
The baseline has a continuum of constant-returns firms and wealth-distribution
dynamics. Our A has two decreasing-returns firms, exogenous terminal collateral
and fixed capital; it does not replicate their dynamics or Ramsey problem.
Their m_t is the input's real price and R_t the real capital cost. Our m is
bank reserves and R the initial rental price; the notation is not interchangeable.

Read CONTEXT.md, METODO_LECTURA.md, TAREAS.md, notas_bigio.md and the markdown
cells of misallocation_eea_2023.ipynb and hechos_estilizados_real_2025.ipynb.
Inherited notebooks include interpretive claims and preliminary TFP numbers;
none is imported as a validated causal estimate, calibration or a confirmed
financial constraint. No microdata, research-paper PDFs or environments are copied.

## Mathematical audit

- R is the initial rental price; t is gross debt repayment, rho the gross
  opportunity return. They cannot be interchanged with a net interest rate.
- h_i is exogenous pledgeable terminal wealth, not endogenous q k_i collateral.
- Opportunity cost of own funds is explicit. With t>rho, borrowing to save is
  dominated and all four firm regimes must be distinguished.
- R clears fixed K. Comparative statics at fixed R do not prove reallocation.
- With both caps, the h/n inequality establishes direction only. Efficiency
  additionally requires the initial MRPK ordering and no crossing of k_H*.
- Banking transmission includes B(t). In the two relevant regimes B'<0,
  so the equilibrium derivative denominator is positive. Nonnegative deposits,
  an interior bank, scarce reserves and unchanged firm regimes are required.
- Reserve abundance, equal collateral ratios and adverse allocations are
  checked separately. Active reserve requirements and t=rho are outside the
  strict interior arguments.
- Numerical verification does not certify global equilibrium existence with
  every extension, a full monetary equilibrium, Lean proofs or causal evidence.
