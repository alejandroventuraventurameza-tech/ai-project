# Lean plan — no formalization claimed yet

The topic delivery does not require a completed Lean run. First finish and merge
the version of `paper/paper.pdf` that will be formalized, then record its exact
commit. Do not formalize an unpinned or changing manuscript.

Run from an updated AppliedModelingLib clone, following the course issue and its
paper-formalization skill, using `gpt-5.6-sol` with reasoning effort `xhigh`.
Folder: `Ventura26ReservesAllocation`. Target every numbered result of the paper,
initially the two-constrained allocation identity, its finite-difference sign,
and the mixed-regime comparative static. Audit the paper once, then work from
the audited statements and precise source locations. Avoid empty abstract
predicates and hypotheses that assume the conclusion. Compile until the intended
results close or report the exact remaining blocker; no `sorry` in proved results.

```text
Please formalize my own paper, an unpublished manuscript with no arXiv record:
https://github.com/alejandroventuraventurameza-tech/ai-project/blob/<commit>/paper/paper.pdf
(pinned at commit <commit>), using the paper-formalization skill and workflow
in this repository. Use Ventura26ReservesAllocation as the paper folder.
```

`<commit>` must be filled with the actual merged paper commit before execution.
The economic assumptions must match the paper: positivity, fixed capital,
unchanged financial regime, underallocation when claiming an efficiency gain,
and no crossing of the efficient allocation for a finite intervention.

From the AppliedModelingLib root run and retain:

```text
python3 scripts/paper_contribution.py check Ventura26ReservesAllocation --fast
```

Copy the entire generated `papers/Ventura26ReservesAllocation/` folder exactly
into `lean/`, preserving audit artifacts and partial results. Respect the generated
`.gitignore`; never force-add ignored artifacts. Map each numbered paper result
to its Lean declaration, file, status, added assumptions (if any), and paper commit.
Repeat the workflow after changing any proposition. Any separate handwritten or
independent Lean exploration must be identified as such and cannot stand in for
the required generated run. No run, declaration, proof fragment or successful check
is asserted for this topic delivery.
