"""Reproduce branch-conditional IRFs, sensitivity checks, tables and figures."""
from pathlib import Path
import csv
import hashlib
import json
import math
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
OUT = HERE / "output"
FIG = REPO / "paper" / "figures"


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def experiment(name, *args):
    target = OUT / name
    result = subprocess.run([sys.executable, "-B", "-X", "utf8",
        str(HERE / "finite_irf.py"), "--output", str(target), *args],
        capture_output=True, text=True, encoding="utf-8")
    require(result.returncode == 0, result.stderr[-4000:])
    report = json.loads((target / "finite_irf_validation.json").read_text())
    with (target / "finite_irf_paths.csv").open(newline="", encoding="utf-8") as f:
        paths = list(csv.DictReader(f))
    require(all(math.isfinite(float(v)) for row in paths for k, v in row.items()
        if k not in ("branch", "period_unit") and v != ""), "Nonfinite path")
    return report, paths


def draw(paths):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    FIG.mkdir(exist_ok=True)
    panels = {
        "irf_transmission": [
            ("reserve_rate", "Remuneración de reservas", "pb", 10000),
            ("interbank_rate", "Tasa interbancaria", "pb", 10000),
            ("loan_rate", "Tasa de crédito", "pb", 10000),
            ("credit_H", "Crédito de H", "log %", None),
            ("credit_L", "Crédito de L", "log %", None),
            ("reserves_pre", "Reservas antes de pagos", "log %", None)],
        "irf_real_allocation": [
            ("capital_next_H", "Capital elegido de H para t+1", "log %", None),
            ("capital_next_L", "Capital elegido de L para t+1", "log %", None),
            ("output", "Producción corriente", "log %", None),
            ("labor", "Trabajo corriente", "log %", None),
            ("inflation", "Inflación bruta", "pb", 10000),
            ("conditional_misallocation_loss", "Pérdida asignativa condicional en t+1", "100 × diferencia log", 100)]}
    plt.rcParams.update({"font.size": 9, "axes.spines.top": False,
                         "axes.spines.right": False, "pdf.fonttype": 42})
    for filename, group in panels.items():
        fig, axes = plt.subplots(2, 3, figsize=(11.5, 6.3), constrained_layout=True)
        for ax, (key, title, unit, scale) in zip(axes.flat, group):
            ax.axhline(0, color="#999999", linewidth=.7)
            for branch, color, style, label in [
                ("slack", "#1769aa", "-", "S: L con holgura inicial"),
                ("binding", "#bc432d", "--", "B: L restringida inicialmente")]:
                rows = [r for r in paths if r["branch"] == branch and int(r["period"]) <= 20]
                values = [float(r[key + ("_log_deviation_pct" if scale is None else "_deviation")])
                          * (1 if scale is None else scale) for r in rows]
                ax.plot([int(r["period"]) for r in rows], values,
                        color=color, linestyle=style, linewidth=1.7, label=label)
            ax.set_title(title, fontsize=9)
            ax.set_xlabel("Período del modelo")
            ax.set_ylabel(unit)
            ax.grid(alpha=.15)
            ax.ticklabel_format(axis="y", style="sci", scilimits=(-3, 3), useOffset=False)
        handles, labels = axes.flat[0].get_legend_handles_labels()
        fig.suptitle("Innovación de −0.1 pb en la regla de remuneración de reservas", fontsize=12)
        axes.flat[0].legend(handles, labels, fontsize=7, frameon=False)
        fig.savefig(FIG / (filename + ".pdf"))
        fig.savefig(FIG / (filename + ".png"), dpi=160)
        plt.close(fig)


def main():
    OUT.mkdir(exist_ok=True)
    base, rows = experiment("main")
    tight, tight_rows = experiment("tight_tolerance", "--solver-tolerance", "1e-13")
    longer, long_rows = experiment("long_horizon", "--horizon", "320")
    larger, _ = experiment("shock_1bp", "--shock=-1e-4")
    for name, report in [("main", base), ("tight_tolerance", tight), ("long_horizon", longer)]:
        require(all(all(g.values()) for g in report["numerical_gates"].values()),
                f"{name}: numerical gate failed")
    for branch in ("slack", "binding"):
        require(not larger["numerical_gates"][branch]["recurrent_nonlinear_residual"],
                "Larger-shock approximation failure changed; inspect before updating the paper")
        require(larger["numerical_gates"][branch]["strict_regime_margins"], "Large shock regime failure")
    comparisons = {}
    for label, other in [("tight_tolerance", tight_rows), ("long_horizon", long_rows)]:
        lookup = {(r["branch"], r["period"]): r for r in other}
        error = max(abs(float(r[k]) - float(lookup[(r["branch"], r["period"])][k]))
                    for r in rows for k in r
                    if k.endswith("_deviation") and r[k] != "")
        require(error < 1e-10, f"{label}: common-horizon responses changed")
        comparisons[label] = error
    impact = {}
    for branch in ("slack", "binding"):
        r = next(r for r in rows if r["branch"] == branch and r["period"] == "0")
        dy = float(r["output_deviation"])
        dc = float(r["total_consumption_deviation"])
        dg = float(r["capital_adjustment_resources_deviation"])
        dr = float(r["price_adjustment_resources_deviation"])
        accounting_error = abs(dy - dc - dg - dr)
        require(accounting_error < 1e-10, "Impact resource-accounting error")
        require(all(abs(float(r[k + "_deviation"])) < 1e-12
                    for k in ("capital_H", "capital_L")), "Installed impact capital must be predetermined")
        require(all(float(r[k + "_deviation"]) < 0 for k in ("labor_H", "labor_L")),
                "Output interpretation must be revisited")
        for i in ("H", "L"):
            require(abs(float(r[f"labor_{i}_log_deviation_pct"]) - 2*(float(r["input_price_log_deviation_pct"])-float(r["wage_log_deviation_pct"]))) < 1e-10, "Impact labor demand identity")
            require(abs(float(r[f"output_{i}_log_deviation_pct"]) - .5*float(r[f"labor_{i}_log_deviation_pct"])) < 1e-10, "Impact production identity")
        impact[branch] = {"loan_rate_bp": 10000*float(r["loan_rate_deviation"]),
            "interbank_rate_bp": 10000*float(r["interbank_rate_deviation"]),
            "output_log_pct": float(r["output_log_deviation_pct"]),
            "credit_H_log_pct": float(r["credit_H_log_deviation_pct"]),
            "credit_L_log_pct": float(r["credit_L_log_deviation_pct"]),
            "loss_100_log_difference": 100*float(r["conditional_misallocation_loss_deviation"]),
            "wage_log_pct": float(r["wage_log_deviation_pct"]),
            "input_price_log_pct": float(r["input_price_log_deviation_pct"]),
            "labor_log_pct": float(r["labor_log_deviation_pct"]),
            "resource_decomposition": {"output": dy, "consumption": dc,
                "capital_resources": dg, "price_resources": dr, "error": accounting_error}}
    require(impact["slack"]["loss_100_log_difference"] < 0 < impact["binding"]["loss_100_log_difference"],
            "Conditional allocation signs changed")
    audit = {"status": "passed_internal_numerical_checks", "full_equilibrium_validated": False,
        "external_data": False, "illustrative_parameters": True,
        "main_input_hashes": base["input_hashes"], "impact": impact,
        "common_horizon_max_level_deviation_difference": comparisons,
        "large_shock_expected_tail_gate_failure": True,
        "limitations": ["Nonlinear two-date prefix; local-linear recurrent path",
            "Backward value recursion does not prove bank policy optimality",
            "No global determinacy or branch selection", "Public debt remains uncalibrated",
            "Conditional allocation loss is a next-period production benchmark, not welfare"]}
    (OUT / "delivery_audit.json").write_text(json.dumps(audit, indent=2)+"\n", encoding="utf-8")
    specs = [("Tasa interbancaria (pb)", "interbank_rate_bp"),
        ("Tasa de crédito (pb)", "loan_rate_bp"), ("Producción (log \\%)", "output_log_pct"),
        ("Crédito H (log \\%)", "credit_H_log_pct"), ("Crédito L (log \\%)", "credit_L_log_pct"),
        ("Pérdida condicional ($100\\Delta\\log$)", "loss_100_log_difference")]
    lines = [r"\begin{tabular}{lrr}\toprule", r"Respuesta al impacto & S & B\\\midrule"]
    for label, key in specs:
        lines.append(f"{label} & {impact['slack'][key]:.8f} & {impact['binding'][key]:.8f}" + r"\\")
    lines.append(r"\bottomrule\end{tabular}")
    (REPO / "paper/irf_impact_table.tex").write_text("\n".join(lines)+"\n", encoding="utf-8")
    draw(rows)
    artifacts = [OUT / "delivery_audit.json", REPO / "paper/irf_impact_table.tex",
                 *sorted(FIG.glob("irf_*.pdf")), *sorted(FIG.glob("irf_*.png"))]
    manifest = {p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in artifacts}
    (OUT / "delivery_manifest.json").write_text(json.dumps(manifest, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": audit["status"], "impact": impact, "figures": str(FIG)}, indent=2))


if __name__ == "__main__":
    main()
