"""Reproduce internal model certificates without reading research notes or data."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
STEPS = [
    "sampled_checks.py",
    "cotas_2026_10_15/verified_linear_operator.py",
    "cotas_2026_10_15/verified_nonlinear_radius.py",
    "cotas_2026_10_15/audit_selector_tree.py",
    "regimenes_2026_10_17/audit_regime_bounds.py",
    "cierre_interno_2026_10_17/finite_bridge.py",
]
ARTIFACTS = [
    "sampled_checks.json",
    "cotas_2026_10_15/verified_linear_bounds.json",
    "cotas_2026_10_15/verified_nonlinear_radius.json",
    "cotas_2026_10_15/rational_preconditioners.json",
    "cotas_2026_10_15/selector_tree_check.json",
    "regimenes_2026_10_17/regime_bounds.json",
    "cierre_interno_2026_10_17/finite_bridge_certificate.json",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manuscript():
    source = REPO / "paper/paper.tex"
    text = source.read_text(encoding="utf-8")
    ledger = json.loads((REPO / "paper/result_ledger.json").read_text(encoding="utf-8"))
    assert sha(source) == ledger["paper_sha256"], "Update result ledger after a manuscript edit."
    pattern = re.compile(
        r"\\begin\{(lemma|proposition|remark)\}(?:\[([^\]]*)\])?(.*?)"
        r"\\end\{\1\}\s*\\begin\{proof\}(.*?)\\end\{proof\}", re.S
    )
    results = list(pattern.finditer(text))
    assert len(results) == ledger["numbered_results"] == 57
    by_label = {re.search(r"\\label\{([^}]+)\}", row[3])[1]: row for row in results}
    for row in ledger["results"]:
        match = by_label[row["label"]]
        assert hashlib.sha256(match[3].encode()).hexdigest() == row["statement_sha256"], row["label"]
        assert hashlib.sha256(match[4].encode()).hexdigest() == row["proof_sha256"], row["label"]
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    assert len(labels) == len(set(labels)), "Duplicate manuscript label."
    refs = re.findall(r"\\(?:ref|eqref)\{([^}]+)\}", text)
    assert not (set(refs) - set(labels)), "Unresolved source reference."
    return sha(source)


def main():
    report = {
        "scope": "Internal arithmetic prerequisites and source inventory, not all analytical proofs or Lean coverage.",
        "source_sha256": check_manuscript(), "numbered_results_retained": 57,
        "python": sys.version, "run_started_utc": datetime.now(timezone.utc).isoformat(),
        "formalization_started": False, "macro_irfs_in_this_step": False, "external_data": False,
        "equilibrium_selection": "Both admissible local branches retained; no selector imposed.",
        "steps": [], "status": "running",
    }
    target = HERE / "verification_report.json"
    try:
        for i, relative in enumerate(STEPS, 1):
            script = HERE / relative
            print(f"V0-M internal check {i}/{len(STEPS)}: {script.name}", flush=True)
            result = subprocess.run(
                [sys.executable, "-B", "-X", "utf8", str(script)], cwd=script.parent,
                capture_output=True, text=True, encoding="utf-8", check=False,
            )
            row = {"script": relative, "sha256": sha(script), "returncode": result.returncode}
            report["steps"].append(row)
            if result.returncode:
                row["stderr"] = result.stderr[-10000:]
                row["stdout_tail"] = result.stdout[-3000:]
                raise RuntimeError(f"{relative}: {result.stderr[-3000:]}")
            print("  passed", flush=True)
        report["input_sha256"] = {
            p.relative_to(HERE).as_posix(): sha(p)
            for p in sorted((HERE / "cotas_2026_10_15/inputs").iterdir()) if p.is_file()
        }
        report["artifacts_sha256"] = {relative: sha(HERE / relative) for relative in ARTIFACTS}
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        report["run_finished_utc"] = datetime.now(timezone.utc).isoformat()
        target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    print("All six V0-M prerequisite checks passed; 57 literal results retained. This step runs neither Lean nor IRFs.")


if __name__ == "__main__":
    main()
