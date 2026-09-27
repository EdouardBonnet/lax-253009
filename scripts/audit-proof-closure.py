#!/usr/bin/env python3
"""Audit the documented proof dependencies after a successful lax build."""

import json
import os
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DATABASE = Path(os.environ.get("LAX_HOME", Path.home() / ".lax")) / "lax-database"
HARDNESS = "Lax253009.CliqueHardness.approximation_implies_np_eq_zpp"
ZPP_BPP = "Lax666725.ZPPSubsetBPP.ZPP_subset_BPP"
BPP_CONSEQUENCE = "Lax253009.BPPConsequence.approximation_implies_np_subset_bpp"
EXPECTED_CONDITIONAL = {
    "Lax253009Proofs.clique_approximation_implies_np_subset_bpp": {HARDNESS, ZPP_BPP},
    "Lax253009Proofs.clique_not_approximable_of_np_ne_zpp": {HARDNESS},
    "Lax253009Proofs.clique_not_approximable_of_np_not_subset_bpp": {BPP_CONSEQUENCE},
}


def require(condition, message):
    if not condition:
        raise SystemExit(f"Audit failed: {message}")


def read(path):
    return json.loads(path.read_text())


def main():
    local = read(ROOT / "build-output.json")
    actual_conditional = {
        proof["id"]: set(proof["assumptions"])
        for proof in local["proofs"] if proof["assumptions"]
    }
    require(actual_conditional == EXPECTED_CONDITIONAL,
            f"unexpected conditional proofs: {actual_conditional}")
    statements = {
        statement["id"]
        for concept in local["concepts"] for statement in concept["statements"]
    }
    conclusions = {proof["conclusion"] for proof in local["proofs"]}
    require(statements <= conclusions,
            f"unexpected statements without proof entries: {statements - conclusions}")

    # Read the dependency closure from generated archive metadata. A proof is
    # closed only when all of its statement assumptions are already closed.
    outputs = [local]
    seen = {local["id"]}
    for output in outputs:
        packages = output["requiredByConcepts"] + output["requiredByProofs"]
        for package in packages:
            submission_id = "lax-" + package.removeprefix("Lax").removesuffix("Proofs")
            if submission_id not in seen:
                outputs.append(read(DATABASE / submission_id / "build-output.json"))
                seen.add(submission_id)
    proofs = [proof for output in outputs for proof in output["proofs"]]
    closed = set()
    while True:
        new = {proof["conclusion"] for proof in proofs
               if set(proof["assumptions"]) <= closed} - closed
        if not new:
            break
        closed.update(new)
    require(ZPP_BPP in closed, "the imported ZPP ⊆ BPP proof is not closed")
    unresolved = statements - closed
    require(not unresolved,
            f"unexpected proof closure: {sorted(unresolved)}")
    independent = sum(not proof["assumptions"] for proof in local["proofs"])
    print(f"{len(local['concepts'])} concepts; {len(local['proofs'])} proof entries")
    print(f"{independent} proofs without archive statement assumptions; "
          f"{len(actual_conditional)} deductions with closed archive dependencies")
    print("Imported ZPP ⊆ BPP: proved with closed upstream dependencies")
    print(f"{len(statements & closed)} of {len(statements)} local statements proved")
    print("No open roots or unresolved consequences.")


if __name__ == "__main__":
    main()
