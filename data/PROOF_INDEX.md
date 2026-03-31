# Proof Artifact Index (Aristotle Downloads)

This index maps paper claims to machine-checked Lean artifacts extracted under `downloads/extracted/`.

## Planned public mirror

When the public repo is ready, set:

- `PUBLIC_REPO_BASE = https://github.com/<ORG>/<REPO>/tree/main/downloads/extracted`

Then replace placeholder links below.

---

## Core CHSH / nonlocality proofs

1. **Quantitative CHSH bounds under geometric constraints**
   - Request: `3eb07f9d-dde1-4353-ab80-8b7f1c47f121`
   - Summary: `downloads/extracted/3eb07f9d-dde1-4353-ab80-8b7f1c47f121-aristotle/3eb07f9d-dde1-4353-ab80-8b7f1c47f121_aristotle/ARISTOTLE_SUMMARY_3eb07f9d-dde1-4353-ab80-8b7f1c47f121.md`
   - Key Lean files:
     - `.../RequestProject/Tsirelson.lean`
     - `.../RequestProject/Obstruction.lean`
     - `.../RequestProject/Construction.lean`
     - `.../RequestProject/Rank1.lean`

2. **CHSH local bound + no-signaling toy verification**
   - Request: `399e8153-4b65-4894-ac4e-245caa023536`
   - Summary: `downloads/extracted/399e8153-4b65-4894-ac4e-245caa023536-aristotle/399e8153-4b65-4894-ac4e-245caa023536_aristotle/ARISTOTLE_SUMMARY_399e8153-4b65-4894-ac4e-245caa023536.md`
   - Key Lean file:
     - `.../RequestProject/EmergentLocalityBell.lean`

3. **Minimal CHSH module (independent)**
   - Request: `42c716ff-5ce1-4113-b46a-caa36d669892`
   - Summary: `downloads/extracted/42c716ff-5ce1-4113-b46a-caa36d669892-aristotle/42c716ff-5ce1-4113-b46a-caa36d669892_aristotle/ARISTOTLE_SUMMARY_42c716ff-5ce1-4113-b46a-caa36d669892.md`
   - Key Lean file:
     - `.../RequestProject/CHSH.lean`

---

## Geometry / metric-emergence proofs

4. **Correlation→geometry equivalence and stress tests**
   - Request: `6d12681e-0b1f-498f-8864-191718955a2c`
   - Summary: `downloads/extracted/6d12681e-0b1f-498f-8864-191718955a2c-aristotle/6d12681e-0b1f-498f-8864-191718955a2c_aristotle/ARISTOTLE_SUMMARY_6d12681e-0b1f-498f-8864-191718955a2c.md`
   - Key Lean folder:
     - `.../RequestProject/CorrGeom/`

5. **Emergent metric + interference toy model**
   - Request: `eba46516-8666-422a-a6e9-b43754904891`
   - Summary: `downloads/extracted/eba46516-8666-422a-a6e9-b43754904891-aristotle/eba46516-8666-422a-a6e9-b43754904891_aristotle/ARISTOTLE_SUMMARY_eba46516-8666-422a-a6e9-b43754904891.md`
   - Key Lean files:
     - `.../RequestProject/EmergentMetric.lean`
     - `.../RequestProject/Interference.lean`
     - `.../RequestProject/ToyModel.lean`

6. **Route-A / Route-B bridge (multiplicative kernels ↔ geometry)**
   - Requests: `1b6667c0-c5f1-46bd-984c-a696bca9192b`, `e47f7af7-bf51-415b-a9a6-6c858c7df76c`
   - Summaries:
     - `downloads/extracted/1b6667c0-c5f1-46bd-984c-a696bca9192b-aristotle/resumed-e47f7af7-bf51-415b-a9a6-6c858c7df76c_aristotle/ARISTOTLE_SUMMARY_1b6667c0-c5f1-46bd-984c-a696bca9192b.md`
     - `downloads/extracted/1b6667c0-c5f1-46bd-984c-a696bca9192b-aristotle/resumed-e47f7af7-bf51-415b-a9a6-6c858c7df76c_aristotle/ARISTOTLE_SUMMARY_e47f7af7-bf51-415b-a9a6-6c858c7df76c.md`
   - Key Lean files:
     - `.../RequestProject/RouteA.lean`
     - `.../RequestProject/RouteB.lean`

---

## Causality / independence proofs

7. **Causal order from propagation kernels + metric independence**
   - Request: `d4d3c17b-77f0-4113-a0de-63eff6f9ec5e`
   - Summary: `downloads/extracted/d4d3c17b-77f0-4113-a0de-63eff6f9ec5e-aristotle/d4d3c17b-77f0-4113-a0de-63eff6f9ec5e_aristotle/ARISTOTLE_SUMMARY_d4d3c17b-77f0-4113-a0de-63eff6f9ec5e.md`
   - Key Lean files:
     - `.../RequestProject/Basic.lean`
     - `.../RequestProject/CoreTheorems.lean`
     - `.../RequestProject/Compatibility.lean`
     - `.../RequestProject/Frontier.lean`

8. **Causal/metric compatibility counterexamples and constraints**
   - Request: `b78c6819-c75f-47d7-8ee8-5967f3b946fa`
   - Summary: `downloads/extracted/b78c6819-c75f-47d7-8ee8-5967f3b946fa-aristotle/b78c6819-c75f-47d7-8ee8-5967f3b946fa_aristotle/ARISTOTLE_SUMMARY_b78c6819-c75f-47d7-8ee8-5967f3b946fa.md`

---

## Notes

- There are duplicate archives for some request IDs (e.g. `(1)` filenames). Keep one canonical copy when publishing publicly.
- Suggested public structure: keep this `downloads/PROOF_INDEX.md` and link from the paper appendix.
