# Summary of changes
## Completed: Deriving Causal Order from Propagation Kernels

I have fully formalized the entire framework in Lean 4 with Mathlib, organized across 5 files with **zero `sorry` statements** and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). All theorems compile and are machine-verified.

### File Structure

- **`RequestProject/Basic.lean`** — Core definitions: `CorrelationKernel` (symmetric kernel → emergent metric d(i,j) = -log I(i,j)), `PropagationKernel` (semigroup composition law), derived `causal` relation, `diamond`, compatibility conditions. Includes proofs that d is a pseudometric (nonneg, self-zero, symmetric, triangle inequality).

- **`RequestProject/CoreTheorems.lean`** — **Theorems 1–3**: Irreflexivity under acyclicity, transitivity from semigroup law, and the main structural theorem that ≺_K is a strict partial order (`IsStrictOrder`). Also proves Assumptions A (false without acyclicity) and B (true: semigroup + acyclicity suffice).

- **`RequestProject/Diamonds.lean`** — **Theorems 4–5**: Causal diamonds are well-defined (empty when no causal relation, imply causal relation by transitivity). Trivial propagation yields trivially empty diamonds.

- **`RequestProject/Compatibility.lean`** — **Theorems 6–7**: 
  - Theorem 6 / Assumption C: Explicit counterexample on Fin 3 showing metric compatibility is NOT automatic (d(0,1) = 10 > 1 = d(0,2) but 1 ∈ ◊(0,2)).
  - Theorem 7 / Assumption D: Finite-speed propagation (K_t(i,j) > 0 ⟹ d(i,j) ≤ vt) implies metric-causal compatibility.

- **`RequestProject/ToyModels.lean`** — **Models A, B, C + Theorem 9**:
  - Model A (directed chain on Fin(n+1)): causal order = usual order, acyclic, finite speed v=1.
  - Model C (symmetric propagation): acyclicity fails, showing directedness is essential.
  - Theorem 9: Same type with different propagation kernels yields different causal orders.

- **`RequestProject/Frontier.lean`** — **Theorems 8, 10 + Assumption E**:
  - Theorem 8: Earliest arrival time is subadditive on causal chains.
  - Theorem 10: `CommonOrigin` structure derives both metric and causal order from a single cost function D, with automatic finite-speed compatibility.
  - Assumption E: Geometry and causality CAN come from the same structure.

### All 5 Assumptions Tested

| Assumption | Result | Theorem |
|---|---|---|
| A: Propagation auto-defines causal order | **False** without acyclicity | `assumption_A_false` |
| B: Semigroup + acyclicity → strict partial order | **True** | `assumption_B_true` |
| C: Metric emergence → auto-compatible | **False** | `assumption_C_false` |
| D: Finite speed → compatibility | **True** | `assumption_D_true` |
| E: Geometry & causality from same structure | **Possible** | `assumption_E` |

See `RequestProject/README.md` for detailed documentation.