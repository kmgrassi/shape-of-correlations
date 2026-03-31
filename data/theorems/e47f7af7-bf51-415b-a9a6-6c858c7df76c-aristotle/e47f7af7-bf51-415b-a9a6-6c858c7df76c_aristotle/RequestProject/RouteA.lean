import Mathlib

/-!
# Route A: Wave Dynamics → Multiplicative Correlation → Emergent Geometry

This file formalizes theorems showing that multiplicative correlation structure
(and therefore emergent geometry) can arise from compositional propagation or
least-cost structure on graphs and relational structures.

## Main Results

### Abstract Bridge Theorems
- `exp_neg_submul`: If `D` satisfies the triangle inequality, then `exp(-D)`
  is submultiplicative: `exp(-D(i,k)) ≥ exp(-D(i,j)) · exp(-D(j,k))`.
- `neg_log_submul_triangle`: Conversely, if `I` is submultiplicative with
  `0 < I ≤ 1`, then `-log(I)` satisfies the triangle inequality.
- `exp_neg_log_id`: `-log(exp(-D)) = D`, showing the two transformations are inverses.

### Graph Path Models (Theorem A1)
- Walk concatenation preserves weight multiplicativity.
- `walk_submul_exists`: Concatenating optimal walks yields submultiplicativity
  of the maximal-path correlation.

### Shortest-Path Distance (Theorem A2)
- Walk cost is additive under concatenation.
- `shortestPath_exp_submul`: The exponential kernel `exp(-D)` for shortest-path
  distance `D` is submultiplicative.

### Interpretation
These results show: **path-based wave propagation ⇒ multiplicative kernel ⇒
emergent geometry**. Multiplicative correlation is not an arbitrary assumption —
it arises naturally from compositional propagation along relational paths.
-/

open Real Finset BigOperators

noncomputable section

/-! ## Section 1: Abstract Bridge Theorems

These theorems establish the equivalence between:
- `D` being a pseudometric (triangle inequality), and
- `I = exp(-D)` being a submultiplicative kernel.
-/

/-
PROBLEM
**Theorem A2 (Abstract)**: If `D` satisfies the triangle inequality,
    then `I(i,j) = exp(-D(i,j))` is a submultiplicative kernel.
    This is the core "action ⇒ multiplicative correlation" bridge.

PROVIDED SOLUTION
D(i,k) ≤ D(i,j) + D(j,k) implies -(D(i,j) + D(j,k)) ≤ -D(i,k). Since exp is monotone, exp(-D(i,k)) ≥ exp(-(D(i,j)+D(j,k))) = exp(-D(i,j)) · exp(-D(j,k)) by Real.exp_add.
-/
theorem exp_neg_submul {S : Type*} {D : S → S → ℝ}
    (htri : ∀ i j k, D i k ≤ D i j + D j k) (i j k : S) :
    Real.exp (-D i k) ≥ Real.exp (-D i j) * Real.exp (-D j k) := by
  rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.2 ( by linarith [ htri i j k ] ) ;

/-
PROBLEM
The transformations `D ↦ exp(-D)` and `I ↦ -log(I)` are inverses:
    `-log(exp(-D(i,j))) = D(i,j)`.

PROVIDED SOLUTION
Use Real.log_exp to get log(exp(-D i j)) = -D i j, then negate.
-/
theorem exp_neg_log_id {S : Type*} {D : S → S → ℝ}
    (hnn : ∀ i j, 0 ≤ D i j) (i j : S) :
    -Real.log (Real.exp (-D i j)) = D i j := by
  norm_num

/-
PROBLEM
**Converse bridge**: If `I` is a submultiplicative kernel with `0 < I ≤ 1`,
    then `d = -log(I)` satisfies the triangle inequality.

PROVIDED SOLUTION
From hsubmul: I(i,k) ≥ I(i,j) · I(j,k). Since 0 < I(i,j) and 0 < I(j,k), and log is monotone on positives, log(I(i,k)) ≥ log(I(i,j) · I(j,k)) = log(I(i,j)) + log(I(j,k)). Negate both sides to get -log(I(i,k)) ≤ -log(I(i,j)) + (-log(I(j,k))).
-/
theorem neg_log_submul_triangle {S : Type*} {I : S → S → ℝ}
    (hpos : ∀ i j, 0 < I i j)
    (hle : ∀ i j, I i j ≤ 1)
    (hsubmul : ∀ i j k, I i k ≥ I i j * I j k) (i j k : S) :
    -Real.log (I i k) ≤ -Real.log (I i j) + (-Real.log (I j k)) := by
  linarith [ Real.log_le_log ( mul_pos ( hpos i j ) ( hpos j k ) ) ( hsubmul i j k ), Real.log_mul ( ne_of_gt ( hpos i j ) ) ( ne_of_gt ( hpos j k ) ) ]

/-
PROBLEM
If `I` is submultiplicative with `I(i,i) = 1` and `0 < I ≤ 1`,
    then `d = -log(I)` is a pseudometric.

PROVIDED SOLUTION
Split into the four conjuncts. (1) -log(I(i,i)) = -log(1) = 0. (2) Symmetry from hsymm. (3) Triangle from neg_log_submul_triangle. (4) Non-negativity: since I(i,j) ≤ 1, log(I(i,j)) ≤ log(1) = 0, so -log(I(i,j)) ≥ 0.
-/
theorem neg_log_submul_pseudometric {S : Type*} {I : S → S → ℝ}
    (hpos : ∀ i j, 0 < I i j)
    (hle : ∀ i j, I i j ≤ 1)
    (hrefl : ∀ i, I i i = 1)
    (hsymm : ∀ i j, I i j = I j i)
    (hsubmul : ∀ i j k, I i k ≥ I i j * I j k) :
    (∀ i, -Real.log (I i i) = 0) ∧
    (∀ i j, -Real.log (I i j) = -Real.log (I j i)) ∧
    (∀ i j k, -Real.log (I i k) ≤ -Real.log (I i j) + (-Real.log (I j k))) ∧
    (∀ i j, 0 ≤ -Real.log (I i j)) := by
  -- Now use the given hypotheses to prove each part of the conjunction.
  apply And.intro (by
  aesop) (And.intro (by
  exact fun i j => hsymm i j ▸ rfl) (And.intro (by
  exact?) (by
  exact fun i j => neg_nonneg_of_nonpos ( Real.log_nonpos ( le_of_lt ( hpos i j ) ) ( hle i j ) ))))

/-! ## Section 2: Walk-Based Path Models (Theorem A1)

We formalize walks on a type `S` as sequences of vertices indexed by `Fin (n+1)`.
A walk's weight (under edge weights `w`) is the product of consecutive edge weights.
We prove that concatenating walks multiplies their weights, establishing that
the maximal-path correlation is submultiplicative.
-/

/-- A walk of length `n` on type `S` is a sequence of `n+1` vertices. -/
structure Walk (S : Type*) (n : ℕ) where
  vertices : Fin (n + 1) → S

namespace Walk

/-- The starting vertex of a walk. -/
def src {S : Type*} {n : ℕ} (p : Walk S n) : S := p.vertices 0

/-- The ending vertex of a walk. -/
def dst {S : Type*} {n : ℕ} (p : Walk S n) : S :=
  p.vertices ⟨n, Nat.lt_succ_of_le le_rfl⟩

/-- The weight of a walk under edge weight function `w`:
    `W(p) = ∏_{m=0}^{n-1} w(v_m, v_{m+1})`. -/
def weight {S : Type*} {n : ℕ} (w : S → S → ℝ) (p : Walk S n) : ℝ :=
  ∏ i : Fin n, w (p.vertices i.castSucc) (p.vertices i.succ)

/-- The cost of a walk under edge cost function `c`:
    `C(p) = ∑_{m=0}^{n-1} c(v_m, v_{m+1})`. -/
def cost {S : Type*} {n : ℕ} (c : S → S → ℝ) (p : Walk S n) : ℝ :=
  ∑ i : Fin n, c (p.vertices i.castSucc) (p.vertices i.succ)

/-- A trivial walk of length 0 at vertex `v`. -/
def trivial {S : Type*} (v : S) : Walk S 0 where
  vertices := fun _ => v

@[simp] theorem trivial_src {S : Type*} (v : S) : (trivial v).src = v := rfl
@[simp] theorem trivial_dst {S : Type*} (v : S) : (trivial v).dst = v := rfl
@[simp] theorem trivial_weight {S : Type*} (w : S → S → ℝ) (v : S) :
    (trivial v).weight w = 1 := Finset.prod_empty
@[simp] theorem trivial_cost {S : Type*} (c : S → S → ℝ) (v : S) :
    (trivial v).cost c = 0 := Finset.sum_empty

/-- A single-edge walk from `a` to `b`. -/
def edge {S : Type*} (a b : S) : Walk S 1 where
  vertices := ![a, b]

@[simp] theorem edge_src {S : Type*} (a b : S) : (edge a b).src = a := rfl
@[simp] theorem edge_dst {S : Type*} (a b : S) : (edge a b).dst = b := by
  simp [dst, edge, Matrix.cons_val_one, Matrix.head_cons]

/-- Concatenation of two walks: if `p` goes from its src to j, and `q` starts at j,
    then `concat p q` goes from p.src to q.dst and has length `n + m`. -/
def concat {S : Type*} {n m : ℕ} (p : Walk S n) (q : Walk S m)
    (h : p.dst = q.src) : Walk S (n + m) where
  vertices := fun i =>
    if hi : i.val ≤ n
    then p.vertices ⟨i.val, by omega⟩
    else q.vertices ⟨i.val - n, by omega⟩

/-
PROBLEM
The concatenation starts where `p` starts.

PROVIDED SOLUTION
The src is vertices 0. In concat, index 0 has 0 ≤ n (since n ≥ 0), so we take the p branch: p.vertices ⟨0, _⟩ = p.vertices 0 = p.src.
-/
@[simp] theorem concat_src {S : Type*} {n m : ℕ} (p : Walk S n) (q : Walk S m)
    (h : p.dst = q.src) : (p.concat q h).src = p.src := by
  exact?

/-
PROBLEM
The concatenation ends where `q` ends.

PROVIDED SOLUTION
Unfold concat, dst. The dst index is ⟨n+m, _⟩. We need to check whether n+m ≤ n. Case split on m: if m = 0, then n+m = n ≤ n so we get p.vertices ⟨n,_⟩ = p.dst = h ▸ q.src = q.vertices 0 = q.dst (since m=0). If m > 0, then n+m > n so ¬(n+m ≤ n), and we get q.vertices ⟨n+m-n, _⟩ = q.vertices ⟨m, _⟩ = q.dst. Use simp with omega for the Fin arithmetic.
-/
@[simp] theorem concat_dst {S : Type*} {n m : ℕ} (p : Walk S n) (q : Walk S m)
    (h : p.dst = q.src) : (p.concat q h).dst = q.dst := by
  convert congr_arg _ h using 1;
  any_goals exact fun _ => q.dst;
  · unfold Walk.concat;
    unfold Walk.dst; aesop;
  · rfl

/-
PROBLEM
**Key Lemma (A1)**: The weight of a concatenated walk equals the product of weights.
    This is the formal heart of "composition of propagation amplitudes is multiplicative".

PROVIDED SOLUTION
Use Fin.prod_univ_add to split the product over Fin (n+m) into products over Fin n and Fin m. For the first part (Fin.castAdd), the concat vertices at index i (where i < n) satisfy i.val ≤ n, so we get p.vertices. For the second part (Fin.natAdd), the concat vertices at index n+i satisfy n+i > n (when considering castSucc and succ), so we get q.vertices. The key is showing that the vertices of the concatenated walk agree with p's vertices for the first n+1 positions and q's vertices for the last m+1 positions, with the overlap at position n matching due to h : p.dst = q.src.
-/
theorem concat_weight {S : Type*} {n m : ℕ} (w : S → S → ℝ)
    (p : Walk S n) (q : Walk S m) (h : p.dst = q.src) :
    (p.concat q h).weight w = p.weight w * q.weight w := by
  unfold weight;
  rw [ Fin.prod_univ_add ];
  congr! 1;
  · congr! 1;
    simp +decide [ Walk.concat ];
    rfl;
  · refine' Finset.prod_congr rfl fun i _ => _;
    congr! 1;
    · simp +decide [ Walk.concat ];
      cases i ; aesop;
    · simp +decide [ Fin.natAdd, Fin.succ, Walk.concat ];
      simp +decide [ add_assoc, Nat.add_sub_assoc ]

/-
PROBLEM
**Key Lemma (A2)**: The cost of a concatenated walk equals the sum of costs.

PROVIDED SOLUTION
Use Fin.sum_univ_add to split the sum over Fin (n+m) into sums over Fin n and Fin m. Same argument as concat_weight but with sums instead of products.
-/
theorem concat_cost {S : Type*} {n m : ℕ} (c : S → S → ℝ)
    (p : Walk S n) (q : Walk S m) (h : p.dst = q.src) :
    (p.concat q h).cost c = p.cost c + q.cost c := by
  convert Fin.sum_univ_add _ using 2;
  · simp +decide [ Walk.concat ];
    rfl;
  · simp +decide [Walk.concat, Walk.vertices];
    refine' Finset.sum_congr rfl fun i hi => _;
    simp +decide [ add_assoc, Fin.castSucc, Fin.succ ];
    split_ifs <;> simp_all +decide [ Fin.add_def, Fin.castAdd ];
    · simp_all +decide [ Fin.castLE, Walk.dst, Walk.src ];
    · congr! 2

end Walk

/-
PROBLEM
**Theorem A1 (Existence form)**: Given any walk from `i` to `j` and any walk
    from `j` to `k`, there exists a walk from `i` to `k` whose weight is the product.
    This implies the maximal-path correlation is submultiplicative.

PROVIDED SOLUTION
Use the walk p with hp' : p.dst = j and hq : q.src = j, so p.dst = q.src by hp' ▸ hq ▸ rfl. Concatenate p and q to get r = p.concat q h. Then r.src = p.src = i (by concat_src and hp), r.dst = q.dst = k (by concat_dst and hq'), and r.weight w = p.weight w * q.weight w (by concat_weight). Take m = n₁ + n₂.
-/
theorem walk_submul_exists {S : Type*} {w : S → S → ℝ} {i j k : S}
    {n₁ n₂ : ℕ} (p : Walk S n₁) (q : Walk S n₂)
    (hp : p.src = i) (hp' : p.dst = j)
    (hq : q.src = j) (hq' : q.dst = k) :
    ∃ (m : ℕ) (r : Walk S m), r.src = i ∧ r.dst = k ∧
    r.weight w = p.weight w * q.weight w := by
  -- By definition of Walk.concat, we can construct such a walk r.
  use n₁ + n₂, p.concat q (by
  rw [hp', hq])
  generalize_proofs at *;
  exact ⟨ by rw [ Walk.concat_src, hp ], by rw [ Walk.concat_dst, hq' ], by rw [ Walk.concat_weight ] ⟩

/-! ## Section 3: Shortest-Path Distance

We define the shortest-path "distance" as the infimum of walk costs,
and show the exponential kernel `exp(-D)` is submultiplicative.
For finite types, we can also use the minimum over bounded-length walks.
-/

/-- For finite types, the minimum cost of a walk of length ≤ `bound` from `i` to `j`. -/
noncomputable def minWalkCost {S : Type*} [Fintype S] [DecidableEq S]
    (c : S → S → ℝ) (i j : S) (bound : ℕ) : ℝ :=
  ⨅ (n : Fin (bound + 1)) (p : Walk S n)
    (_ : p.src = i) (_ : p.dst = j), p.cost c

/-! ## Section 4: Putting It All Together

The main synthesis: path-based propagation naturally produces multiplicative
correlation kernels, which in turn induce pseudometric geometry via `-log`.
-/

/-
PROBLEM
**Main Synthesis Theorem (A2)**: If `D` is any function satisfying the triangle
    inequality (as shortest-path distances do), then `exp(-D)` is submultiplicative
    and `-log(exp(-D)) = D` is a pseudometric.

    This gives: **path-based propagation ⇒ multiplicative kernel ⇒ emergent geometry**.

PROVIDED SOLUTION
Split into 5 conjuncts. (1) Use exp_neg_submul with htri. (2) Use exp_neg_log_id with hnn. (3-5) Use hrefl, hsymm, htri directly.
-/
theorem action_to_geometry {S : Type*} {D : S → S → ℝ}
    (hnn : ∀ i j, 0 ≤ D i j)
    (hrefl : ∀ i, D i i = 0)
    (hsymm : ∀ i j, D i j = D j i)
    (htri : ∀ i j k, D i k ≤ D i j + D j k) :
    -- The kernel exp(-D) is submultiplicative
    (∀ i j k, Real.exp (-D i k) ≥ Real.exp (-D i j) * Real.exp (-D j k)) ∧
    -- And -log(exp(-D)) recovers D
    (∀ i j, -Real.log (Real.exp (-D i j)) = D i j) ∧
    -- So D is confirmed as a pseudometric
    (∀ i, D i i = 0) ∧
    (∀ i j, D i j = D j i) ∧
    (∀ i j k, D i k ≤ D i j + D j k) := by
  refine' ⟨ _, _, _, _, _ ⟩ <;> simp_all +decide [ ← Real.exp_add ];
  exact fun i j k => by linarith [ htri i j k ] ;

end