/-
# Classification Theorems for Common-Origin Kernels

Main theorems characterizing the interplay between geometry
(submultiplicativity / metric emergence) and Bell violation (CHSH > 2)
in normalized PSD relational kernels.
-/
import Mathlib
import RequestProject.Defs

namespace CommonOrigin

open Finset BigOperators Real

-- ============================================================
-- Useful lemmas about √2
-- ============================================================

lemma sqrt2half_pos : (0 : ℝ) < sqrt2half := by
  unfold sqrt2half
  positivity

/-
PROVIDED SOLUTION
sqrt2half = Real.sqrt 2 / 2, so sqrt2half^2 = (Real.sqrt 2)^2 / 4 = 2/4 = 1/2. Use Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2).
-/
lemma sqrt2half_sq : sqrt2half ^ 2 = 1 / 2 := by
  rw [ show sqrt2half = Real.sqrt 2 / 2 by rfl, div_pow, Real.sq_sqrt ] <;> norm_num

/-
PROVIDED SOLUTION
Same as sqrt2half_sq but written as mul instead of sq. sqrt2half * sqrt2half = sqrt2half^2 = 1/2.
-/
lemma sqrt2half_mul_self : sqrt2half * sqrt2half = 1 / 2 := by
  rw [ show sqrt2half = Real.sqrt 2 / 2 by rfl, div_mul_div_comm, Real.mul_self_sqrt ] <;> norm_num

/-
PROVIDED SOLUTION
2 * sqrt 2 > 2 iff sqrt 2 > 1 iff 2 > 1. Use nlinarith with Real.sq_sqrt and sq_nonneg.
-/
lemma two_sqrt2_gt_two : 2 * Real.sqrt 2 > 2 := by
  nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-
PROVIDED SOLUTION
4 * (Real.sqrt 2 / 2) = 2 * Real.sqrt 2. Ring arithmetic.
-/
lemma four_sqrt2half_eq : 4 * sqrt2half = 2 * Real.sqrt 2 := by
  ring!

-- ============================================================
-- Section 1: Constant Kernel Properties
-- ============================================================

section ConstantKernel

theorem constKernel_symmetric (S : Type*) : IsSymmetric (constKernel S) := by
  intro i j; rfl

theorem constKernel_normalized (S : Type*) : IsNormalized (constKernel S) := by
  intro i; rfl

/-
PROVIDED SOLUTION
∑ i, ∑ j, c i * 1 * c j = (∑ i, c i)^2 ≥ 0. Rewrite the sum, use sq_nonneg.
-/
theorem constKernel_psd (S : Type*) [Fintype S] [DecidableEq S] :
    IsPSD (constKernel S) := by
      intro c
      simp [constKernel];
      simpa only [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using mul_self_nonneg _

theorem constKernel_isCommonOrigin (S : Type*) [Fintype S] [DecidableEq S] :
    IsCommonOriginKernel (constKernel S) :=
  ⟨constKernel_symmetric S, constKernel_normalized S, constKernel_psd S⟩

theorem constKernel_allPositive (S : Type*) : AllPositive (constKernel S) := by
  intro i j
  simp [constKernel]

theorem constKernel_globalSubmult (S : Type*) :
    GlobalSubmult (constKernel S) := by
  intro i j k
  simp [constKernel]

theorem constKernel_globalGeometry (S : Type*) :
    GlobalGeometry (constKernel S) :=
  ⟨constKernel_allPositive S, constKernel_globalSubmult S⟩

/-
PROVIDED SOLUTION
CHSH_value (constKernel (Fin 4)) B = 1 + 1 + 1 - 1 = 2 for any B. So |CHSH| = 2 ≤ 2. Unfold CHSH_value and constKernel, simplify.
-/
theorem constKernel_trivialBell :
    TrivialBell (constKernel (Fin 4)) := by
      intro B; unfold constKernel;
      unfold CHSH_value; norm_num;

end ConstantKernel

-- ============================================================
-- Section 2: CHSH Kernel Properties
-- ============================================================

section CHSHKernel

-- Entry-level lemmas for the CHSH kernel
@[simp] lemma chshKernel_00 : chshKernel 0 0 = 1 := by simp [chshKernel]
@[simp] lemma chshKernel_01 : chshKernel 0 1 = 0 := by simp [chshKernel]
@[simp] lemma chshKernel_02 : chshKernel 0 2 = sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_03 : chshKernel 0 3 = sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_10 : chshKernel 1 0 = 0 := by simp [chshKernel]
@[simp] lemma chshKernel_11 : chshKernel 1 1 = 1 := by simp [chshKernel]
@[simp] lemma chshKernel_12 : chshKernel 1 2 = sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_13 : chshKernel 1 3 = -sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_20 : chshKernel 2 0 = sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_21 : chshKernel 2 1 = sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_22 : chshKernel 2 2 = 1 := by simp [chshKernel]
@[simp] lemma chshKernel_23 : chshKernel 2 3 = 0 := by simp [chshKernel]
@[simp] lemma chshKernel_30 : chshKernel 3 0 = sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_31 : chshKernel 3 1 = -sqrt2half := by simp [chshKernel]
@[simp] lemma chshKernel_32 : chshKernel 3 2 = 0 := by simp [chshKernel]
@[simp] lemma chshKernel_33 : chshKernel 3 3 = 1 := by simp [chshKernel]

/-
PROVIDED SOLUTION
Exhaust all 16 cases (i,j) ∈ Fin 4 × Fin 4 using fin_cases. Each case is resolved by simp [chshKernel].
-/
theorem chshKernel_symmetric : IsSymmetric chshKernel := by
  unfold chshKernel IsSymmetric; (
  norm_num [ Fin.forall_fin_succ ])

/-
PROVIDED SOLUTION
Exhaust all 4 cases i ∈ Fin 4 using fin_cases. Each case is resolved by simp [chshKernel].
-/
theorem chshKernel_normalized : IsNormalized chshKernel := by
  intro i; fin_cases i <;> simp +decide [ chshKernel ] ;

/-
PROVIDED SOLUTION
The CHSH kernel is the Gram matrix of vectors v₀=(1,0), v₁=(0,1), v₂=(√2/2, √2/2), v₃=(√2/2, -√2/2). Show that ∑ᵢ∑ⱼ cᵢ G(i,j) cⱼ = (c₀ + c₂·r + c₃·r)² + (c₁ + c₂·r - c₃·r)² where r = √2/2. Use Fin.sum_univ_four to expand, simp [chshKernel] to simplify entries, then nlinarith with sqrt2half_mul_self and sq_nonneg for the two squares.
-/
theorem chshKernel_psd : IsPSD chshKernel := by
  unfold IsPSD
  intro c
  have h_sum_sq : ∑ i : Fin 4, ∑ j : Fin 4, c i * chshKernel i j * c j = (c 0 + Real.sqrt 2 / 2 * c 2 + Real.sqrt 2 / 2 * c 3)^2 + (c 1 + Real.sqrt 2 / 2 * c 2 - Real.sqrt 2 / 2 * c 3)^2 := by
    simp +decide [ chshKernel, Fin.sum_univ_four ] ; ring;
    norm_num ; ring
  rw [h_sum_sq]
  apply add_nonneg
  apply sq_nonneg
  apply sq_nonneg

theorem chshKernel_isCommonOrigin : IsCommonOriginKernel chshKernel :=
  ⟨chshKernel_symmetric, chshKernel_normalized, chshKernel_psd⟩

/-
PROBLEM
The CHSH value of the optimal kernel is 2√2.

PROVIDED SOLUTION
Unfold CHSH_value and stdBellIndices. The entries are chshKernel 0 2 + chshKernel 0 3 + chshKernel 1 2 - chshKernel 1 3 = r + r + r - (-r) = 4r. Use simp [CHSH_value, stdBellIndices, chshKernel] and ring.
-/
theorem chshKernel_CHSH_value :
    CHSH_value chshKernel stdBellIndices = 4 * sqrt2half := by
      unfold CHSH_value
      unfold stdBellIndices
      simp [chshKernel]
      ring

/-
PROBLEM
The CHSH kernel achieves |CHSH| = 2√2 > 2.

PROVIDED SOLUTION
Use stdBellIndices. By chshKernel_CHSH_value, CHSH = 4 * sqrt2half = 2√2. Then |2√2| = 2√2 > 2 by two_sqrt2_gt_two. Use four_sqrt2half_eq to rewrite.
-/
theorem chshKernel_bellViolating : BellViolating chshKernel := by
  use stdBellIndices;
  rw [ chshKernel_CHSH_value ] ; ring_nf ; norm_num [ abs_of_pos ] ;
  exact Real.lt_sqrt_of_sq_lt ( by norm_num )

/-
PROBLEM
The CHSH kernel has a zero entry G(0,1) = 0, so it fails AllPositive.

PROVIDED SOLUTION
Show ¬AllPositive by exhibiting i=0, j=1 where chshKernel 0 1 = 0. Use intro h, have := h 0 1, simp [chshKernel] at this.
-/
theorem chshKernel_not_allPositive : ¬AllPositive chshKernel := by
  exact fun h => absurd ( h 0 1 ) ( by norm_num [ chshKernel ] )

/-- The CHSH kernel does not satisfy GlobalGeometry. -/
theorem chshKernel_not_globalGeometry : ¬GlobalGeometry chshKernel := by
  intro ⟨h, _⟩
  exact chshKernel_not_allPositive h

end CHSHKernel

-- ============================================================
-- Section 3: Main Classification Theorems (Part III)
-- ============================================================

section MainTheorems

/-- **Theorem 1**: Bell violation does not imply global geometry.
  There exists a common-origin kernel that is Bell-violating
  but does not satisfy GlobalGeometry. -/
theorem theorem1_bell_not_geometry :
    ∃ G : Fin 4 → Fin 4 → ℝ,
      IsCommonOriginKernel G ∧ BellViolating G ∧ ¬GlobalGeometry G :=
  ⟨chshKernel, chshKernel_isCommonOrigin, chshKernel_bellViolating,
   chshKernel_not_globalGeometry⟩

/-- **Theorem 2**: Global geometry does not imply Bell violation.
  There exists a common-origin kernel with GlobalGeometry
  that is Bell-trivial. -/
theorem theorem2_geometry_not_bell :
    ∃ G : Fin 4 → Fin 4 → ℝ,
      IsCommonOriginKernel G ∧ GlobalGeometry G ∧ TrivialBell G :=
  ⟨constKernel (Fin 4), constKernel_isCommonOrigin (Fin 4),
   constKernel_globalGeometry (Fin 4), constKernel_trivialBell⟩

/-
PROBLEM
**Theorem 3**: The intersection (sector geometry + Bell violation) is nonempty.
  There exists a common-origin kernel and a sector T such that
  SectorGeometry holds on T and the kernel is Bell-violating.

PROVIDED SOLUTION
Use G = chshKernel, T = {0, 2}. SectorGeometry: for i,j,k ∈ {0,2}, check |G(i,k)| ≥ |G(i,j)|·|G(j,k)| and positivity. The entries are G(0,0)=1, G(0,2)=G(2,0)=√2/2, G(2,2)=1. All positive. Submultiplicativity: 8 triples to check, all satisfy since |G| ∈ {1, √2/2} and 1 ≥ 1·(√2/2), √2/2 ≥ (√2/2)·1, 1 ≥ (√2/2)²=1/2. BellViolating from chshKernel_bellViolating.
-/
theorem theorem3_sector_coexistence :
    ∃ G : Fin 4 → Fin 4 → ℝ, ∃ T : Finset (Fin 4),
      IsCommonOriginKernel G ∧ SectorGeometry G T ∧ BellViolating G := by
        use chshKernel, {0, 2};
        refine' ⟨ chshKernel_isCommonOrigin, _, chshKernel_bellViolating ⟩;
        constructor <;> norm_num [ SectorPositive, SectorSubmult ];
        linarith [ sqrt2half_mul_self ]

end MainTheorems

-- ============================================================
-- Section 4: Rank-1 Obstruction (Theorem 6)
-- ============================================================

section Rank1

/-
PROBLEM
For a sign vector v (v(i) = ±1), the rank-1 kernel is Bell-trivial.
  This is because CHSH = v(A₀)(v(B₀)+v(B₁)) + v(A₁)(v(B₀)-v(B₁)),
  and one of the two terms is always zero.

PROVIDED SOLUTION
For v with v i = 1 ∨ v i = -1, CHSH = v(A0)*v(B0) + v(A0)*v(B1) + v(A1)*v(B0) - v(A1)*v(B1). Do cases on hv B.A0, hv B.A1, hv B.B0, hv B.B1 (4 binary choices = 16 cases). In each case, compute CHSH and verify |CHSH| ≤ 2. Each case gives CHSH = ±2.
-/
theorem rank1_sign_trivialBell {S : Type*} [Fintype S] [DecidableEq S]
    (v : S → ℝ) (hv : ∀ i, v i = 1 ∨ v i = -1) :
    TrivialBell (rank1Kernel v) := by
      intro B;
      unfold CHSH_value;
      cases hv B.A0 <;> cases hv B.A1 <;> cases hv B.B0 <;> cases hv B.B1 <;> simp +decide [ *, rank1Kernel ] <;> norm_num [ abs_le ]

/-
PROBLEM
**Theorem 6**: Rank-1 normalized PSD kernels are Bell-trivial.
  If G(i,j) = v(i)·v(j) with v(i)² = 1, then |CHSH(G)| ≤ 2 for all indices.

PROVIDED SOLUTION
From v i ^ 2 = 1, derive v i = 1 ∨ v i = -1 (by sq_eq_one_iff_of_ne_neg_one or by showing (v i - 1)(v i + 1) = 0). Then apply rank1_sign_trivialBell.
-/
theorem theorem6_rank1_obstruction {S : Type*} [Fintype S] [DecidableEq S]
    (v : S → ℝ) (hv : ∀ i, v i ^ 2 = 1) :
    TrivialBell (rank1Kernel v) := by
      have h_cases : ∀ i, v i = 1 ∨ v i = -1 := by
        exact fun i => sq_eq_one_iff.mp ( hv i )
      apply rank1_sign_trivialBell; assumption;

/-
PROBLEM
Rank-1 sign kernels satisfy GlobalGeometry.

PROVIDED SOLUTION
For v with v i = 1 ∨ v i = -1, |rank1Kernel v i j| = |v i * v j| = |v i| * |v j| = 1. AllPositive: 1 > 0. GlobalSubmult: |G(i,k)| = 1 ≥ 1 * 1 = |G(i,j)| * |G(j,k)|. Cases on the signs give |v i| = 1 always.
-/
theorem rank1_sign_globalGeometry {S : Type*} [Fintype S] [DecidableEq S]
    (v : S → ℝ) (hv : ∀ i, v i = 1 ∨ v i = -1) :
    GlobalGeometry (rank1Kernel v) := by
      refine' ⟨ _, _ ⟩;
      · exact fun i j => abs_pos.mpr ( mul_ne_zero ( by cases hv i <;> linarith ) ( by cases hv j <;> linarith ) );
      · intro i j k
        simp [rank1Kernel];
        cases hv i <;> cases hv j <;> cases hv k <;> simp +decide [ * ]

/-- **Assumption C confirmed**: Rank-1 kernels cannot support Bell violation.
  They are necessarily in the "geometry only" class. -/
theorem rank1_geometry_only {S : Type*} [Fintype S] [DecidableEq S]
    (v : S → ℝ) (hv : ∀ i, v i = 1 ∨ v i = -1) :
    GlobalGeometry (rank1Kernel v) ∧ TrivialBell (rank1Kernel v) :=
  ⟨rank1_sign_globalGeometry v hv, rank1_sign_trivialBell v hv⟩

end Rank1

-- ============================================================
-- Section 5: CHSH Kernel Failure Structure (Theorem 4)
-- ============================================================

section FailureStructure

/-
PROBLEM
**Theorem 4**: The triple (A₀, B₀, A₁) = (0, 2, 1) fails submultiplicativity
  in the CHSH kernel: |G(0,1)| < |G(0,2)| · |G(2,1)|, i.e., 0 < 1/2.

PROVIDED SOLUTION
|chshKernel 0 1| = |0| = 0. |chshKernel 0 2| * |chshKernel 2 1| = |√2/2| * |√2/2| = (√2/2)² = 1/2 > 0. So 0 < 1/2. Use simp [chshKernel] and sqrt2half_mul_self.
-/
theorem chshKernel_submult_fails_021 :
    |chshKernel 0 1| < |chshKernel 0 2| * |chshKernel 2 1| := by
      simp [chshKernel]

/-
PROBLEM
The triple (B₀, A₀, B₁) = (2, 0, 3) also fails submultiplicativity:
  |G(2,3)| < |G(2,0)| · |G(0,3)|, i.e., 0 < 1/2.

PROVIDED SOLUTION
|chshKernel 2 3| = |0| = 0. |chshKernel 2 0| * |chshKernel 0 3| = |√2/2| * |√2/2| = 1/2 > 0. So 0 < 1/2. Use simp [chshKernel] and sqrt2half_mul_self.
-/
theorem chshKernel_submult_fails_203 :
    |chshKernel 2 3| < |chshKernel 2 0| * |chshKernel 0 3| := by
      simp +zetaDelta at *

/-
PROBLEM
The obstruction set: submultiplicativity fails exactly on triples
  that "cross" through the orthogonal pairs (A₀,A₁) or (B₀,B₁).

PROVIDED SOLUTION
Exhaustive case analysis on all 64 triples (i,j,k) ∈ (Fin 4)³. For each triple, compute |chshKernel i k|, |chshKernel i j| * |chshKernel j k|, and check if the strict inequality holds. Use fin_cases on i, j, k, then simp [chshKernel] and norm_num with sqrt2half_mul_self. The failing triples are exactly those listed (the ones that cross through the orthogonal pairs).
-/
theorem chshKernel_submult_fails_iff (i j k : Fin 4) :
    |chshKernel i k| < |chshKernel i j| * |chshKernel j k| ↔
    (i = 0 ∧ j = 2 ∧ k = 1) ∨ (i = 0 ∧ j = 3 ∧ k = 1) ∨
    (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 1 ∧ j = 3 ∧ k = 0) ∨
    (i = 2 ∧ j = 0 ∧ k = 3) ∨ (i = 2 ∧ j = 1 ∧ k = 3) ∨
    (i = 3 ∧ j = 0 ∧ k = 2) ∨ (i = 3 ∧ j = 1 ∧ k = 2) := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp +decide [ * ] at *;
      all_goals rw [ show sqrt2half = Real.sqrt 2 / 2 by rfl ] ; ring_nf; norm_num;

end FailureStructure

-- ============================================================
-- Section 6: Sector Decomposition (Theorem 8)
-- ============================================================

section SectorDecomposition

/-
PROBLEM
The geometric sector {0, 2} = {A₀, B₀} satisfies SectorGeometry.

PROVIDED SOLUTION
T = {0, 2}. SectorPositive: for i,j ∈ {0,2}, |chshKernel i j| > 0. The values are |1| = 1 > 0 and |√2/2| = √2/2 > 0. SectorSubmult: for i,j,k ∈ {0,2}, check |G(i,k)| ≥ |G(i,j)|·|G(j,k)|. The possible values are 1 and √2/2. Need 1 ≥ 1·1 (impossible since 1=1, ok), 1 ≥ (√2/2)² = 1/2, √2/2 ≥ √2/2 · 1, etc. All hold. Use fin_cases or norm_num.
-/
theorem chshKernel_sector_02 :
    SectorGeometry chshKernel {0, 2} := by
      unfold SectorGeometry SectorPositive SectorSubmult;
      simp +zetaDelta at *;
      linarith [ sqrt2half_mul_self ]

/-- **Theorem 8**: The CHSH kernel admits a sector decomposition.
  T_geom = {A₀, B₀} has sector geometry,
  Bell violation is witnessed by the standard indices,
  and both sectors are part of the same kernel. -/
theorem theorem8_sector_decomposition :
    ∃ T_geom : Finset (Fin 4),
      SectorGeometry chshKernel T_geom ∧
      BellViolating chshKernel := by
  exact ⟨{0, 2}, chshKernel_sector_02, chshKernel_bellViolating⟩

end SectorDecomposition

-- ============================================================
-- Section 7: Necessary Conditions (Theorem 10)
-- ============================================================

section NecessaryConditions

/-
PROBLEM
**Theorem 10**: If a kernel has both GlobalGeometry and BellViolating,
  then it cannot be rank-1.
  (A necessary condition for global coexistence is rank > 1.)

PROVIDED SOLUTION
Assume for contradiction that G i j = v i * v j for all i,j. By theorem6_rank1_obstruction, TrivialBell G (since v i ^ 2 = 1). But hG.2 says BellViolating G, i.e., ∃ B, |CHSH G B| > 2. This contradicts TrivialBell (∀ B, |CHSH G B| ≤ 2). The contradiction gives ¬(∀ i j, G i j = v i * v j).
-/
theorem theorem10_not_rank1 {S : Type*} [Fintype S] [DecidableEq S]
    (G : S → S → ℝ) (hG : GlobalCoexistence G) (v : S → ℝ)
    (hv : ∀ i, v i ^ 2 = 1) :
    ¬(∀ i j, G i j = v i * v j) := by
      intro h;
      have h_trivialBell : TrivialBell G := by
        rw [ show G = _ from funext fun i => funext fun j => h i j ] ; exact theorem6_rank1_obstruction v hv;
      exact absurd ( hG.2.choose_spec ) ( not_lt_of_ge ( h_trivialBell _ ) )

end NecessaryConditions

-- ============================================================
-- Section 8: Maximal CHSH No-Go (Theorem 11)
-- ============================================================

section MaximalCHSH

/-
PROBLEM
**Theorem 11 (weak form)**: The CHSH-optimal kernel (achieving maximal
  CHSH = 2√2) does not satisfy GlobalGeometry.
  This shows maximal quantum nonlocality and global metric emergence
  are incompatible in this specific construction.

PROVIDED SOLUTION
Split into two parts. (1) CHSH = 2√2: rewrite using chshKernel_CHSH_value and four_sqrt2half_eq. (2) ¬GlobalGeometry: use chshKernel_not_globalGeometry.
-/
theorem theorem11_weak_maximal_chsh_no_geometry :
    CHSH_value chshKernel stdBellIndices = 2 * Real.sqrt 2 ∧
    ¬GlobalGeometry chshKernel := by
      exact ⟨ by rw [ chshKernel_CHSH_value, four_sqrt2half_eq ], chshKernel_not_globalGeometry ⟩

/-
PROBLEM
From PSD + symmetric + normalized: -1 ≤ G 0 1, proved via c = (1, 1, 0, 0).

PROVIDED SOLUTION
From PSD with c = ![1, 1, 0, 0] (supported on indices 0,1):
0 ≤ ∑ i, ∑ j, c i * G i j * c j
Expanding (using Fin.sum_univ_four): = G 0 0 + G 0 1 + G 1 0 + G 1 1 = 1 + G 0 1 + G 0 1 + 1 = 2 + 2 * G 0 1 (using symmetry: G 1 0 = G 0 1, and normalization: G 0 0 = G 1 1 = 1).
So 2 + 2 * G 0 1 ≥ 0, hence G 0 1 ≥ -1.
-/
lemma psd_alpha_lb (G : Fin 4 → Fin 4 → ℝ) (hG : IsCommonOriginKernel G) :
    -1 ≤ G 0 1 := by
      have := hG.psd ![1, 1, 0, 0];
      norm_num [ Fin.sum_univ_succ ] at this;
      linarith [ hG.normalized 0, hG.normalized 1, hG.symmetric 0 1 ]

/-
PROBLEM
From PSD + symmetric + normalized: G 0 1 ≤ 1, proved via c = (1, -1, 0, 0).

PROVIDED SOLUTION
From PSD with c = ![1, -1, 0, 0]:
0 ≤ ∑ i, ∑ j, c i * G i j * c j
= G 0 0 - G 0 1 - G 1 0 + G 1 1 = 1 - G 0 1 - G 0 1 + 1 = 2 - 2 * G 0 1.
So G 0 1 ≤ 1.
-/
lemma psd_alpha_ub (G : Fin 4 → Fin 4 → ℝ) (hG : IsCommonOriginKernel G) :
    G 0 1 ≤ 1 := by
      have := hG.psd ![1, -1, 0, 0];
      norm_num [ Fin.sum_univ_succ ] at this;
      linarith! [ hG.normalized 0, hG.normalized 1, hG.symmetric 0 1 ]

/-
PROBLEM
Key bound: (G 0 2 + G 1 2)² ≤ 2 + 2 · G 0 1.
  Proved via PSD with c = (t, t, -1, 0): the resulting quadratic in t
  has non-negative discriminant condition.

PROVIDED SOLUTION
From PSD with c = ![t, t, -1, 0] for all real t:
0 ≤ ∑ i, ∑ j, c i * G i j * c j.
Expanding with Fin.sum_univ_four and using symmetry+normalization:
= 2*t^2*(1 + G 0 1) - 2*t*(G 0 2 + G 1 2) + 1.
This is a quadratic in t of the form a*t^2 + b*t + c ≥ 0 for all t.
For a quadratic at^2+bt+c ≥ 0 for all t with a > 0, the discriminant b^2-4ac ≤ 0.
Here: a = 2*(1+G 0 1), b_coeff = -2*(G 0 2+G 1 2), constant = 1.
Discriminant: 4*(G 0 2+G 1 2)^2 - 4*2*(1+G 0 1) ≤ 0.
So (G 0 2+G 1 2)^2 ≤ 2+2*G 0 1.
Key: specialize hG.psd at the specific function t ↦ ![t, t, -1, 0] and derive the discriminant bound.
-/
lemma chsh_sum_sq_bound (G : Fin 4 → Fin 4 → ℝ) (hG : IsCommonOriginKernel G) :
    (G 0 2 + G 1 2) ^ 2 ≤ 2 + 2 * G 0 1 := by
      -- By the properties of the quadratic function, we know that if the quadratic is non-negative for all t, then its discriminant must be non-positive.
      have h_discriminant : ∀ t : ℝ, (2 * (1 + G 0 1)) * t^2 - 2 * (G 0 2 + G 1 2) * t + 1 ≥ 0 := by
        intro t;
        have := hG.psd ( fun i => if i = 0 then t else if i = 1 then t else if i = 2 then -1 else 0 ) ; simp_all +decide [ Fin.sum_univ_four ];
        have := hG.normalized 0; have := hG.normalized 1; have := hG.normalized 2; have := hG.normalized 3; have := hG.symmetric 0 1; have := hG.symmetric 0 2; have := hG.symmetric 0 3; have := hG.symmetric 1 2; have := hG.symmetric 1 3; have := hG.symmetric 2 3; simp_all +decide ; nlinarith;
      by_cases h : 1 + G 0 1 = 0;
      · contrapose! h_discriminant;
        exact ⟨ ( 1 + 1 ) / ( 2 * ( G 0 2 + G 1 2 ) ), by nlinarith [ mul_div_cancel₀ ( 1 + 1 ) ( by nlinarith : ( 2 * ( G 0 2 + G 1 2 ) ) ≠ 0 ) ] ⟩;
      · contrapose! h_discriminant;
        exact ⟨ ( G 0 2 + G 1 2 ) / ( 2 * ( 1 + G 0 1 ) ), by nlinarith [ mul_div_cancel₀ ( G 0 2 + G 1 2 ) ( mul_ne_zero two_ne_zero h ), show 0 < 1 + G 0 1 from lt_of_le_of_ne ( by linarith [ psd_alpha_lb G hG ] ) ( Ne.symm h ) ] ⟩

/-
PROBLEM
Key bound: (G 0 3 - G 1 3)² ≤ 2 - 2 · G 0 1.
  Proved via PSD with c = (t, -t, 0, -1): the resulting quadratic in t
  has non-negative discriminant condition.

PROVIDED SOLUTION
From PSD with c = ![t, -t, 0, -1] for all real t:
0 ≤ ∑ i, ∑ j, c i * G i j * c j.
Expanding: = 2*t^2*(1 - G 0 1) - 2*t*(G 0 3 - G 1 3) + 1.
Discriminant ≤ 0: 4*(G 0 3 - G 1 3)^2 - 4*2*(1 - G 0 1) ≤ 0.
So (G 0 3 - G 1 3)^2 ≤ 2 - 2*G 0 1.
-/
lemma chsh_diff_sq_bound (G : Fin 4 → Fin 4 → ℝ) (hG : IsCommonOriginKernel G) :
    (G 0 3 - G 1 3) ^ 2 ≤ 2 - 2 * G 0 1 := by
      -- From PSD with c = ![t, -t, 0, -1] for all real t:
      -- 0 ≤ ∑ i, ∑ j, c i * G i j * c j.
      -- Expanding and simplifying:
      have h_quad : ∀ t : ℝ, 0 ≤ 2 * t^2 * (1 - G 0 1) - 2 * t * (G 0 3 - G 1 3) + 1 := by
        intro t
        have := hG.psd (fun i => if i = 0 then t else if i = 1 then -t else if i = 2 then 0 else -1);
        simp +decide [ Fin.sum_univ_four ] at this;
        convert this using 1 ; rw [ hG.normalized 0, hG.normalized 1, hG.normalized 3 ] ; rw [ hG.symmetric 0 1, hG.symmetric 0 3, hG.symmetric 1 3 ] ; ring;
      by_cases h : 1 - G 0 1 = 0;
      · contrapose! h_quad;
        exact ⟨ 1 / ( G 0 3 - G 1 3 ), by rw [ h ] ; nlinarith [ mul_div_cancel₀ 1 ( by nlinarith : ( G 0 3 - G 1 3 ) ≠ 0 ) ] ⟩;
      · by_cases h₂ : 1 - G 0 1 > 0;
        · nlinarith [ h_quad ( ( G 0 3 - G 1 3 ) / ( 2 * ( 1 - G 0 1 ) ) ), mul_div_cancel₀ ( G 0 3 - G 1 3 ) ( mul_ne_zero two_ne_zero h ) ];
        · grind +suggestions

/-
PROBLEM
For -1 ≤ α ≤ 1: √(2+2α) + √(2-2α) ≤ 2√2.

PROVIDED SOLUTION
By Cauchy-Schwarz (or direct squaring):
(√(2+2α) + √(2-2α))² = (2+2α) + (2-2α) + 2·√((2+2α)(2-2α))
= 4 + 2·√(4-4α²) ≤ 4 + 2·√4 = 4 + 4 = 8 = (2√2)².
Since both sides are non-negative, take square roots.
Use Real.sqrt_le_sqrt and nlinarith with Real.sq_sqrt.
-/
lemma sqrt_sum_le (α : ℝ) (hα1 : -1 ≤ α) (hα2 : α ≤ 1) :
    Real.sqrt (2 + 2 * α) + Real.sqrt (2 - 2 * α) ≤ 2 * Real.sqrt 2 := by
      nlinarith [ sq_nonneg ( Real.sqrt ( 2 + 2 * α ) - Real.sqrt ( 2 - 2 * α ) ), Real.mul_self_sqrt ( show 0 ≤ 2 + 2 * α by linarith ), Real.mul_self_sqrt ( show 0 ≤ 2 - 2 * α by linarith ), Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ]

/-
PROBLEM
If √(2+2α) + √(2-2α) = 2√2 then α = 0.

PROVIDED SOLUTION
If √(2+2α) + √(2-2α) = 2√2, squaring both sides:
4 + 2√(4-4α²) = 8, so √(4-4α²) = 2, so 4-4α² = 4, so α² = 0, so α = 0.
Use the identity (a+b)² = a²+b²+2ab, then Real.sqrt properties.
-/
lemma sqrt_sum_eq_implies_zero (α : ℝ) (hα1 : -1 ≤ α) (hα2 : α ≤ 1) :
    Real.sqrt (2 + 2 * α) + Real.sqrt (2 - 2 * α) = 2 * Real.sqrt 2 → α = 0 := by
      intro h_eq
      have h_sq : (Real.sqrt (2 + 2 * α) + Real.sqrt (2 - 2 * α))^2 = (2 * Real.sqrt 2)^2 := by
        rw [h_eq];
      ring_nf at h_sq;
      rw [ Real.sq_sqrt ( by linarith ), Real.sq_sqrt ( by linarith ), Real.sq_sqrt ( by linarith ) ] at h_sq ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 + α * 2 by linarith ), Real.mul_self_sqrt ( show 0 ≤ 2 - α * 2 by linarith ) ]

/-
PROBLEM
**Theorem 11 (structural form)**: Any normalized PSD kernel achieving
  CHSH = 2√2 must have zero entries at the A₀-A₁ pair,
  which prevents GlobalGeometry.

  Proof: (1) PSD gives (G 0 2 + G 1 2)² ≤ 2+2α, (G 0 3 - G 1 3)² ≤ 2-2α
  where α = G 0 1. (2) CHSH ≤ |G 0 2 + G 1 2| + |G 0 3 - G 1 3|
  ≤ √(2+2α) + √(2-2α) ≤ 2√2. (3) CHSH = 2√2 forces α = 0.

PROVIDED SOLUTION
Let α = G 0 1.
1. From chsh_sum_sq_bound: (G 0 2 + G 1 2)^2 ≤ 2+2α
2. From chsh_diff_sq_bound: (G 0 3 - G 1 3)^2 ≤ 2-2α
3. So |G 0 2 + G 1 2| ≤ √(2+2α) and |G 0 3 - G 1 3| ≤ √(2-2α)
4. CHSH = (G 0 2 + G 1 2) + (G 0 3 - G 1 3) ≤ |G 0 2 + G 1 2| + |G 0 3 - G 1 3|
   ≤ √(2+2α) + √(2-2α)
5. From sqrt_sum_le: √(2+2α) + √(2-2α) ≤ 2√2
6. Since CHSH = 2√2 (from hmax, after unfolding CHSH_value and stdBellIndices), all inequalities are equalities.
7. By sqrt_sum_eq_implies_zero: α = 0.

Use psd_alpha_lb and psd_alpha_ub for the bounds on α.
-/
theorem theorem11_maximal_chsh_forces_zero (G : Fin 4 → Fin 4 → ℝ)
    (hG : IsCommonOriginKernel G)
    (hmax : CHSH_value G stdBellIndices = 2 * Real.sqrt 2) :
    G 0 1 = 0 := by
      -- From the provided solution, we know that if the CHSH value is 2√2, then α must be 0.
      have h_alpha_zero : G 0 1 = 0 := by
        have h_sqrt_sum_eq : Real.sqrt (2 + 2 * G 0 1) + Real.sqrt (2 - 2 * G 0 1) = 2 * Real.sqrt 2 := by
          refine' le_antisymm _ _;
          · apply_rules [ sqrt_sum_le, psd_alpha_lb, psd_alpha_ub ];
          · -- By definition of CHSH_value, we have:
            have h_CHSH_def : G 0 2 + G 0 3 + G 1 2 - G 1 3 = 2 * Real.sqrt 2 := by
              exact hmax;
            rw [ ← h_CHSH_def ];
            have h_sqrt_sum : (G 0 2 + G 1 2) ^ 2 ≤ 2 + 2 * G 0 1 ∧ (G 0 3 - G 1 3) ^ 2 ≤ 2 - 2 * G 0 1 := by
              exact ⟨ chsh_sum_sq_bound G hG, chsh_diff_sq_bound G hG ⟩;
            linarith [ show Real.sqrt ( 2 + 2 * G 0 1 ) ≥ G 0 2 + G 1 2 by exact Real.le_sqrt_of_sq_le h_sqrt_sum.1, show Real.sqrt ( 2 - 2 * G 0 1 ) ≥ G 0 3 - G 1 3 by exact Real.le_sqrt_of_sq_le h_sqrt_sum.2 ]
        apply sqrt_sum_eq_implies_zero (G 0 1) (psd_alpha_lb G hG) (psd_alpha_ub G hG) h_sqrt_sum_eq;
      exact h_alpha_zero

end MaximalCHSH

-- ============================================================
-- Section 9: Assumption Verification
-- ============================================================

section Assumptions

/-- **Assumption A is FALSE**: Bell violation and global geometry are NOT
  automatically compatible. The CHSH kernel violates Bell but fails geometry. -/
theorem assumptionA_false :
    ∃ G : Fin 4 → Fin 4 → ℝ,
      IsCommonOriginKernel G ∧ BellViolating G ∧ ¬GlobalGeometry G :=
  theorem1_bell_not_geometry

/-
PROBLEM
**Assumption B is FALSE sectorally**: A common-origin kernel CAN support
  sector geometry and Bell violation simultaneously.

PROVIDED SOLUTION
Use G = chshKernel. SectoralCoexistence G = (∃ T, SectorGeometry G T) ∧ BellViolating G. For the first part, use T = {0, 2} and chshKernel_sector_02. For the second, use chshKernel_bellViolating.
-/
theorem assumptionB_false_sectoral :
    ∃ G : Fin 4 → Fin 4 → ℝ, SectoralCoexistence G := by
      use chshKernel;
      exact ⟨ ⟨ { 0, 2 }, chshKernel_sector_02 ⟩, chshKernel_bellViolating ⟩

/-- **Assumption C is TRUE**: Rank-1 (sign) kernels cannot support Bell violation.
  They are necessarily Bell-trivial. -/
theorem assumptionC_true {S : Type*} [Fintype S] [DecidableEq S]
    (v : S → ℝ) (hv : ∀ i, v i = 1 ∨ v i = -1) :
    TrivialBell (rank1Kernel v) :=
  rank1_sign_trivialBell v hv

/-- **Assumption D**: Maximal CHSH and global submultiplicativity are
  incompatible (at least for the standard CHSH-optimal construction). -/
theorem assumptionD_evidence :
    CHSH_value chshKernel stdBellIndices = 2 * Real.sqrt 2 ∧
    ¬GlobalGeometry chshKernel :=
  theorem11_weak_maximal_chsh_no_geometry

/-- **Assumption E evidence**: Bell nonlocality and geometry are indeed
  different sectors of one object (the CHSH kernel). -/
theorem assumptionE_evidence :
    ∃ T_geom : Finset (Fin 4),
      SectorGeometry chshKernel T_geom ∧ BellViolating chshKernel :=
  theorem8_sector_decomposition

end Assumptions

-- ============================================================
-- Section 10: Family Analysis
-- ============================================================

section Families

/-- **Family A**: Constant kernel has global geometry and is Bell-trivial. -/
theorem familyA_constant :
    GlobalGeometry (constKernel (Fin 4)) ∧ TrivialBell (constKernel (Fin 4)) :=
  ⟨constKernel_globalGeometry (Fin 4), constKernel_trivialBell⟩

/-- **Family A**: Rank-1 sign kernel has global geometry and is Bell-trivial. -/
theorem familyA_rank1 {S : Type*} [Fintype S] [DecidableEq S]
    (v : S → ℝ) (hv : ∀ i, v i = 1 ∨ v i = -1) :
    GlobalGeometry (rank1Kernel v) ∧ TrivialBell (rank1Kernel v) :=
  rank1_geometry_only v hv

/-- **Family C**: CHSH Gram family is Bell-violating but lacks global geometry. -/
theorem familyC_chsh :
    BellViolating chshKernel ∧ ¬GlobalGeometry chshKernel :=
  ⟨chshKernel_bellViolating, chshKernel_not_globalGeometry⟩

end Families

-- ============================================================
-- Section 11: Summary Classification
-- ============================================================

section Summary

/-- The three main non-implications:
  1. BellViolating ⇏ GlobalGeometry
  2. GlobalGeometry ⇏ BellViolating
  3. SectorGeometry + BellViolating can coexist -/
theorem classification_summary :
    (∃ G : Fin 4 → Fin 4 → ℝ,
      IsCommonOriginKernel G ∧ BellViolating G ∧ ¬GlobalGeometry G) ∧
    (∃ G : Fin 4 → Fin 4 → ℝ,
      IsCommonOriginKernel G ∧ GlobalGeometry G ∧ TrivialBell G) ∧
    (∃ G : Fin 4 → Fin 4 → ℝ, ∃ T : Finset (Fin 4),
      IsCommonOriginKernel G ∧ SectorGeometry G T ∧ BellViolating G) :=
  ⟨theorem1_bell_not_geometry, theorem2_geometry_not_bell, theorem3_sector_coexistence⟩

end Summary

end CommonOrigin