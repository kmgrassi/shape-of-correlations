import RequestProject.Defs

/-!
# Basic Properties of ApproxSubmult and muParam

## Theorems proved:
- `approxSubmult_zero`: ApproxSubmult 0 always holds
- `approxSubmult_le`: monotonicity in μ
- `approxSubmult_one_iff_exact`: μ = 1 ⟺ exact submultiplicativity (Theorem 2)
- `approxSubmult_only_zero`: characterization of μ(G) = 0 (Theorem 3)
- `muParam_set_nonempty`: the feasible set is nonempty
- `muParam_set_bddAbove`: the feasible set is bounded above
- `muParam_nonneg`: μ(G) ≥ 0
- `approxSubmult_muParam`: the supremum is achieved (Theorem A)
- `muParam_is_maximal`: μ(G) is the maximal consistency parameter (Theorem A)
- `muParam_eq_sInf_ratio`: μ(G) equals infimum of ratios (Theorem A, alternate form)
-/

noncomputable section

open Real

variable {α : Type*}

/-! ## Basic structural lemmas -/

/-- ApproxSubmult 0 always holds since absolute values are nonneg. -/
theorem approxSubmult_zero (G : α → α → ℝ) : ApproxSubmult 0 G :=
  fun i j k => le_trans (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)

/-- If ApproxSubmult μ holds and 0 ≤ μ' ≤ μ, then ApproxSubmult μ' holds. -/
theorem approxSubmult_le {μ μ' : ℝ} {G : α → α → ℝ}
    (hle : μ' ≤ μ) (_hμ' : 0 ≤ μ') (hG : ApproxSubmult μ G) :
    ApproxSubmult μ' G :=
  fun i j k => le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) (abs_nonneg _)) (hG i j k)

/-! ## Theorem 2: μ = 1 iff exact submultiplicativity -/

/-- ApproxSubmult 1 G is equivalent to ExactSubmult G. -/
theorem approxSubmult_one_iff_exact (G : α → α → ℝ) :
    ApproxSubmult 1 G ↔ ExactSubmult G := by
  unfold ApproxSubmult ExactSubmult; aesop

/-! ## Theorem 3: μ = 0 characterization -/

/-- If for every ε > 0 there exist i,j,k with |G(i,k)| < ε · |G(i,j)| · |G(j,k)|,
    then no positive μ satisfies ApproxSubmult μ G. This characterizes μ(G) = 0
    as complete failure of uniform geometric consistency. -/
theorem approxSubmult_only_zero {G : α → α → ℝ}
    (h : ∀ ε > 0, ∃ i j k, |G i k| < ε * |G i j| * |G j k|) :
    ∀ μ, 0 < μ → ¬ApproxSubmult μ G :=
  fun μ hμ hμ' => by rcases h μ hμ with ⟨i, j, k, hk⟩; linarith [hμ' i j k]

/-! ## Theorem A: muParam is the maximal consistency parameter -/

/-- The set {μ ≥ 0 | ApproxSubmult μ G} is nonempty (it contains 0). -/
theorem muParam_set_nonempty (G : α → α → ℝ) :
    (0 : ℝ) ∈ {μ : ℝ | 0 ≤ μ ∧ ApproxSubmult μ G} :=
  ⟨le_rfl, approxSubmult_zero G⟩

/-- When a kernel has a non-degenerate triple, the feasible set is bounded above
    by the consistency ratio at that triple. -/
theorem muParam_set_bddAbove {G : α → α → ℝ} (hnd : HasNondegTriple G) :
    BddAbove {μ : ℝ | 0 ≤ μ ∧ ApproxSubmult μ G} := by
  obtain ⟨i, j, k, h_pos⟩ := hnd
  exact ⟨|G i k| / (|G i j| * |G j k|),
    fun μ hμ => by rw [le_div_iff₀ h_pos]; linarith [hμ.2 i j k]⟩

/-- muParam G is nonneg. -/
theorem muParam_nonneg {G : α → α → ℝ} (hnd : HasNondegTriple G) :
    0 ≤ muParam G :=
  le_trans (by norm_num) (le_csSup (muParam_set_bddAbove hnd) (muParam_set_nonempty G))

/-- The supremum is achieved: ApproxSubmult (muParam G) G holds.
    For each triple, either the denominator vanishes (making the RHS zero)
    or the sup is bounded by the ratio at that triple. -/
theorem approxSubmult_muParam [Fintype α] {G : α → α → ℝ} (hnd : HasNondegTriple G) :
    ApproxSubmult (muParam G) G := by
  intro i j k
  by_cases h : |G i j| * |G j k| = 0 <;> simp_all +decide [mul_assoc]
  · cases h <;> simp +decide [*]
  · refine' le_trans (mul_le_mul_of_nonneg_right (csSup_le _ _)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))) _
    exact |G i k| / (|G i j| * |G j k|)
    · exact ⟨0, ⟨le_rfl, approxSubmult_zero G⟩⟩
    · exact fun μ hμ => by
        rw [le_div_iff₀ (mul_pos (abs_pos.mpr h.1) (abs_pos.mpr h.2))]
        linarith [hμ.2 i j k]
    · rw [div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt (abs_pos.mpr h.1)) (ne_of_gt (abs_pos.mpr h.2)))]

/-- muParam G is the maximal nonneg constant for which ApproxSubmult holds:
    any μ ≥ 0 with ApproxSubmult μ G satisfies μ ≤ muParam G. -/
theorem muParam_is_maximal {G : α → α → ℝ} (hnd : HasNondegTriple G)
    {μ : ℝ} (hμ : 0 ≤ μ) (hG : ApproxSubmult μ G) :
    μ ≤ muParam G :=
  le_csSup (muParam_set_bddAbove hnd) ⟨hμ, hG⟩

/-! ## Theorem A, alternate form: muParam equals the infimum of ratios -/

/-- **Theorem A (intrinsic formula)**: For a kernel with a non-degenerate triple,
    μ(G) = inf { |G(i,k)| / (|G(i,j)| · |G(j,k)|) : (i,j,k) non-degenerate }.
    This shows μ(G) is an intrinsic property of the kernel, not an arbitrary parameter. -/
theorem muParam_eq_sInf_ratio {G : α → α → ℝ} (hnd : HasNondegTriple G) :
    muParam G = sInf {r : ℝ | ∃ i j k, |G i j| * |G j k| > 0 ∧
      r = |G i k| / (|G i j| * |G j k|)} := by
  refine' le_antisymm _ _
  · refine' le_csInf _ _
    · exact ⟨_, ⟨hnd.choose, hnd.choose_spec.choose,
        hnd.choose_spec.choose_spec.choose, hnd.choose_spec.choose_spec.choose_spec, rfl⟩⟩
    · rintro _ ⟨i, j, k, h, rfl⟩
      refine' csSup_le _ _ <;> norm_num
      · exact ⟨0, ⟨le_rfl, approxSubmult_zero G⟩⟩
      · exact fun b hb hb' => by rw [le_div_iff₀ h]; linarith [hb' i j k]
  · refine' le_csSup _ _
    · exact muParam_set_bddAbove hnd
    · refine' ⟨_, _⟩
      · exact le_csInf
          ⟨_, ⟨hnd.choose, hnd.choose_spec.choose, hnd.choose_spec.choose_spec.choose,
            hnd.choose_spec.choose_spec.choose_spec, rfl⟩⟩
          (by rintro x ⟨i, j, k, hk, rfl⟩
              exact div_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      · intro i j k
        by_cases h : |G i j| * |G j k| = 0 <;> simp_all +decide [div_le_iff₀]
        · cases h <;> simp +decide [*]
        · rw [mul_assoc]
          exact le_trans (mul_le_mul_of_nonneg_right
            (csInf_le ⟨0, by rintro x ⟨i, j, k, hk, rfl⟩; positivity⟩
              ⟨i, j, k, by aesop, rfl⟩)
            (by positivity))
            (by rw [div_mul_cancel₀ _ (by aesop)])

end
