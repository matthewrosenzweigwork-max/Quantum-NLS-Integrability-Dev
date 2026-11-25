import LiebLiniger.FixedPeriod.Quantum.MixedTensor
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
Actual occupation vectors inside the project's spatial symmetric sectors.
No basis-completeness, Fock-factorization, partial-trace, or trace identity is assumed.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ComplexConjugate

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Literal occupation counts of a finite tensor word. -/
def occupationWordCount {n d : ℕ} (f : Fin n → Fin d) (j : Fin d) : ℕ :=
  Fintype.card {i : Fin n // f i = j}

/-- The actual symmetrized mixed spatial tensor associated to an occupation word. -/
def occupationWordVector {n d : ℕ} (e : Fin d → Lp ℂ 2 μ) (f : Fin n → Fin d) :
    SymmetricSector μ n :=
  symmetricTensorContinuousMultilinear μ n (fun i => e (f i))

/-- A pure symmetric tensor tests an occupation word by the genuine one-particle inner products. -/
theorem occupationWordVector_inner_pure {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (f : Fin n → Fin d) (u : Lp ℂ 2 μ) :
    inner ℂ (occupationWordVector μ e f) (pureSymmetricTensor μ n u) =
      ∏ i, inner ℂ (e (f i)) u := by
  change inner ℂ (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (f i))))
    (pureTensorL2 μ u) = _
  have hs := (symmetrizeL2_isSymmetric μ)
    (mixedTensorL2 μ (fun i => e (f i))) (pureTensorL2 (ι := Fin n) μ u)
  change inner ℂ (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (f i))))
    (pureTensorL2 (ι := Fin n) μ u) =
    inner ℂ (mixedTensorL2 μ (fun i => e (f i)))
      (symmetrizeL2 μ (pureTensorL2 (ι := Fin n) μ u)) at hs
  rw [hs, symmetrizeL2_pureTensorL2]
  rw [← mixedTensorL2_diagonal μ u, inner_mixedTensorL2]

/-- Grouping equal one-particle factors gives precisely the occupation powers. -/
theorem occupationWordVector_inner_pure_counts {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (f : Fin n → Fin d) (u : Lp ℂ 2 μ) :
    inner ℂ (occupationWordVector μ e f) (pureSymmetricTensor μ n u) =
      ∏ j, (inner ℂ (e j) u) ^ occupationWordCount f j := by
  rw [occupationWordVector_inner_pure]
  have h := Fintype.prod_fiberwise' f (fun j => inner ℂ (e j) u)
  simp only [Finset.prod_const, Finset.card_univ] at h
  exact h.symm

/-- The finite permutation-average Gram formula on actual symmetric tensors. -/
theorem occupationWordVector_inner {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (f g : Fin n → Fin d) :
    inner ℂ (occupationWordVector μ e f) (occupationWordVector μ e g) =
      (n.factorial : ℂ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n), ∏ i, inner ℂ (e (f i)) (e (g (σ.symm i))) := by
  change inner ℂ (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (f i))))
    (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (g i)))) = _
  have hs := (symmetrizeL2_isSymmetric μ)
    (mixedTensorL2 μ (fun i => e (f i)))
    (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (g i))))
  change inner ℂ (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (f i))))
    (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (g i)))) =
    inner ℂ (mixedTensorL2 μ (fun i => e (f i)))
      (symmetrizeL2 μ (symmetrizeL2 μ (mixedTensorL2 μ (fun i => e (g i))))) at hs
  rw [hs, symmetrizeL2_idempotent,
    symmetrizeL2_apply_fin, inner_smul_right, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [permutationL2_mixedTensorL2, inner_mixedTensorL2]

/-- Counting permutations that preserve a word gives the exact occupation norm factor. -/
theorem occupationWordVector_norm_sq {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (he : Orthonormal ℂ e) (f : Fin n → Fin d) :
    ‖occupationWordVector μ e f‖ ^ 2 =
      (∏ j, (occupationWordCount f j).factorial : ℝ) / (n.factorial : ℝ) := by
  have h := occupationWordVector_inner μ e f f
  have hprod (σ : Equiv.Perm (Fin n)) :
      (∏ i, inner ℂ (e (f i)) (e (f (σ.symm i)))) =
        if f ∘ σ = f then (1 : ℂ) else 0 := by
    by_cases hfix : f ∘ σ = f
    · rw [ite_eq_left hfix]
      apply Finset.prod_eq_one
      intro i hi
      have hi' : f (σ.symm i) = f i := by
        have h' := congrFun hfix (σ.symm i)
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h'.symm
      rw [hi']
      rw [inner_self_eq_norm_sq_to_K, he.norm_eq_one]
      norm_num
    · rw [ite_eq_right hfix]
      have hne : ∃ i, f i ≠ f (σ.symm i) := by
        by_contra hn
        push Not at hn
        apply hfix
        funext i
        have h' := hn (σ i)
        simpa only [Equiv.symm_apply_apply, Function.comp_apply] using h'
      obtain ⟨i, hi⟩ := hne
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact he.inner_eq_zero hi
  rw [Finset.sum_congr rfl (fun σ _ => hprod σ)] at h
  have hc : (∑ σ : Equiv.Perm (Fin n), if f ∘ σ = f then (1 : ℂ) else 0) =
      (Fintype.card {σ : Equiv.Perm (Fin n) // f ∘ σ = f} : ℂ) := by
    simp only [Finset.sum_boole, Fintype.card_subtype]
  rw [hc, DomMulAct.stabilizer_card f] at h
  have hAmb : inner ℂ
      (occupationWordVector μ e f : ProductL2 μ (Fin n))
      (occupationWordVector μ e f : ProductL2 μ (Fin n)) =
      (n.factorial : ℂ)⁻¹ *
        ((∏ j, (Fintype.card {i : Fin n // f i = j}).factorial : ℕ) : ℂ) := h
  have hcast : (n.factorial : ℂ)⁻¹ *
      ((∏ j, (Fintype.card {i : Fin n // f i = j}).factorial : ℕ) : ℂ) =
      (((∏ j, (occupationWordCount f j).factorial : ℝ) / (n.factorial : ℝ)) : ℂ) := by
    simp only [occupationWordCount, Nat.cast_prod]
    push_cast
    ring
  rw [hcast] at hAmb
  change ‖(occupationWordVector μ e f : ProductL2 μ (Fin n))‖ ^ 2 = _
  calc
    _ = (inner ℂ (occupationWordVector μ e f : ProductL2 μ (Fin n))
        (occupationWordVector μ e f : ProductL2 μ (Fin n))).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := by
      have hr := congrArg Complex.re hAmb
      simpa only [← Complex.ofReal_div, Complex.ofReal_re] using hr

/-- Source-normalized occupation vector in the actual spatial symmetric sector. -/
def normalizedOccupationWordVector {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (f : Fin n → Fin d) : SymmetricSector μ n :=
  (Real.sqrt ((n.factorial : ℝ) / ∏ j, (occupationWordCount f j).factorial) : ℂ) •
    occupationWordVector μ e f

/-- The normalized occupation vector has unit norm, including the vacuum word. -/
theorem normalizedOccupationWordVector_norm {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (he : Orthonormal ℂ e) (f : Fin n → Fin d) :
    ‖normalizedOccupationWordVector μ e f‖ = 1 := by
  have hpos : 0 < (∏ j, ((occupationWordCount f j).factorial : ℝ)) := by positivity
  have hn : 0 < (n.factorial : ℝ) := by positivity
  have hs : ‖normalizedOccupationWordVector μ e f‖ ^ 2 = 1 := by
    unfold normalizedOccupationWordVector
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity),
      occupationWordVector_norm_sq μ e he f]
    simp only [Nat.cast_prod]
    field_simp [hpos.ne', hn.ne']
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hs)

/-- Every actual occupation word has exactly the source total particle count. -/
theorem occupationWordCount_sum {n d : ℕ} (f : Fin n → Fin d) :
    ∑ j, occupationWordCount f j = n := by
  calc
    (∑ j, occupationWordCount f j) =
        Fintype.card (Σ j : Fin d, {i : Fin n // f i = j}) := by
      rw [Fintype.card_sigma]
      rfl
    _ = Fintype.card (Fin n) := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    _ = n := Fintype.card_fin n

/-- Relabeling particle positions preserves each actual occupation count. -/
theorem occupationWordCount_permutation {n d : ℕ} (f : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) : occupationWordCount (f ∘ σ) = occupationWordCount f := by
  funext j
  unfold occupationWordCount
  apply Fintype.card_congr
  exact
    { toFun := fun i => ⟨σ i.1, i.2⟩
      invFun := fun i => ⟨σ.symm i.1, by simpa only [Function.comp_apply,
        Equiv.apply_symm_apply] using i.2⟩
      left_inv := fun i => by
        apply Subtype.ext
        change σ.symm (σ i.val) = i.val
        exact σ.symm_apply_apply i.val
      right_inv := fun i => by
        apply Subtype.ext
        change σ (σ.symm i.val) = i.val
        exact σ.apply_symm_apply i.val }

/-- Distinct occupations are orthogonal in the actual symmetric sector. -/
theorem occupationWordVector_inner_eq_zero {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (he : Orthonormal ℂ e) (f g : Fin n → Fin d)
    (hfg : occupationWordCount f ≠ occupationWordCount g) :
    inner ℂ (occupationWordVector μ e f) (occupationWordVector μ e g) = 0 := by
  rw [occupationWordVector_inner]
  suffices (∑ σ : Equiv.Perm (Fin n),
      ∏ i, inner ℂ (e (f i)) (e (g (σ.symm i)))) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro σ hσ
  have hne : ∃ i, f i ≠ g (σ.symm i) := by
    by_contra hn
    push Not at hn
    have hwords : f = g ∘ σ.symm := funext hn
    apply hfg
    rw [hwords, occupationWordCount_permutation]
  obtain ⟨i, hi⟩ := hne
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact he.inner_eq_zero hi

/-- Choosing one tensor word for each distinct occupation gives a genuine orthonormal family. -/
theorem normalizedOccupationWordVector_orthonormal {ι : Type*} {n d : ℕ}
    (e : Fin d → Lp ℂ 2 μ) (he : Orthonormal ℂ e) (f : ι → Fin n → Fin d)
    (hf : Function.Injective (fun i => occupationWordCount (f i))) :
    Orthonormal ℂ (fun i => normalizedOccupationWordVector μ e (f i)) := by
  constructor
  · intro i
    exact normalizedOccupationWordVector_norm μ e he (f i)
  · intro i j hij
    change inner ℂ
      ((Real.sqrt ((n.factorial : ℝ) / ∏ k, (occupationWordCount (f i) k).factorial) : ℂ) •
        (occupationWordVector μ e (f i) : ProductL2 μ (Fin n)))
      ((Real.sqrt ((n.factorial : ℝ) / ∏ k, (occupationWordCount (f j) k).factorial) : ℂ) •
        (occupationWordVector μ e (f j) : ProductL2 μ (Fin n))) = 0
    have hz : inner ℂ (occupationWordVector μ e (f i) : ProductL2 μ (Fin n))
        (occupationWordVector μ e (f j) : ProductL2 μ (Fin n)) = 0 :=
      occupationWordVector_inner_eq_zero μ e he (f i) (f j) (fun h => hij (hf h))
    rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), hz,
      mul_zero, mul_zero]

/-- Exact coherent-sector coefficient, before the final factorial simplification. -/
theorem normalizedOccupationWordVector_inner_exponentialSector {n d : ℕ}
    (e : Fin d → Lp ℂ 2 μ) (f : Fin n → Fin d) (u : Lp ℂ 2 μ) :
    inner ℂ (normalizedOccupationWordVector μ e f) (exponentialSector μ n u) =
      (Real.sqrt ((n.factorial : ℝ) / ∏ j, (occupationWordCount f j).factorial) : ℂ) *
        (factorialWeight n : ℂ) *
          ∏ j, (inner ℂ (e j) u) ^ occupationWordCount f j := by
  change inner ℂ
    ((Real.sqrt ((n.factorial : ℝ) / ∏ j, (occupationWordCount f j).factorial) : ℂ) •
      (occupationWordVector μ e f : ProductL2 μ (Fin n)))
    ((factorialWeight n : ℂ) • pureTensorL2 (ι := Fin n) μ u) = _
  have hp : inner ℂ (occupationWordVector μ e f : ProductL2 μ (Fin n))
      (pureTensorL2 (ι := Fin n) μ u) =
      ∏ j, (inner ℂ (e j) u) ^ occupationWordCount f j :=
    occupationWordVector_inner_pure_counts μ e f u
  rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), Complex.conj_ofReal, hp]
  ring

/-- The normalized coherent coefficient has exactly the product-factorial denominator. -/
theorem normalizedOccupationWordVector_coherent_coefficient {n d : ℕ}
    (e : Fin d → Lp ℂ 2 μ) (f : Fin n → Fin d) (u : Lp ℂ 2 μ) :
    inner ℂ (normalizedOccupationWordVector μ e f) (exponentialSector μ n u) =
      ((Real.sqrt (∏ j, (occupationWordCount f j).factorial : ℝ))⁻¹ : ℂ) *
        ∏ j, (inner ℂ (e j) u) ^ occupationWordCount f j := by
  rw [normalizedOccupationWordVector_inner_exponentialSector]
  have hn : Real.sqrt (n.factorial : ℝ) ≠ 0 := by positivity
  have hp : Real.sqrt (∏ j, (occupationWordCount f j).factorial : ℝ) ≠ 0 := by positivity
  have hc : Real.sqrt ((n.factorial : ℝ) / ∏ j, (occupationWordCount f j).factorial) *
      factorialWeight n = (Real.sqrt (∏ j, (occupationWordCount f j).factorial : ℝ))⁻¹ := by
    rw [Real.sqrt_div (Nat.cast_nonneg _), factorialWeight]
    simp only [Nat.cast_prod]
    field_simp [hn, hp]
  rw [← Complex.ofReal_mul, hc, Complex.ofReal_inv]

end LiebLiniger.FixedPeriod.Quantum
