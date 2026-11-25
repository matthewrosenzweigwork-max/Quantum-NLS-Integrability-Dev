import LiebLiniger.FixedPeriod.Quantum.WickGuardedDerivativePairing
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! SOURCE ONLY: actual count-j matching kernels and their identification with
the same independent source derivative contraction, including the unavailable
branch. This bounded assembly depends on exact qualified derivative, weighted
data and tensor pairings. No Wick operator product is assumed or claimed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem q2024_sector_inner_smul_right (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ x (a • y) = a * inner ℂ x y := by
  change inner ℂ (x : ProductL2 μ (Fin n)) (a • (y : ProductL2 μ (Fin n))) = _
  exact inner_smul_right (𝕜 := ℂ) _ _ _

/-- Every matching preserves EXACT source input/output degrees minus the same
contraction count. Thus j≤min(p,q) and the total sector shift stays q-p. -/
theorem sourceWickMatchingTerms_degrees (p q : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) (t : SourceWickMatchingTerm μ)
    (ht : t ∈ sourceWickMatchingTerms μ p gs q hs) :
    t.inputDegree + t.contractions = p ∧ t.outputDegree + t.contractions = q := by
  induction p generalizing q hs t with
  | zero =>
    simp only [sourceWickMatchingTerms, List.mem_singleton] at ht
    subst t
    exact ⟨rfl, by simp⟩
  | succ p ih =>
    cases q with
    | zero =>
      simp only [sourceWickMatchingTerms, List.mem_map] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      have hh := ih 0 (Fin.tail gs) hs a ha
      dsimp only [sourceMatchingKeep]
      omega
    | succ q =>
      simp only [sourceWickMatchingTerms, List.mem_append] at ht
      rcases ht with ht | ht
      · simp only [List.mem_map] at ht
        obtain ⟨a, ha, rfl⟩ := ht
        have hh := ih (q + 1) (Fin.tail gs) hs a ha
        dsimp only [sourceMatchingKeep]
        omega
      · simp only [List.mem_flatten, List.mem_ofFn] at ht
        obtain ⟨ts, ⟨i, rfl⟩, ht⟩ := ht
        simp only [List.mem_map] at ht
        obtain ⟨a, ha, rfl⟩ := ht
        have hh := ih q (Fin.tail gs) (i.removeNth hs) a ha
        dsimp only [sourceMatchingContract]
        omega

/-- The original matching list filtered by its literal contraction count.
There is no quotient by identical field values or equal resulting kernels. -/
def sourceWickMatchingCountTerms (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) : List (SourceWickMatchingTerm μ) :=
  (sourceWickMatchingTerms μ p gs q hs).filter (fun t => decide (t.contractions = j))

/-- Actual source kernel of one count-j matching. Both casts are earned only
from the independent recursive degree invariant, preserving all zero sectors. -/
def sourceWickMatchingTermKernel (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ)
    (t : {t // t ∈ sourceWickMatchingCountTerms μ p q j gs hs}) :
    SymmetricSector μ (p + 0 - j) →L[ℂ] SymmetricSector μ (0 + q - j) := by
  have hm := (List.mem_filter.mp t.property).1
  have hj : t.val.contractions = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp t.property).2
  have hd := sourceWickMatchingTerms_degrees μ p q gs hs t.val hm
  have hin : p + 0 - j = t.val.inputDegree := by omega
  have hout : t.val.outputDegree = 0 + q - j := by omega
  exact t.val.coefficient •
    ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L
      InnerProductSpace.rankOne ℂ
        (symmetricTensorContinuousMultilinear μ t.val.outputDegree t.val.outputFields)
        (symmetricTensorContinuousMultilinear μ t.val.inputDegree t.val.inputFields) ∘L
      (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap)

/-- Genuine bounded source kernel: a finite sum of the independent count-j
physical rank-one kernels. Its degrees are exactly those of the source
contraction of pure annihilation degree p with pure creation degree q. -/
def sourceWickMatchingKernel (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) :
    SymmetricSector μ (p + 0 - j) →L[ℂ] SymmetricSector μ (0 + q - j) :=
  ((sourceWickMatchingCountTerms μ p q j gs hs).attach.map
    (sourceWickMatchingTermKernel μ p q j gs hs)).sum

private theorem matching_cast_polarized {a b c d : ℕ}
    (hin : a = b) (hout : c = d)
    (T : SymmetricSector μ b →L[ℂ] SymmetricSector μ c) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ
      ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap) v u =
      wickKernelPolarized μ T v u := by
  subst b
  subst d
  rfl

/-- Every actual transported matching kernel has the independently specified
physical scalar pure pairing, with the original conjugate-first orientation. -/
theorem sourceWickMatchingTermKernel_polarized (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (t : {t // t ∈ sourceWickMatchingCountTerms μ p q j gs hs}) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceWickMatchingTermKernel μ p q j gs hs t) v u =
      t.val.coefficient *
        ((∏ i : Fin t.val.outputDegree, inner ℂ v (t.val.outputFields i)) *
          ∏ k : Fin t.val.inputDegree, inner ℂ (t.val.inputFields k) u) := by
  unfold sourceWickMatchingTermKernel
  rw [show ∀ (c : ℂ) {a b : ℕ} (T : SymmetricSector μ a →L[ℂ] SymmetricSector μ b),
      wickKernelPolarized μ (c • T) v u = c * wickKernelPolarized μ T v u from
    fun c {a b} T => by
      simp only [wickKernelPolarized, ContinuousLinearMap.smul_apply,
        q2024_sector_inner_smul_right μ b]]
  rw [matching_cast_polarized]
  simp only [wickKernelPolarized, InnerProductSpace.rankOne_apply, inner_smul_right,
    inner_pure_symmetricMixedTensor, inner_symmetricMixedTensor_pure]
  ring

private theorem matching_polarized_list_sum {p q : ℕ}
    (ts : List (SymmetricSector μ p →L[ℂ] SymmetricSector μ q)) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ ts.sum v u =
      (ts.map (fun T => wickKernelPolarized μ T v u)).sum := by
  induction ts with
  | nil => simp only [List.sum_nil, List.map_nil, wickKernelPolarized,
      ContinuousLinearMap.zero_apply, inner_zero_right]
  | cons T ts ih =>
    simp only [List.sum_cons, List.map_cons, wickKernelPolarized,
      ContinuousLinearMap.add_apply, inner_add_right] at ih ⊢
    rw [ih]

/-- Concrete pure pairing of the SAME fixed-degree matching kernel as a list
sum with every physical factor and every recursive multiplicity retained. -/
theorem sourceWickMatchingKernel_polarized (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceWickMatchingKernel μ p q j gs hs) v u =
      ((sourceWickMatchingCountTerms μ p q j gs hs).map (fun t =>
        t.coefficient *
          ((∏ i : Fin t.outputDegree, inner ℂ v (t.outputFields i)) *
            ∏ k : Fin t.inputDegree, inner ℂ (t.inputFields k) u))).sum := by
  unfold sourceWickMatchingKernel
  rw [matching_polarized_list_sum, List.map_map]
  simp only [Function.comp_def]
  have hm := List.map_congr_left (l := (sourceWickMatchingCountTerms μ p q j gs hs).attach)
    (fun t _ => sourceWickMatchingTermKernel_polarized μ p q j gs hs t v u)
  rw [hm]
  simpa only [Function.comp_apply] using
    congrArg (fun xs : List ℂ => xs.sum)
      (List.attach_map_val (l := sourceWickMatchingCountTerms μ p q j gs hs)
        (f := fun t => t.coefficient *
          ((∏ i : Fin t.outputDegree, inner ℂ v (t.outputFields i)) *
            ∏ k : Fin t.inputDegree, inner ℂ (t.inputFields k) u)))

/-- Unavailable matching orders contain no terms at all, as earned from the
actual recursive degree invariant; the bounded kernel is consequently zero. -/
theorem sourceWickMatchingCountTerms_unavailable (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (hj : ¬ j ≤ min p q) :
    sourceWickMatchingCountTerms μ p q j gs hs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro t ht
  have hm := (List.mem_filter.mp ht).1
  have hc : t.contractions = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp ht).2
  have hd := sourceWickMatchingTerms_degrees μ p q gs hs t hm
  omega

@[simp] theorem sourceWickMatchingKernel_unavailable (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (hj : ¬ j ≤ min p q) :
    sourceWickMatchingKernel μ p q j gs hs = 0 := by
  unfold sourceWickMatchingKernel
  have hnil : (sourceWickMatchingCountTerms μ p q j gs hs).attach = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have hm : t.val ∈ ([] : List (SourceWickMatchingTerm μ)) :=
      (congrArg (fun ls : List (SourceWickMatchingTerm μ) => t.val ∈ ls)
        (sourceWickMatchingCountTerms_unavailable μ p q j gs hs hj)).mp t.property
    exact List.not_mem_nil hm
  rw [hnil, List.map_nil, List.sum_nil]

/-- SAME actual independently defined source contraction is j! times the
bounded matching kernel. The weighted pairing identity is proved by the
separate B-side provider; complete-sector pure totality earns operator equality.
No derivative-kernel equality or Wick product hypothesis is supplied. -/
theorem sourceDerivativeContractionKernel_mixed_annihilation_creation
    (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) :
    sourceDerivativeContractionKernel μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
          (symmetricTensorContinuousMultilinear μ p gs))
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
          (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) j =
      (j.factorial : ℂ) • sourceWickMatchingKernel μ p q j gs hs := by
  by_cases hj : j ≤ min p q
  · apply wickSymmetricSector_operator_eq_of_pure_pairings μ
    intro u v
    change wickKernelPolarized μ (sourceDerivativeContractionKernel μ _ _ j) v u = _
    rw [sourceDerivativeContractionKernel_mixed_annihilation_creation_pairing
      μ p q j gs hs hj v u,
      sourceWickOrderedPairing_eq_factorial_matchingPureSum μ p q j gs hs v u]
    rw [ContinuousLinearMap.smul_apply, q2024_sector_inner_smul_right μ (0 + q - j)]
    change (j.factorial : ℂ) * sourceWickMatchingPureSum μ p q j gs hs v u =
      (j.factorial : ℂ) * wickKernelPolarized μ (sourceWickMatchingKernel μ p q j gs hs) v u
    rw [sourceWickMatchingKernel_polarized]
    rfl
  · rw [sourceDerivativeContractionKernel_unavailable μ _ _ j hj,
      sourceWickMatchingKernel_unavailable μ p q j gs hs hj]
    apply ContinuousLinearMap.ext
    intro x
    change (0 : SymmetricSector μ (0 + q - j)) =
      (j.factorial : ℂ) • (0 : SymmetricSector μ (0 + q - j))
    exact (smul_zero (j.factorial : ℂ)).symm

end LiebLiniger.FixedPeriod.Quantum
end
