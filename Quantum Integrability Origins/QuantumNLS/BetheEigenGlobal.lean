import QuantumNLS.BetheEigen
import QuantumNLS.ContactFormTheorem
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
Global assembly for the literal unnormalized Bethe vector.
Frozen BE1 a51f488d and the accepted contact chain are imported read-only.
Source: periodic_basis.tex:248–286, eigenvector and independence components.
-/
noncomputable section
open scoped BigOperators Topology Interval InnerProductSpace ComplexConjugate
open Filter MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionIdentification QuantumNLS.CollisionTrace
  QuantumNLS.BetheWavefunctions QuantumNLS.BetheWeakGradient
  QuantumNLS.BetheExtension QuantumNLS.BetheH1 QuantumNLS.BetheCollision
  QuantumNLS.BetheEigen

namespace QuantumNLS.BetheEigenGlobal

theorem integrable_conjugate {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

theorem cube_integrable_conj_mul {N : ℕ} {L : ℝ} {f φ : (Fin N → ℝ) → ℂ}
    (hf : Integrable f (cubeMeasure N L)) (hφ : Continuous φ) :
    Integrable (fun x => conj (f x) * φ x) (cubeMeasure N L) := by
  have hi : IntegrableOn (fun x => conj (f x)) (Icc (fun _ => 0) (fun _ => L)) volume :=
    integrable_conjugate hf
  exact hi.mul_continuousOn hφ.continuousOn isCompact_Icc

/-- A measurable, bounded bulk second partial, zero on every collision wall.
Strict chambers are disjoint, so at most one summand is nonzero. -/
def bulkSecond {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N)
    (x : Fin N → ℝ) : ℂ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin N), if StrictAnti (x ∘ σ) then
    ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) (σ.symm i) (x ∘ σ) else 0

theorem ordered_permutation_unique {N : ℕ} {x : Fin N → ℝ}
    (hx : Function.Injective x) {σ τ : Equiv.Perm (Fin N)}
    (hσ : Antitone (x ∘ σ)) (hτ : Antitone (x ∘ τ)) : σ = τ := by
  apply Equiv.ext
  intro i
  exact hx (congrFun (Tuple.unique_antitone hσ hτ) i)

theorem bulkSecond_chamber {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : StrictAnti (x ∘ σ)) :
    bulkSecond L c n i x =
      ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) (σ.symm i) (x ∘ σ) := by
  classical
  have hx : Function.Injective x := by
    intro a b h
    apply σ.symm.injective
    apply hσ.injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
  unfold bulkSecond
  rw [Finset.sum_eq_single σ]
  · simp only [hσ, ↓reduceIte]
  · intro τ _ hτ
    split_ifs with ht
    · exact (hτ (ordered_permutation_unique hx ht.antitone hσ.antitone)).elim
    · rfl
  · simp

theorem measurable_bulkSecond {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    Measurable (bulkSecond L c n i) := by
  classical
  apply Finset.measurable_sum
  intro σ _
  have hm : MeasurableSet {x : Fin N → ℝ | StrictAnti (x ∘ σ)} := by
    simp only [StrictAnti, Set.ofPred_forall]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      MeasurableSet.iInter fun (_ : a < b) =>
        measurableSet_lt (by fun_prop) (by fun_prop)
  exact ((continuous_ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) (σ.symm i)).comp
    (by fun_prop : Continuous (fun x : Fin N → ℝ => x ∘ σ))).measurable.ite hm measurable_const

/-- A finite bound for the actual second chamber partials. -/
def secondBound {N : ℕ} (c : ℝ) (q : Fin N → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin N), ‖coefficient c (q ∘ σ)‖ * ∑ j, q j ^ 2

theorem secondBound_nonneg {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    0 ≤ secondBound c q := by unfold secondBound; positivity

theorem norm_ansatzSecondPartial_le {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (i : Fin N) :
    ‖ansatzSecondPartial c q i x‖ ≤ secondBound c q := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro σ _
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, planeWave_norm, mul_one]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => sq_nonneg (q j)) (Finset.mem_univ (σ i)))
    (norm_nonneg _)

theorem norm_bulkSecond_le {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N) (x : Fin N → ℝ) :
    ‖bulkSecond L c n i x‖ ≤
      Fintype.card (Equiv.Perm (Fin N)) * secondBound c (BetheSmooth.sourceRoots L n c) := by
  classical
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), secondBound c (BetheSmooth.sourceRoots L n c) := by
      apply Finset.sum_le_sum
      intro σ _
      split_ifs
      · exact norm_ansatzSecondPartial_le _ _ _ _
      · simpa using secondBound_nonneg c (BetheSmooth.sourceRoots L n c)
    _ = _ := by simp

theorem bulkSecond_integrable {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    Integrable (bulkSecond L c n i) (cubeMeasure N L) := by
  exact (integrable_const _).mono' (measurable_bulkSecond L c n i).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_bulkSecond_le L c n i))

/-- The free eigen-equation on the cube, away from its null collision walls. -/
theorem bulkSecond_sum {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (x : Fin N → ℝ)
    (hx : Function.Injective x) :
    (∑ i, bulkSecond L c n i x) = -(energy L c n : ℂ) * symmetricExtension L c n x := by
  let σ := Tuple.sort (α := ℝᵒᵈ) x
  have hs : StrictAnti (x ∘ σ) :=
    (decreasing_antitone x).strictAnti_of_injective (hx.comp σ.injective)
  simp_rw [bulkSecond_chamber L c n _ x σ hs]
  rw [Equiv.sum_comp σ.symm (fun j => ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) j (x ∘ σ)),
    coordinateAnsatz_laplacian]
  unfold energy
  push_cast
  rfl

/-- Coordinate covariance of the bulk partial off the collision walls. -/
theorem bulkSecond_permute {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) (hx : Function.Injective x) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    bulkSecond L c n i (x ∘ τ) = bulkSecond L c n (τ i) x := by
  let σ := Tuple.sort (α := ℝᵒᵈ) x
  have hs : StrictAnti (x ∘ σ) :=
    (decreasing_antitone x).strictAnti_of_injective (hx.comp σ.injective)
  let ρ := σ.trans τ.symm
  have he : (x ∘ τ) ∘ ρ = x ∘ σ := by ext j; simp [ρ]
  rw [bulkSecond_chamber L c n i (x ∘ τ) ρ (he ▸ hs),
    bulkSecond_chamber L c n (τ i) x σ hs, he]
  rfl

/-- Inserting a coordinate different from each spectator preserves injectivity. -/
theorem injective_insert {N : ℕ} (i : Fin (N+1)) {y : Fin N → ℝ}
    (hy : Function.Injective y) {t : ℝ} (ht : ∀ j, t ≠ y j) :
    Function.Injective (i.insertNth t y) := by
  intro a b hab
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · exact hb.symm
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hb
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hab
      exact (ht j hab).elim
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    by_cases hb : b = i
    · subst b
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hab
      exact (ht j hab.symm).elim
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hb
      simp only [Fin.insertNth_apply_succAbove] at hab
      exact congrArg i.succAbove (hy hab)

/-- Identifies the second partial on each sorted insertion interval. -/
theorem bulkSecond_insertion_chart {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (y : Fin N → ℝ) (hy : Antitone y) (hinj : Function.Injective y)
    (r : Fin (N+1)) {t : ℝ} (ht : Fin.lastCases 0 y r < t ∧ t < Fin.cases L y r)
    (hne : ∀ j, t ≠ y j) :
    bulkSecond L c n 0 (Fin.cons t y) =
      ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) r (r.insertNth t y) := by
  have hstrict : StrictAnti (r.insertNth t y) :=
    (antitone_insert_of_bounds L y hy r t ⟨ht.1.le, ht.2.le⟩).strictAnti_of_injective
      (injective_insert r hinj hne)
  have he := insert_eq_cons_permute r t y
  have hh : StrictAnti (Fin.cons t y ∘ insertionPermutation r) := he ▸ hstrict
  rw [bulkSecond_chamber L c n 0 (Fin.cons t y) (insertionPermutation r) hh]
  rw [← he]
  have hr : (insertionPermutation r).symm 0 = r := by
    apply (insertionPermutation r).injective
    simp [insertionPermutation_self]
  rw [hr]

/-- The sorted chamber bulk integrals assemble into the actual coordinate
integral. Endpoint and spectator collisions form finite null sets here. -/
theorem sorted_bulk_integral {N : ℕ} {L : ℝ} (hL : 0 ≤ L) (c : ℝ)
    (n : Fin (N+1) → ℤ) (y : Fin N → ℝ) (hy : Antitone y)
    (hinj : Function.Injective y) (hbox : ∀ j, y j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : Continuous φ) :
    (∫ t in (0 : ℝ)..L, conj (bulkSecond L c n 0 (Fin.cons t y)) * φ t) =
      ∑ r : Fin (N+1), ∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r),
        conj (ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) r
          (r.insertNth t y)) * φ t := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t => conj (bulkSecond L c n 0 (Fin.cons t y)) * φ t) volume a b := by
    have hm : Measurable (fun t : ℝ => conj (bulkSecond L c n 0 (Fin.cons t y))) :=
      Complex.continuous_conj.measurable.comp ((measurable_bulkSecond L c n 0).comp (by fun_prop))
    have hg : IntervalIntegrable (fun t => conj (bulkSecond L c n 0 (Fin.cons t y))) volume a b := by
      constructor <;> exact (integrable_const _).mono' hm.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun t => by
          simpa only [Complex.norm_conj] using norm_bulkSecond_le L c n 0 (Fin.cons t y))
    exact hg.mul_continuousOn hφ.continuousOn
  rw [integral_insertion_partition L y _ hi]
  apply Finset.sum_congr rfl
  intro r _
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t ∂volume, ∀ j, t ≠ y j := Filter.eventually_all.2 fun j => volume.ae_ne (y j)
  filter_upwards [hne, volume.ae_ne (Fin.cases L y r)] with t ht hu hmem
  rw [uIoc_of_le (insertion_interval_order hL y hy hbox r)] at hmem
  rw [bulkSecond_insertion_chart L c n y hy hinj r
    ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩ ht]

/-- Arbitrary spectator order and moving slot, with the bulk now a single
measurable coordinate integral instead of a sum of chamber integrals. -/
theorem slice_bulk_integral {N : ℕ} {L : ℝ} (hL : 0 ≤ L) (c : ℝ)
    (n : Fin (N+1) → ℤ) (i : Fin (N+1)) (y : Fin N → ℝ)
    (hinj : Function.Injective y) (hbox : ∀ j, y j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : Continuous φ) :
    (∫ t in (0 : ℝ)..L, conj (bulkSecond L c n i (i.insertNth t y)) * φ t) =
      ∑ r : Fin (N+1),
        ∫ t in (Fin.lastCases 0 (decreasing y) r)..(Fin.cases L (decreasing y) r),
          conj (ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) r
            (r.insertNth t (decreasing y))) * φ t := by
  rw [← sorted_bulk_integral hL c n (decreasing y) (decreasing_antitone y)
    (hinj.comp (Tuple.sort (α := ℝᵒᵈ) y).injective) (fun j => hbox _) φ hφ]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t ∂volume, ∀ j, t ≠ y j := Filter.eventually_all.2 fun j => volume.ae_ne (y j)
  filter_upwards [hne] with t ht _
  have hx : Function.Injective (Fin.cons t y) := by
    simpa only [Fin.insertNth_zero'] using injective_insert 0 hinj ht
  rw [insert_eq_cons_permute, bulkSecond_permute L c n _ hx, insertionPermutation_self]
  rw [show Fin.cons t (decreasing y) = Fin.cons t y ∘ headPermutation (Tuple.sort (α := ℝᵒᵈ) y)
      from cons_permute t y (Tuple.sort (α := ℝᵒᵈ) y), bulkSecond_permute L c n _ hx]
  rfl

/-- Entire coordinate second IBP in terms of the bounded bulk representative.
No boundary, gluing, or weak-identity premise is supplied. -/
theorem slice_second_identity {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+2) → ℤ} (hn : Antitone n) (i : Fin (N+2))
    (y : Fin (N+1) → ℝ) (hinj : Function.Injective y) (hbox : ∀ j, y j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, conj (gradient L c n i (i.insertNth t y)) * deriv φ t) =
      -(c : ℂ) * ∑ j : Fin (N+1),
        conj (symmetricExtension L c n (i.insertNth (y j) y)) * φ (y j) -
      ∫ t in (0 : ℝ)..L, conj (bulkSecond L c n i (i.insertNth t y)) * φ t := by
  rw [slice_second_integrationByParts hL hc hn i y hbox φ hφ hper,
    slice_bulk_integral hL.le c n i y hinj hbox φ hφ.continuous]

/-- The one-particle IBP has no collision terms. Periodic normal matching
cancels its only two endpoints. -/
theorem slice_second_identity_one {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin 1 → ℤ} (hn : Antitone n) (i : Fin 1) (y : Fin 0 → ℝ)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, conj (gradient L c n i (i.insertNth t y)) * deriv φ t) =
      -(c : ℂ) * ∑ j : Fin 0,
        conj (symmetricExtension L c n (i.insertNth (y j) y)) * φ (y j) -
      ∫ t in (0 : ℝ)..L, conj (bulkSecond L c n i (i.insertNth t y)) * φ t := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hreg (x : Fin 1 → ℝ) : regular 0 x := by
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  have hanti (x : Fin 1 → ℝ) : Antitone x := by
    intro a b _
    exact le_of_eq (congrArg x (Subsingleton.elim _ _))
  have hstrict (x : Fin 1 → ℝ) : StrictAnti x := by
    intro a b hab
    exact ((ne_of_lt hab) (Subsingleton.elim _ _)).elim
  have hg (t : ℝ) : gradient L c n 0 ((0 : Fin 1).insertNth t y) =
      ansatzPartial c (BetheSmooth.sourceRoots L n c) 0 ((0 : Fin 1).insertNth t y) := by
    rw [gradient_eq_ansatzPartial L c n 0 _ (hreg _), decreasing_eq (hanti _)]
    congr 1
    exact Subsingleton.elim _ _
  have hb (t : ℝ) : bulkSecond L c n 0 ((0 : Fin 1).insertNth t y) =
      ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) 0 ((0 : Fin 1).insertNth t y) := by
    exact bulkSecond_chamber L c n 0 _ (Equiv.refl _) (hstrict _)
  simp_rw [hg, hb]
  simp only [Fin.sum_univ_zero, mul_zero, zero_sub]
  have hf := ansatzPartial_outer_faces hL hc hn y
  have he : (Fin.snoc y (0 : ℝ) : Fin 1 → ℝ) = (Fin.cons 0 y : Fin 1 → ℝ) := by
    ext j
    fin_cases j
    simp [Fin.snoc_zero]
  simp only [Fin.last_zero, he] at hf
  have hip := insertion_second_integrationByParts c (BetheSmooth.sourceRoots L n c)
    (0 : Fin 1) y 0 L φ hφ
  simp only [Fin.insertNth_zero'] at hip ⊢
  rw [hf, hper, sub_self, zero_sub] at hip
  exact hip

/-- All positive particle numbers, including the empty spectator tuple. -/
theorem slice_second_identity_all {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1))
    (y : Fin N → ℝ) (hinj : Function.Injective y) (hbox : ∀ j, y j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, conj (gradient L c n i (i.insertNth t y)) * deriv φ t) =
      -(c : ℂ) * ∑ j : Fin N,
        conj (symmetricExtension L c n (i.insertNth (y j) y)) * φ (y j) -
      ∫ t in (0 : ℝ)..L, conj (bulkSecond L c n i (i.insertNth t y)) * φ t := by
  cases N with
  | zero => exact slice_second_identity_one hL hc hn i y φ hφ hper
  | succ N => exact slice_second_identity hL hc hn i y hinj hbox φ hφ hper

/-- Global Fubini assembly for one moving coordinate. Its contact terms use
one copy of each spectator coordinate, with ordinary Lebesgue measure. -/
theorem cube_second_identity {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1))
    (φ : (Fin (N+1) → ℝ) → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (Function.update x i L) = φ (Function.update x i 0)) :
    (∫ x, conj (gradient L c n i x) * testPartial φ i x ∂cubeMeasure (N+1) L) =
      -(c : ℂ) * ∑ j : Fin (N),
        (∫ y, conj (symmetricExtension L c n (i.insertNth (y j) y)) *
          φ (i.insertNth (y j) y) ∂cubeMeasure (N) L) -
      ∫ x, conj (bulkSecond L c n i x) * φ x ∂cubeMeasure (N+1) L := by
  classical
  have hA : Integrable (fun x => conj (gradient L c n i x) * testPartial φ i x)
      (cubeMeasure (N+1) L) := by
    exact cube_integrable_conj_mul ((gradient_memLp L c n i).integrable (by norm_num))
      (continuous_testPartial hφ i)
  have hB : Integrable (fun x => conj (bulkSecond L c n i x) * φ x)
      (cubeMeasure (N+1) L) :=
    cube_integrable_conj_mul (bulkSecond_integrable L c n i) hφ.continuous
  have hC (j : Fin (N)) : Integrable
      (fun y : Fin (N) → ℝ => conj (symmetricExtension L c n (i.insertNth (y j) y)) *
        φ (i.insertNth (y j) y)) (cubeMeasure (N) L) := by
    exact ((Complex.continuous_conj.comp ((continuous_symmetricExtension L c n).comp
      (by fun_prop))).mul (hφ.continuous.comp (by fun_prop))).integrableOn_Icc
  rw [cube_integral_slice hL.le i _ hA, cube_integral_slice hL.le i _ hB]
  have hBi : Integrable (fun y => ∫ t in (0 : ℝ)..L,
      conj (bulkSecond L c n i (i.insertNth t y)) * φ (i.insertNth t y))
      (cubeMeasure (N) L) := by
    let μ : Measure ℝ := volume.restrict (Icc 0 L)
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i).symm
    have he : Integrable (fun p : ℝ × (Fin (N) → ℝ) =>
        conj (bulkSecond L c n i (i.insertNth p.1 p.2)) * φ (i.insertNth p.1 p.2))
        (μ.prod (Measure.pi fun _ : Fin (N) => μ)) := by
      have hb : Integrable (fun x => conj (bulkSecond L c n i x) * φ x)
          (Measure.pi fun _ : Fin (N+1) => μ) := by
        simpa only [cubeMeasure_eq_pi, μ] using hB
      exact hp.integrable_comp_of_integrable hb
    have hh := he.integral_prod_right
    simpa only [μ, ← cubeMeasure_eq_pi, intervalIntegral.integral_of_le hL.le,
      ← integral_Icc_eq_integral_Ioc] using hh
  rw [← integral_finsetSum _ (fun j _ => hC j), ← integral_const_mul,
    ← integral_sub (((integrable_finsetSum _ (fun j _ => hC j))).const_mul _) hBi]
  apply integral_congr_ae
  filter_upwards [cube_ae_injective (N := N) L, ae_restrict_mem measurableSet_Icc] with y hy hbox
  let x : Fin (N+1) → ℝ := i.insertNth 0 y
  have htest : ContDiff ℝ 1 (fun t => φ (Function.update x i t)) :=
    hφ.comp (contDiff_update 1 x i)
  have he := slice_second_identity_all hL hc hn i y hy (fun j => ⟨hbox.1 j, hbox.2 j⟩)
    (fun t => φ (Function.update x i t)) htest (hper x)
  simp_rw [testPartial_update hφ] at he
  simpa only [x, Fin.update_insertNth] using he

/-- Summing the bulk integrals uses the actual free chamber equation and
retains the source energy with its original sign and scale. -/
theorem cube_bulk_sum {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (φ : (Fin N → ℝ) → ℂ) (hφ : Continuous φ) :
    (∑ i, ∫ x, conj (bulkSecond L c n i x) * φ x ∂cubeMeasure N L) =
      -(energy L c n : ℂ) * ∫ x, conj (symmetricExtension L c n x) * φ x ∂cubeMeasure N L := by
  rw [← integral_finsetSum _ (fun i _ =>
    cube_integrable_conj_mul (bulkSecond_integrable L c n i) hφ),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [cube_ae_injective (N := N) L] with x hx
  rw [← Finset.sum_mul, ← map_sum, bulkSecond_sum L c n x hx, map_mul, map_neg,
    Complex.conj_ofReal, mul_assoc]

/-- Reindex all spectators as the common collision coordinate and the
remaining coordinates. This is a literal coordinate equivalence. -/
def spectatorIndex {N : ℕ} (i : Fin (N+1)) (j : Fin N) :
    Fin N ≃ DCoord i (i.succAbove j) where
  toFun k := if h : k = j then .inl () else
    .inr ⟨i.succAbove k, Fin.succAbove_ne i k,
      fun he => h ((Fin.strictMono_succAbove i).injective he)⟩
  invFun z := match z with
    | .inl _ => j
    | .inr k => (finSuccAboveEquiv i).symm ⟨k.val, k.property.1⟩
  left_inv k := by
    by_cases h : k = j
    · simp only [h, dite_true]
    · simp only [h, dite_false]
      exact (finSuccAboveEquiv i).symm_apply_apply k
  right_inv z := by
    rcases z with u | k
    · cases u; simp only [dite_true]
    · have hk : i.succAbove ((finSuccAboveEquiv i).symm ⟨k.val, k.property.1⟩) = k.val :=
        congrArg Subtype.val ((finSuccAboveEquiv i).apply_symm_apply ⟨k.val, k.property.1⟩)
      have hn : (finSuccAboveEquiv i).symm ⟨k.val, k.property.1⟩ ≠ j := by
        intro he
        rw [he] at hk
        exact k.property.2 hk.symm
      simp only [hn, dite_false]
      exact congrArg Sum.inr (Subtype.ext hk)

theorem diagonal_spectatorIndex {N : ℕ} {L : ℝ} [Fact (0 < L)]
    (i : Fin (N+1)) (j : Fin N) (y : Fin N → AddCircle L) :
    diagonal i (i.succAbove j) (fun z => y ((spectatorIndex i j).symm z)) =
      i.insertNth (y j) y := by
  classical
  apply funext
  apply (Fin.forall_iff_succAbove (P := fun l =>
    diagonal i (i.succAbove j) (fun z => y ((spectatorIndex i j).symm z)) l =
      (i.insertNth (y j) y : Fin (N+1) → AddCircle L) l) i).2
  constructor
  · simp [CollisionIdentification.diagonal, QuantumNLS.CollisionTrace.diagPoint, spectatorIndex]
  · intro k
    rw [Fin.insertNth_apply_succAbove]
    by_cases h : k = j
    · subst k
      simp [CollisionIdentification.diagonal, QuantumNLS.CollisionTrace.diagPoint, spectatorIndex]
    · have hne : i.succAbove k ≠ i.succAbove j := fun he =>
        h ((Fin.strictMono_succAbove i).injective he)
      have he : (spectatorIndex i j) k = .inr ⟨i.succAbove k, Fin.succAbove_ne i k, hne⟩ := by
        change (if hk : k = j then Sum.inl () else Sum.inr _) = _
        simp only [h, dite_false]
      have hv := (spectatorIndex i j).symm_apply_apply k
      rw [he] at hv
      simpa only [CollisionIdentification.diagonal, QuantumNLS.CollisionTrace.diagPoint,
        Fin.succAbove_ne, dite_false, hne] using congrArg y hv

/-- Exact change of coordinates from a spectator integral to dy_ij. All
circle coordinates have mass L; this introduces no geometric area factor. -/
theorem collision_integral_spectators {N : ℕ} {L : ℝ} [Fact (0 < L)]
    (i : Fin (N+1)) (j : Fin N) (F : (Fin (N+1) → AddCircle L) → ℂ)
    (hF : Continuous F) :
    (∫ y : Fin N → ℝ, F (fun k => (((i.insertNth (y j) y : Fin (N+1) → ℝ) k) : AddCircle L)) ∂cubeMeasure N L) =
      ∫ p, F (QuantumNLS.CollisionTrace.diagPoint i (i.succAbove j) p.1 p.2)
        ∂dyij (L := L) i (i.succAbove j) := by
  let e := spectatorIndex i j
  have hp := measurePreserving_piCongrLeft
    (fun _ : DCoord i (i.succAbove j) => (volume : Measure (AddCircle L))) e
  have hu := measurePreserving_unitSumPositions L (QuantumNLS.CollisionTrace.Rest (N+1) i (i.succAbove j))
  calc
    _ = ∫ y, F (i.insertNth (y j) y) ∂torusPiMeasure L N := by
      rw [torusPiMeasure, ← volume_pi]
      rw [torus_integral_cube L (fun y : Fin N → AddCircle L => F (i.insertNth (y j) y))
        ((hF.comp (by fun_prop)).aestronglyMeasurable)]
      apply integral_congr_ae
      filter_upwards with y
      congr 1
      ext k
      by_cases hk : k = i
      · subst k; simp
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hk
        simp
    _ = ∫ z, F (diagonal i (i.succAbove j) z)
        ∂Measure.pi (fun _ : DCoord i (i.succAbove j) => (volume : Measure (AddCircle L))) := by
      rw [← hp.integral_comp' (fun z => F (diagonal i (i.succAbove j) z))]
      apply integral_congr_ae
      filter_upwards with y
      rw [show (MeasurableEquiv.piCongrLeft (fun _ : DCoord i (i.succAbove j) => AddCircle L) e) y =
        (fun z => y (e.symm z)) from (by
          ext z
          simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply])]
      rw [diagonal_spectatorIndex]
    _ = _ := hu.integral_comp' (fun p => F
      (QuantumNLS.CollisionTrace.diagPoint i (i.succAbove j) p.1 p.2))

/-- Each spectator term in the cube IBP is the already constructed contact
trace pairing, on precisely the accepted dy_ij measure. -/
theorem cube_contact_eq_Gp {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ)
    (i : Fin (N+1)) (j : Fin N) :
    (∫ y, conj (symmetricExtension L c n (i.insertNth (y j) y)) *
      φ (i.insertNth (y j) y) ∂cubeMeasure N L) =
      ContactFormTheorem.Gp (waveH1 (L := L) hc hn) (smoothH1 hφ) i (i.succAbove j) := by
  have hij : i ≠ i.succAbove j := (Fin.succAbove_ne i j).symm
  rw [ContactFormTheorem.Gp, dite_eq_left hij, ← productTrace_inner,
    inner_eq_integral_of_ae _ _ (productTrace_waveH1_ae hc hn i (i.succAbove j) hij)
      (productTrace_smooth i (i.succAbove j) hij hφ)]
  rw [← collision_integral_spectators i j
    (fun x => conj (torusExtension L c n x) * liftK (L := L) φ x)
    ((Complex.continuous_conj.comp (continuous_torusExtension hc hn)).mul
      (continuous_liftK hφ.smooth.continuous hφ.periodic))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hx : ∀ k, (i.insertNth (y j) y : Fin (N+1) → ℝ) k ∈ Icc (0 : ℝ) L := by
    intro k
    by_cases hk : k = i
    · subst k
      simpa only [Fin.insertNth_apply_same, mem_Icc] using And.intro (hy.1 j) (hy.2 j)
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hk
      simpa only [Fin.insertNth_apply_succAbove, mem_Icc] using And.intro (hy.1 k) (hy.2 k)
  rw [torusExtension_closed_cube hc hn _ hx, liftK_coe hφ.periodic]

/-- Counting both moving coordinates of each collision yields exactly 2c. -/
theorem cube_contact_sum {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (∑ i : Fin (N+1), ∑ j : Fin N,
      ∫ y, conj (symmetricExtension L c n (i.insertNth (y j) y)) *
        φ (i.insertNth (y j) y) ∂cubeMeasure N L) =
      2 * ContactForm.contactSum (waveH1 (L := L) hc hn) (smoothH1 hφ) := by
  simp_rw [cube_contact_eq_Gp hc hn hφ]
  rw [ContactFormTheorem.contactSum_eq_Gp, ContactFormTheorem.sum_pair_double
    _ (ContactFormTheorem.Gp_diag _ _) (ContactFormTheorem.Gp_swap _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succAbove (fun b => ContactFormTheorem.Gp
    (waveH1 (L := L) hc hn) (smoothH1 hφ) i b) i, ContactFormTheorem.Gp_diag, zero_add]


/-- The torus kinetic integral pulls back to the same cube gradient used by
BE1, with the literal classical partial of the smooth periodic test. -/
theorem kinetic_integral_cube {N : ℕ} {L : ℝ} [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (i : Fin N) :
    (∫ x, conj (torusGradient L c n i x) * liftK (L := L) (pderiv i φ) x
      ∂torusPiMeasure L N) =
      ∫ x, conj (gradient L c n i x) * testPartial φ i x ∂cubeMeasure N L := by
  have hm : Measurable (fun x => conj (torusGradient L c n i x) *
      liftK (L := L) (pderiv i φ) x) :=
    (Complex.continuous_conj.measurable.comp (measurable_torusGradient L c n i)).mul
      (continuous_liftK (continuous_pderiv hφ i) (latticePeriodic_pderiv hφ i)).measurable
  rw [show torusPiMeasure L N = (volume : Measure (Fin N → AddCircle L)) from volume_pi.symm,
    torus_integral_cube L _ hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [representatives_coe_ae N L] with x hx
  rw [liftK_coe (latticePeriodic_pderiv hφ i), torusGradient, hx,
    testPartial_eq_pderiv (hφ.smooth.of_le (by simp))]

/-- The bulk pairing on the physical torus is the ordinary cube pairing. -/
theorem inner_waveH1_cube {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ⟪(waveH1 (L := L) hc hn).val, (smoothH1 hφ).val⟫_ℂ =
      ∫ x, conj (symmetricExtension L c n x) * φ x ∂cubeMeasure (N+1) L := by
  rw [inner_waveH1_smooth hc hn hφ,
    show torusPiMeasure L (N+1) = (volume : Measure (Fin (N+1) → AddCircle L)) from volume_pi.symm,
    torus_integral_cube L (fun x => conj (torusExtension L c n x) * liftK (L := L) φ x)
      (((Complex.continuous_conj.comp (continuous_torusExtension hc hn)).mul
      (continuous_liftK hφ.smooth.continuous hφ.periodic)).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [torusExtension_closed_cube hc hn x (fun i => ⟨hx.1 i, hx.2 i⟩), liftK_coe hφ.periodic]

/-- Smooth-test weak identity, obtained from coordinate Fubini, the free
bulk equation, exact dy_ij reindexing, and double counting the pairs. -/
theorem smooth_eigen_left {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ContactForm.q c (waveH1 (L := L) hc hn) (smoothH1 hφ) =
      (energy L c n : ℂ) * ⟪(waveH1 (L := L) hc hn).val, (smoothH1 hφ).val⟫_ℂ := by
  have hL : 0 < L := Fact.out
  have htest : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have he : (∑ i : Fin (N+1),
      ∫ x, conj (gradient L c n i x) * testPartial φ i x ∂cubeMeasure (N+1) L) =
      ∑ i : Fin (N+1), (-(c : ℂ) * ∑ j : Fin (N),
        (∫ y, conj (symmetricExtension L c n (i.insertNth (y j) y)) *
          φ (i.insertNth (y j) y) ∂cubeMeasure (N) L) -
        ∫ x, conj (bulkSecond L c n i x) * φ x ∂cubeMeasure (N+1) L) := by
    exact Finset.sum_congr rfl fun i _ => cube_second_identity hL hc hn i φ htest (test_faces hφ.periodic i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, cube_contact_sum hc hn hφ,
    cube_bulk_sum L c n φ hφ.smooth.continuous] at he
  rw [q_waveH1 hc hn (smoothH1 hφ) (fun i => gradientCLM i (smoothH1 hφ))
    (fun i => ContactDistributionFull.gradientCLM_hasWeakPartial i _), inner_waveH1_cube hc hn hφ]
  have hk (i : Fin (N+1)) :
      ⟪weakGradient (L := L) c n i, gradientCLM i (smoothH1 hφ)⟫_ℂ =
        ∫ x, conj (gradient L c n i x) * testPartial φ i x ∂cubeMeasure (N+1) L := by
    rw [inner_eq_integral_of_ae _ _ (coe_weakGradient c n i) (gradientCLM_smooth_ae hφ i)]
    exact kinetic_integral_cube c n hφ i
  simp_rw [hk]
  push_cast
  linear_combination he

/-- Hermitian symmetry of the actual contact form. -/
theorem conjugate_q {N : ℕ} {L : ℝ} [Fact (0 < L)] (c : ℝ)
    (x y : PhysH1 L N) : conj (ContactForm.q c x y) = ContactForm.q c y x := by
  simp only [ContactForm.q, ContactForm.kinSum, ContactForm.contactSum,
    map_add, map_mul, map_sum, inner_conj_symm, Complex.conj_ofReal]


/-- The smooth-test identity in the form's conjugate-linear first slot. -/
theorem smooth_eigen {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ContactForm.q c (smoothH1 hφ) (waveH1 (L := L) hc hn) =
      (energy L c n : ℂ) * ⟪(smoothH1 hφ).val, (waveH1 (L := L) hc hn).val⟫_ℂ := by
  have he := congrArg conj (smooth_eigen_left hc hn hφ)
  simpa only [conjugate_q, map_mul, Complex.conj_ofReal, inner_conj_symm] using he

/-- Density extends the proved smooth-test identity to every H¹ symmetric
test, using the accepted trigonometric approximation theorem. -/
theorem weak_eigen {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (φ : ContactOperator.VSym L (N+1)) :
    ContactForm.q c φ.1 (waveH1 (L := L) hc hn) =
      (energy L c n : ℂ) * ⟪φ.1.val, (waveH1 (L := L) hc hn).val⟫_ℂ := by
  have hall := ContactDistribution.variational_of_trig hc.le (waveH1Sym (L := L) hc hn)
    ((energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym (L := L) hc hn))
  have hh : ∀ (S : Finset (Fin (N+1) → ℤ)) (a : (Fin (N+1) → ℤ) → ℂ)
      (hs : trigElem (L := L) S a ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L (N+1)))),
      ContactForm.q c (trigElem (L := L) S a) (waveH1 (L := L) hc hn) =
        ⟪(ContactOperator.valSym (⟨trigElem (L := L) S a, hs⟩ : ContactOperator.VSym L (N+1)) :
          ContactOperator.SymL2 L (N+1)),
          (energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym (L := L) hc hn)⟫_ℂ := by
    intro S a hs
    have hm := ContactDistribution.trigElem_mem_testClass S a hs
    obtain ⟨f, hf, hsym, he⟩ := hm
    have hv : trigElem (L := L) S a = smoothH1 hf := by
      apply PhysH1.val_injective
      exact he.trans (smoothH1_val hf).symm
    change ContactForm.q c (trigElem (L := L) S a) (waveH1 (L := L) hc hn) =
      ⟪(trigElem (L := L) S a).val, (energy L c n : ℂ) • (waveH1 (L := L) hc hn).val⟫_ℂ
    rw [hv, inner_smul_right]
    exact smooth_eigen hc hn hf
  have he := hall hh φ
  change ContactForm.q c φ.1 (waveH1 (L := L) hc hn) =
    ⟪φ.1.val, (energy L c n : ℂ) • (waveH1 (L := L) hc hn).val⟫_ℂ at he
  rwa [inner_smul_right] at he

/-- Unconditional operator-domain membership and the literal source energy
equation for the unnormalized Bethe vector. -/
theorem Hop_eigen {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ∃ h : (ContactOperator.valSym (waveH1Sym (L := L) hc hn) : ContactOperator.SymL2 L (N+1)) ∈
        (ContactOperator.Hop c hc.le).domain,
      ContactOperator.Hop c hc.le ⟨ContactOperator.valSym (waveH1Sym hc hn), h⟩ =
        (energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym hc hn) :=
  Hop_eigen_of_weak_identity hc hn (weak_eigen hc hn)


/-- A plane wave is a multiplicative character of the additive coordinate
space. The coefficients retain the source's positive i convention. -/
def planeCharacter {N : ℕ} (q : Fin N → ℝ) : Multiplicative (Fin N → ℝ) →* ℂ where
  toFun x := planeWave q x.toAdd
  map_one' := by simp [planeWave]
  map_mul' x y := by
    simp [planeWave, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, Complex.exp_add]

/-- Differentiating at zero recovers every component of a real frequency. -/
theorem planeCharacter_injective {N : ℕ} : Function.Injective (planeCharacter (N := N)) := by
  intro q r he
  funext i
  have hf : (fun t => planeWave q (Function.update (fun _ : Fin N => 0) i t)) =
      (fun t => planeWave r (Function.update (fun _ : Fin N => 0) i t)) := by
    funext t
    exact congrArg (fun f : Multiplicative (Fin N → ℝ) →* ℂ =>
      f (Multiplicative.ofAdd (Function.update (fun _ : Fin N => 0) i t))) he
  have hq := planeWave_update_hasDerivAt q (fun _ => 0) i 0
  have hr := planeWave_update_hasDerivAt r (fun _ => 0) i 0
  rw [hf] at hq
  have hd := hq.unique hr
  simp only [Function.update_eq_self, planeWave, mul_zero, Finset.sum_const_zero,
    Complex.ofReal_zero, Complex.exp_zero, mul_one] at hd
  exact Complex.ofReal_injective (mul_left_cancel₀ Complex.I_ne_zero hd)

/-- Distinct finite frequency families are independent as characters. -/
theorem planeCharacters_independent {I : Type*} {N : ℕ} (q : I → Fin N → ℝ)
    (hq : Function.Injective q) :
    LinearIndependent ℂ (fun a => (planeCharacter (q a) : Multiplicative (Fin N → ℝ) → ℂ)) :=
  (linearIndependent_monoidHom (Multiplicative (Fin N → ℝ)) ℂ).comp _
    (planeCharacter_injective.comp hq)

/-- Character independence and the nonzero source coefficients imply that
the entire chamber ansatz cannot be the zero function. -/
theorem coordinateAnsatz_not_zero {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    (hq : Function.Injective q) : coordinateAnsatz c q ≠ 0 := by
  classical
  intro hzero
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin N) => q ∘ σ) := by
    intro σ τ h
    apply Equiv.ext
    intro i
    exact hq (congrFun h i)
  have hi := planeCharacters_independent (fun σ : Equiv.Perm (Fin N) => q ∘ σ) hinj
  have hz : (∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) •
      (planeCharacter (q ∘ σ) : Multiplicative (Fin N → ℝ) → ℂ)) = 0 := by
    ext x
    simpa [coordinateAnsatz, planeCharacter] using congrFun hzero x.toAdd
  exact coefficient_ne_zero c q (by
    simpa only [Function.comp_def, Equiv.refl_apply] using
      (Fintype.linearIndependent_iff.1 hi (fun σ => coefficient c (q ∘ σ)) hz (Equiv.refl _)))

/-- Finite plane-wave sums are real analytic on the whole coordinate space. -/
theorem analyticAt_coordinateAnsatz {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) :
    AnalyticAt ℝ (coordinateAnsatz c q) x := by
  unfold coordinateAnsatz
  apply Finset.analyticAt_fun_sum
  intro σ _
  let a : (Fin N → ℝ) →L[ℝ] ℝ := ∑ i, q (σ i) • ContinuousLinearMap.proj i
  have ha : AnalyticAt ℝ (fun y : Fin N → ℝ => ∑ i, q (σ i) * y i) x := by
    convert a.analyticAt x using 1
    ext y
    simp [a]
  have hc : AnalyticAt ℝ (fun y : Fin N → ℝ =>
      Complex.I * ((∑ i, q (σ i) * y i : ℝ) : ℂ)) x :=
    analyticAt_const.mul ((Complex.ofRealCLM.analyticAt _).comp ha)
  have hexp : AnalyticAt ℝ Complex.exp (Complex.I * ((∑ i, q (σ i) * x i : ℝ) : ℂ)) :=
    (analyticAt_cexp).restrictScalars
  have he : AnalyticAt ℝ (fun y : Fin N → ℝ =>
      Complex.exp (Complex.I * ((∑ i, q (σ i) * y i : ℝ) : ℂ))) x := hexp.comp (f := fun y : Fin N → ℝ =>
        Complex.I * ((∑ i, q (σ i) * y i : ℝ) : ℂ)) hc
  exact analyticAt_const.mul he

/-- The source's strict coordinate chamber is open, including the
zero-dimensional case. -/
theorem isOpen_chamber (N : ℕ) (L : ℝ) : IsOpen (chamber N L) := by
  have ho : IsOpen {x : Fin N → ℝ | StrictAnti x} := by
    simp only [StrictAnti, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      isOpen_iInter_of_finite fun (_ : a < b) => isOpen_lt (by fun_prop) (by fun_prop)
  have hb : IsOpen {x : Fin N → ℝ | ∀ i, 0 < x i ∧ x i < L} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)
  exact ho.inter hb

/-- An explicit interior point of every source chamber. -/
theorem chamber_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) : (chamber N L).Nonempty := by
  let d : ℝ := L / (N+1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hde : d * (N+1) = L := by dsimp [d]; field_simp
  refine ⟨fun i => d * ((N : ℝ) - i.val), ?_, ?_⟩
  · intro i j hij
    have hh : (i.val : ℝ) < j.val := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_left (by linarith) hd
  · intro i
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ i.val := by positivity
    constructor
    · exact mul_pos hd (sub_pos.2 hi)
    · calc
        d * ((N : ℝ) - i.val) ≤ d * N := mul_le_mul_of_nonneg_left (by linarith) hd.le
        _ < d * (N+1) := mul_lt_mul_of_pos_left (by linarith) hd
        _ = L := hde

/-- A nonzero entire ansatz cannot vanish throughout the source chamber.
This uses the real-analytic identity theorem and character independence. -/
theorem coordinateAnsatz_chamber_nonzero {N : ℕ} {L : ℝ} (hL : 0 < L)
    (c : ℝ) (q : Fin N → ℝ) (hq : Function.Injective q) :
    ∃ x ∈ chamber N L, coordinateAnsatz c q x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := chamber_nonempty hL N
  have he : coordinateAnsatz c q =ᶠ[𝓝 x] 0 := by
    filter_upwards [(isOpen_chamber N L).mem_nhds hx] with y hy
    exact h y hy
  have ha : AnalyticOnNhd ℝ (coordinateAnsatz c q) Set.univ :=
    fun x _ => analyticAt_coordinateAnsatz c q x
  exact coordinateAnsatz_not_zero c q hq
    (ha.eq_of_eventuallyEq (analyticOnNhd_const) he)

/-- Literal nonvanishing of the actual, unnormalized Bethe L² vector. -/
theorem wave_ne_zero {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (waveH1 (L := L) hc hn).val ≠ 0 := by
  intro hz
  have hae : torusExtension L c n =ᵐ[torusPiMeasure L (N+1)] 0 := by
    have he := coe_waveH1_val (L := L) hc hn
    rw [hz] at he
    exact he.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have heq : torusExtension L c n = 0 :=
    Measure.eq_of_ae_eq hae (continuous_torusExtension hc hn) continuous_const
  obtain ⟨x, hx, hne⟩ := coordinateAnsatz_chamber_nonzero (Fact.out : 0 < L) c
    (BetheSmooth.sourceRoots L n c) (BetheSmooth.sourceRoots_strictAnti (Fact.out : 0 < L) hc hn).injective
  apply hne
  change wavefunction L c n x = 0
  rw [← periodicExtension_chamber L c n hx]
  exact congrFun heq (fun i => (x i : AddCircle L))

/-- The same literal nonvanishing on the source's symmetric Hilbert space. -/
theorem valSym_ne_zero {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ContactOperator.valSym (waveH1Sym (L := L) hc hn) ≠ 0 := by
  intro h
  exact wave_ne_zero hc hn (congrArg (fun x : ContactOperator.SymL2 L (N+1) => (x : L2TN L (N+1))) h)


/-- The literal logarithmic Bethe equations recover the integer label from
the roots. No energy nondegeneracy assumption is involved. -/
theorem sourceRoots_label_injective {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    Function.Injective (fun n : Fin N → ℤ => BetheSmooth.sourceRoots L n c) := by
  intro n m h
  have he := congrArg (BetheAdmission.logMap L c) h
  rw [BetheSmooth.sourceRoots_solves hL hc n, BetheSmooth.sourceRoots_solves hL hc m] at he
  funext i
  have hi := congrFun he i
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hnum := mul_left_cancel₀ hπ hi
  unfold BetheSmooth.sourceNumbers at hnum
  have hn : (n i : ℝ) = m i := by linarith
  exact_mod_cast hn

/-- Different antitone labels have disjoint permutation frequency sets.
This is the source's frequency separation input for independence. -/
theorem frequency_sets_disjoint {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n m : Fin N → ℤ} (hn : Antitone n) (hm : Antitone m) (hne : n ≠ m) :
    Disjoint (Set.range (fun σ : Equiv.Perm (Fin N) => BetheSmooth.sourceRoots L n c ∘ σ))
      (Set.range (fun σ : Equiv.Perm (Fin N) => BetheSmooth.sourceRoots L m c ∘ σ)) := by
  rw [Set.disjoint_left]
  rintro x ⟨σ, rfl⟩ ⟨τ, he⟩
  apply hne
  apply sourceRoots_label_injective hL hc
  have hd := congrArg decreasing he
  rw [decreasing_permute, decreasing_permute,
    decreasing_eq (BetheSmooth.sourceRoots_strictAnti hL hc hn).antitone,
    decreasing_eq (BetheSmooth.sourceRoots_strictAnti hL hc hm).antitone] at hd
  exact hd.symm


/-- All frequency assignments from a finite family of distinct antitone
labels are distinct, even when the corresponding energies coincide. -/
theorem joint_frequencies_injective {I : Type*} {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) (n : I → Fin N → ℤ)
    (hn : ∀ a, Antitone (n a)) (hinj : Function.Injective n) :
    Function.Injective (fun p : I × Equiv.Perm (Fin N) => BetheSmooth.sourceRoots L (n p.1) c ∘ p.2) := by
  rintro ⟨a, σ⟩ ⟨b, τ⟩ he
  have hab : a = b := by
    by_contra hab
    have hd := frequency_sets_disjoint hL hc (hn a) (hn b) (fun h => hab (hinj h))
    exact Set.disjoint_left.1 hd ⟨σ, rfl⟩ ⟨τ, he.symm⟩
  subst b
  exact Prod.ext rfl (permuted_roots_injective hL hc (hn a) he)

/-- Independence on the open source chamber. Analytic continuation reduces
the chamber restriction to finite character independence on the full
additive coordinate space. -/
theorem chamber_ansatz_independent {I : Type*} [Fintype I] {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) (n : I → Fin N → ℤ)
    (hn : ∀ a, Antitone (n a)) (hinj : Function.Injective n) (g : I → ℂ)
    (hzero : ∀ x ∈ chamber N L, ∑ a, g a * wavefunction L c (n a) x = 0) :
    ∀ a, g a = 0 := by
  classical
  let F : (Fin N → ℝ) → ℂ := fun x => ∑ a, g a * wavefunction L c (n a) x
  have ha : AnalyticOnNhd ℝ F Set.univ := by
    intro x _
    exact Finset.analyticAt_fun_sum _ fun a _ =>
      analyticAt_const.mul (analyticAt_coordinateAnsatz c (BetheSmooth.sourceRoots L (n a) c) x)
  obtain ⟨x, hx⟩ := chamber_nonempty hL N
  have he : F =ᶠ[𝓝 x] 0 := by
    filter_upwards [(isOpen_chamber N L).mem_nhds hx] with y hy
    exact hzero y hy
  have hglobal : F = 0 := ha.eq_of_eventuallyEq analyticOnNhd_const he
  let Q : I × Equiv.Perm (Fin N) → Fin N → ℝ :=
    fun p => BetheSmooth.sourceRoots L (n p.1) c ∘ p.2
  have hi := planeCharacters_independent Q (joint_frequencies_injective hL hc n hn hinj)
  have hp (x : Fin N → ℝ) :
      (∑ p : I × Equiv.Perm (Fin N), (g p.1 * coefficient c (Q p)) * planeWave (Q p) x) = 0 := by
    rw [Fintype.sum_prod_type]
    simpa only [F, wavefunction, coordinateAnsatz, Finset.mul_sum, mul_assoc, Q, Pi.zero_apply] using congrFun hglobal x
  have hz : (∑ p : I × Equiv.Perm (Fin N), (g p.1 * coefficient c (Q p)) •
      (planeCharacter (Q p) : Multiplicative (Fin N → ℝ) → ℂ)) = 0 := by
    ext x
    simpa [planeCharacter] using hp x.toAdd
  intro a
  have hg := Fintype.linearIndependent_iff.1 hi (fun p => g p.1 * coefficient c (Q p)) hz (a, Equiv.refl _)
  exact (mul_eq_zero.1 hg).resolve_right (coefficient_ne_zero c _)

/-- A finite L² linear relation gives a literal zero relation on the chamber.
The passage from classes to functions uses continuity and positive measure
of nonempty open subsets of the ordinary product torus. -/
theorem finite_waves_independent {I : Type*} [Fintype I] {N : ℕ}
    {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    (n : I → Fin (N+1) → ℤ) (hn : ∀ a, Antitone (n a)) (hinj : Function.Injective n) :
    LinearIndependent ℂ (fun a => (waveH1 (L := L) hc (hn a)).val) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro g hg
  let F : (Fin (N+1) → AddCircle L) → ℂ := fun x =>
    ∑ a, g a * torusExtension L c (n a) x
  have hF : Continuous F := continuous_finsetSum _ fun a _ =>
    continuous_const.mul (continuous_torusExtension hc (hn a))
  have hvals (a : I) :
      ((g a • (waveH1 (L := L) hc (hn a)).val : L2TN L (N+1)) : (Fin (N+1) → AddCircle L) → ℂ)
        =ᵐ[torusPiMeasure L (N+1)] (fun x => g a * torusExtension L c (n a) x) := by
    filter_upwards [Lp.coeFn_smul (g a) (waveH1 (L := L) hc (hn a)).val,
      coe_waveH1_val (L := L) hc (hn a)] with x hx hv
    rw [hx, Pi.smul_apply, smul_eq_mul, hv]
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun a => g a • (waveH1 (L := L) hc (hn a)).val)
  rw [hg] at hsum
  have hae : F =ᵐ[torusPiMeasure L (N+1)] 0 := by
    filter_upwards [hsum, Filter.eventually_all.2 hvals, Lp.coeFn_zero ℂ 2 (torusPiMeasure L (N+1))]
      with x hx hv hz
    change (∑ a, g a * torusExtension L c (n a) x) = 0
    calc
      _ = ∑ a, ((g a • (waveH1 (L := L) hc (hn a)).val : L2TN L (N+1)) :
          (Fin (N+1) → AddCircle L) → ℂ) x := Finset.sum_congr rfl fun a _ => (hv a).symm
      _ = (0 : L2TN L (N+1)) x := by
        simpa only [Finset.sum_apply] using hx.symm
      _ = 0 := hz
  have heq : F = 0 := Measure.eq_of_ae_eq hae hF continuous_const
  apply chamber_ansatz_independent (Fact.out : 0 < L) hc n hn hinj g
  intro x hx
  have he := congrFun heq (fun i => (x i : AddCircle L))
  dsimp only [F] at he
  have hp (a : I) : torusExtension L c (n a) (fun i => (x i : AddCircle L)) =
      wavefunction L c (n a) x := periodicExtension_chamber L c (n a) hx
  simpa only [hp, Pi.zero_apply] using he

/-- Literal linear independence of the unnormalized Bethe vectors for c>0,
indexed by all antitone integer labels. No normalization, orthogonality,
energy separation, or completeness premise is used. -/
theorem waves_independent {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c) :
    LinearIndependent ℂ (fun n : {n : Fin (N+1) → ℤ // Antitone n} =>
      (waveH1 (L := L) hc n.property).val) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact finite_waves_independent hc (fun a : s => a.val.val) (fun a => a.val.property)
    (Subtype.val_injective.comp Subtype.val_injective)



/-- The BE1 remainder, for every positive particle number: the global H¹
weak identity, actual operator-domain/eigenvalue equation, and literal
nonvanishing of the same unnormalized symmetric Bethe vector. -/
theorem bethe_eigenvector {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (∀ φ : ContactOperator.VSym L (N+1),
      ContactForm.q c φ.1 (waveH1 (L := L) hc hn) =
        (energy L c n : ℂ) * ⟪φ.1.val, (waveH1 (L := L) hc hn).val⟫_ℂ) ∧
    (∃ h : (ContactOperator.valSym (waveH1Sym (L := L) hc hn) : ContactOperator.SymL2 L (N+1)) ∈
        (ContactOperator.Hop c hc.le).domain,
      ContactOperator.Hop c hc.le ⟨ContactOperator.valSym (waveH1Sym hc hn), h⟩ =
        (energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym hc hn)) ∧
    ContactOperator.valSym (waveH1Sym (L := L) hc hn) ≠ 0 :=
  ⟨weak_eigen hc hn, Hop_eigen hc hn, valSym_ne_zero hc hn⟩

end QuantumNLS.BetheEigenGlobal

#print axioms QuantumNLS.BetheEigenGlobal.integrable_conjugate
#print axioms QuantumNLS.BetheEigenGlobal.cube_integrable_conj_mul
#print axioms QuantumNLS.BetheEigenGlobal.bulkSecond
#print axioms QuantumNLS.BetheEigenGlobal.ordered_permutation_unique
#print axioms QuantumNLS.BetheEigenGlobal.bulkSecond_chamber
#print axioms QuantumNLS.BetheEigenGlobal.measurable_bulkSecond
#print axioms QuantumNLS.BetheEigenGlobal.secondBound
#print axioms QuantumNLS.BetheEigenGlobal.secondBound_nonneg
#print axioms QuantumNLS.BetheEigenGlobal.norm_ansatzSecondPartial_le
#print axioms QuantumNLS.BetheEigenGlobal.norm_bulkSecond_le
#print axioms QuantumNLS.BetheEigenGlobal.bulkSecond_integrable
#print axioms QuantumNLS.BetheEigenGlobal.bulkSecond_sum
#print axioms QuantumNLS.BetheEigenGlobal.bulkSecond_permute
#print axioms QuantumNLS.BetheEigenGlobal.injective_insert
#print axioms QuantumNLS.BetheEigenGlobal.bulkSecond_insertion_chart
#print axioms QuantumNLS.BetheEigenGlobal.sorted_bulk_integral
#print axioms QuantumNLS.BetheEigenGlobal.slice_bulk_integral
#print axioms QuantumNLS.BetheEigenGlobal.slice_second_identity
#print axioms QuantumNLS.BetheEigenGlobal.slice_second_identity_one
#print axioms QuantumNLS.BetheEigenGlobal.slice_second_identity_all
#print axioms QuantumNLS.BetheEigenGlobal.cube_second_identity
#print axioms QuantumNLS.BetheEigenGlobal.cube_bulk_sum
#print axioms QuantumNLS.BetheEigenGlobal.spectatorIndex
#print axioms QuantumNLS.BetheEigenGlobal.diagonal_spectatorIndex
#print axioms QuantumNLS.BetheEigenGlobal.collision_integral_spectators
#print axioms QuantumNLS.BetheEigenGlobal.cube_contact_eq_Gp
#print axioms QuantumNLS.BetheEigenGlobal.cube_contact_sum
#print axioms QuantumNLS.BetheEigenGlobal.kinetic_integral_cube
#print axioms QuantumNLS.BetheEigenGlobal.inner_waveH1_cube
#print axioms QuantumNLS.BetheEigenGlobal.smooth_eigen_left
#print axioms QuantumNLS.BetheEigenGlobal.conjugate_q
#print axioms QuantumNLS.BetheEigenGlobal.smooth_eigen
#print axioms QuantumNLS.BetheEigenGlobal.weak_eigen
#print axioms QuantumNLS.BetheEigenGlobal.Hop_eigen
#print axioms QuantumNLS.BetheEigenGlobal.planeCharacter
#print axioms QuantumNLS.BetheEigenGlobal.planeCharacter_injective
#print axioms QuantumNLS.BetheEigenGlobal.planeCharacters_independent
#print axioms QuantumNLS.BetheEigenGlobal.coordinateAnsatz_not_zero
#print axioms QuantumNLS.BetheEigenGlobal.analyticAt_coordinateAnsatz
#print axioms QuantumNLS.BetheEigenGlobal.isOpen_chamber
#print axioms QuantumNLS.BetheEigenGlobal.chamber_nonempty
#print axioms QuantumNLS.BetheEigenGlobal.coordinateAnsatz_chamber_nonzero
#print axioms QuantumNLS.BetheEigenGlobal.wave_ne_zero
#print axioms QuantumNLS.BetheEigenGlobal.valSym_ne_zero
#print axioms QuantumNLS.BetheEigenGlobal.sourceRoots_label_injective
#print axioms QuantumNLS.BetheEigenGlobal.frequency_sets_disjoint
#print axioms QuantumNLS.BetheEigenGlobal.joint_frequencies_injective
#print axioms QuantumNLS.BetheEigenGlobal.chamber_ansatz_independent
#print axioms QuantumNLS.BetheEigenGlobal.finite_waves_independent
#print axioms QuantumNLS.BetheEigenGlobal.waves_independent
#print axioms QuantumNLS.BetheEigenGlobal.bethe_eigenvector
