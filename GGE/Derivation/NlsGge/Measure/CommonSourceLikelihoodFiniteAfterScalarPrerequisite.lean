import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Measure.CommonLikelihoodScalarDoubling
import NlsGge.Measure.FiniteFourierLikelihoodMoments
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NlsGge.Measure

def commonSourceLikelihoodExponent
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h z : ℤ → ℂ) : ℝ :=
  ∑ n ∈ NlsGge.Pilot.symmetricModes N,
    (2 * fullWeightRate c.val n * (star (h n) * z n).re -
      fullWeightRate c.val n * ‖h n‖ ^ 2)

def commonSourceLikelihoodReal
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h z : ℤ → ℂ) : ℝ :=
  Real.exp (commonSourceLikelihoodExponent lower upper c N h z)

def commonSourceLikelihoodEnergy
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h : ℤ → ℂ) : ℝ :=
  ∑ n ∈ NlsGge.Pilot.symmetricModes N,
    2 * fullWeightRate c.val n * ‖h n‖ ^ 2

def commonSourceNestedShift
    (N M : ℕ) (h : ℤ → ℂ) : ℤ → ℂ :=
  fun n =>
    if n ∈ NlsGge.Pilot.symmetricModes M then
      if n ∈ NlsGge.Pilot.symmetricModes N then (2 : ℂ) * h n else h n
    else 0

private def commonModeProjection (N : ℕ) (z : ℤ → ℂ) : NlsGge.Pilot.FourierPlane N :=
  fun i => z (NlsGge.Pilot.modeIndex N i)

private lemma sum_symmetricModes_eq_sum_modeIndex (N : ℕ) (f : ℤ → ℝ) :
    (∑ n ∈ NlsGge.Pilot.symmetricModes N, f n) =
      ∑ i : Fin (2 * N + 1), f (NlsGge.Pilot.modeIndex N i) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => NlsGge.Pilot.modeIndex N i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_Icc.mpr (NlsGge.Pilot.modeIndex_bounds N i)
  · intro i hi j hj h
    exact NlsGge.Pilot.modeIndex_injective N h
  · intro n hn
    have hn' : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simpa [NlsGge.Pilot.symmetricModes] using hn
    obtain ⟨i, hmode⟩ := NlsGge.Pilot.modeIndex_covers N n
      (Finset.mem_Icc.mp hn').1 (Finset.mem_Icc.mp hn').2
    exact ⟨i, Finset.mem_univ _, hmode⟩
  · intro i hi
    rfl

private lemma commonLikelihood_eq_finite (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (h z : ℤ → ℂ) :
    commonSourceLikelihoodReal lower upper c N h z =
      fullWeightFourierLikelihoodReal c.val N
        (commonModeProjection N h) (commonModeProjection N z) := by
  unfold commonSourceLikelihoodReal commonSourceLikelihoodExponent
    fullWeightFourierLikelihoodReal commonModeProjection
  rw [sum_symmetricModes_eq_sum_modeIndex]

private lemma commonEnergy_eq_finite (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (h : ℤ → ℂ) :
    commonSourceLikelihoodEnergy lower upper c N h =
      fullWeightFourierLikelihoodEnergy c.val N (commonModeProjection N h) := by
  unfold commonSourceLikelihoodEnergy fullWeightFourierLikelihoodEnergy commonModeProjection
  rw [sum_symmetricModes_eq_sum_modeIndex]

theorem integrable_and_integral_commonSourceLikelihoodReal
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c.val j)
    (hupper : ∀ j : ℕ, c.val j ≤ upper)
    (N : ℕ) (h : ℤ → ℂ) :
    Integrable
      (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z)
      (fullWeightSequenceGaussian c.val) ∧
    (∫ z : ℤ → ℂ, commonSourceLikelihoodReal lower upper c N h z
      ∂fullWeightSequenceGaussian c.val) = 1 := by
  classical
  let P := commonModeProjection N
  let μ := fullWeightSequenceGaussian c.val
  let ν := fullWeightFourierGaussian N c.val
  let g : NlsGge.Pilot.FourierPlane N → ℝ :=
    fun y => fullWeightFourierLikelihoodReal c.val N (commonModeProjection N h) y
  obtain ⟨hfiniteI, hfiniteInt⟩ :=
    integrable_and_integral_fullWeightFourierLikelihoodReal
      lower upper c.val hlower hbound hupper N (commonModeProjection N h)
  have hmap : μ.map P = ν := by
    change (fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
          z (NlsGge.Pilot.modeIndex N i)) =
      fullWeightFourierGaussian N c.val
    exact fullWeightSequenceGaussian_map_modes N c.val
  have hPmeas : Measurable P := by
    change Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
      z (NlsGge.Pilot.modeIndex N i))
    fun_prop
  have hfiniteMap : Integrable g (μ.map P) := by
    rw [hmap]
    exact hfiniteI
  have hfiniteAEStrong : AEStronglyMeasurable g (μ.map P) :=
    hfiniteMap.aestronglyMeasurable
  have hcompI : Integrable (g ∘ P) μ :=
    (integrable_map_measure hfiniteAEStrong hPmeas.aemeasurable).mp hfiniteMap
  have hfun (z : ℤ → ℂ) :
      commonSourceLikelihoodReal lower upper c N h z = g (P z) := by
    dsimp [g, P]
    exact commonLikelihood_eq_finite lower upper c N h z
  have hcommonI : Integrable
      (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z) μ := by
    have hfunEq :
        (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z) = g ∘ P :=
      funext hfun
    rw [hfunEq]
    exact hcompI
  have hmapIntegral :
      (∫ y : NlsGge.Pilot.FourierPlane N, g y ∂μ.map P) =
        ∫ z : ℤ → ℂ, g (P z) ∂μ :=
    integral_map hPmeas.aemeasurable hfiniteAEStrong
  have hfiniteIntegralMap :
      (∫ y : NlsGge.Pilot.FourierPlane N, g y ∂μ.map P) = 1 := by
    rw [hmap]
    exact hfiniteInt
  refine ⟨hcommonI, ?_⟩
  calc
    (∫ z : ℤ → ℂ, commonSourceLikelihoodReal lower upper c N h z ∂μ) =
        ∫ z : ℤ → ℂ, g (P z) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hfun
    _ = ∫ y : NlsGge.Pilot.FourierPlane N, g y ∂μ.map P := hmapIntegral.symm
    _ = 1 := hfiniteIntegralMap

theorem integrable_and_integral_sq_commonSourceLikelihoodReal
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c.val j)
    (hupper : ∀ j : ℕ, c.val j ≤ upper)
    (N : ℕ) (h : ℤ → ℂ) :
    Integrable
      (fun z : ℤ → ℂ => (commonSourceLikelihoodReal lower upper c N h z) ^ 2)
      (fullWeightSequenceGaussian c.val) ∧
    (∫ z : ℤ → ℂ, (commonSourceLikelihoodReal lower upper c N h z) ^ 2
      ∂fullWeightSequenceGaussian c.val) =
      Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
  classical
  let P := commonModeProjection N
  let μ := fullWeightSequenceGaussian c.val
  let ν := fullWeightFourierGaussian N c.val
  let g : NlsGge.Pilot.FourierPlane N → ℝ :=
    fun y => (fullWeightFourierLikelihoodReal c.val N (commonModeProjection N h) y) ^ 2
  obtain ⟨hfiniteI, hfiniteInt⟩ :=
    integrable_and_integral_sq_fullWeightFourierLikelihoodReal
      lower upper c.val hlower hbound hupper N (commonModeProjection N h)
  have hmap : μ.map P = ν := by
    change (fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
          z (NlsGge.Pilot.modeIndex N i)) =
      fullWeightFourierGaussian N c.val
    exact fullWeightSequenceGaussian_map_modes N c.val
  have hPmeas : Measurable P := by
    change Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
      z (NlsGge.Pilot.modeIndex N i))
    fun_prop
  have hfiniteMap : Integrable g (μ.map P) := by
    rw [hmap]
    exact hfiniteI
  have hfiniteAEStrong : AEStronglyMeasurable g (μ.map P) :=
    hfiniteMap.aestronglyMeasurable
  have hcompI : Integrable (g ∘ P) μ :=
    (integrable_map_measure hfiniteAEStrong hPmeas.aemeasurable).mp hfiniteMap
  have hfun (z : ℤ → ℂ) :
      (commonSourceLikelihoodReal lower upper c N h z) ^ 2 = g (P z) := by
    dsimp [g, P]
    rw [commonLikelihood_eq_finite]
  have hcommonI : Integrable
      (fun z : ℤ → ℂ => (commonSourceLikelihoodReal lower upper c N h z) ^ 2) μ := by
    have hfunEq :
        (fun z : ℤ → ℂ => (commonSourceLikelihoodReal lower upper c N h z) ^ 2) = g ∘ P :=
      funext hfun
    rw [hfunEq]
    exact hcompI
  have hmapIntegral :
      (∫ y : NlsGge.Pilot.FourierPlane N, g y ∂μ.map P) =
        ∫ z : ℤ → ℂ, g (P z) ∂μ :=
    integral_map hPmeas.aemeasurable hfiniteAEStrong
  have hfiniteIntegralMap :
      (∫ y : NlsGge.Pilot.FourierPlane N, g y ∂μ.map P) =
        Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
    rw [hmap, commonEnergy_eq_finite lower upper c N h]
    exact hfiniteInt
  refine ⟨hcommonI, ?_⟩
  calc
    (∫ z : ℤ → ℂ, (commonSourceLikelihoodReal lower upper c N h z) ^ 2 ∂μ) =
        ∫ z : ℤ → ℂ, g (P z) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hfun
    _ = ∫ y : NlsGge.Pilot.FourierPlane N, g y ∂μ.map P := hmapIntegral.symm
    _ = Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := hfiniteIntegralMap

private lemma sum_extend_by_zero {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : A ⊆ B) (f : α → ℝ) :
    (∑ n ∈ A, f n) = ∑ n ∈ B, (if n ∈ A then f n else 0) := by
  classical
  calc
    (∑ n ∈ A, f n) = ∑ n ∈ A, (if n ∈ A then f n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [hn]
    _ = ∑ n ∈ B, (if n ∈ A then f n else 0) := by
      apply Finset.sum_subset hAB
      intro n hn hnA
      simp [hnA]

private lemma commonLikelihoodExponent_cross_identity
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N M : ℕ) (hNM : N ≤ M) (h z : ℤ → ℂ) :
    commonSourceLikelihoodExponent lower upper c N h z +
        commonSourceLikelihoodExponent lower upper c M h z =
      commonSourceLikelihoodEnergy lower upper c N h +
        commonSourceLikelihoodExponent lower upper c M
          (commonSourceNestedShift N M h) z := by
  classical
  let A := NlsGge.Pilot.symmetricModes N
  let B := NlsGge.Pilot.symmetricModes M
  let q : ℤ → ℝ := fullWeightRate c.val
  let f : ℤ → ℝ := fun n =>
    2 * q n * (star (h n) * z n).re - q n * ‖h n‖ ^ 2
  let e : ℤ → ℝ := fun n => 2 * q n * ‖h n‖ ^ 2
  let k : ℤ → ℝ := fun n =>
    2 * q n * (star (commonSourceNestedShift N M h n) * z n).re -
      q n * ‖commonSourceNestedShift N M h n‖ ^ 2
  have hAB : A ⊆ B := by
    intro n hn
    simp only [A, B, NlsGge.Pilot.symmetricModes, Finset.mem_Icc] at hn ⊢
    omega
  have hsumf : (∑ n ∈ A, f n) =
      ∑ n ∈ B, (if n ∈ A then f n else 0) := sum_extend_by_zero A B hAB f
  have hsume : (∑ n ∈ A, e n) =
      ∑ n ∈ B, (if n ∈ A then e n else 0) := sum_extend_by_zero A B hAB e
  change (∑ n ∈ A, f n) + ∑ n ∈ B, f n =
      (∑ n ∈ A, e n) + ∑ n ∈ B, k n
  rw [hsumf, hsume, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hA : n ∈ A
  · have hshift : commonSourceNestedShift N M h n = (2 : ℂ) * h n := by
      simp [commonSourceNestedShift, A, B, hA, hn]
    simp only [if_pos hA]
    dsimp [f, e, k, q]
    rw [hshift]
    exact commonLikelihoodScalarDoubling (fullWeightRate c.val n) (h n) (z n)
  · have hshift : commonSourceNestedShift N M h n = h n := by
      simp [commonSourceNestedShift, A, B, hA, hn]
    simp only [if_neg hA]
    dsimp [f, e, k, q]
    rw [hshift]

theorem commonSourceLikelihoodReal_mul_eq_nestedShift
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N M : ℕ) (hNM : N ≤ M) (h z : ℤ → ℂ) :
    commonSourceLikelihoodReal lower upper c N h z *
        commonSourceLikelihoodReal lower upper c M h z =
      Real.exp (commonSourceLikelihoodEnergy lower upper c N h) *
        commonSourceLikelihoodReal lower upper c M
          (commonSourceNestedShift N M h) z := by
  unfold commonSourceLikelihoodReal
  calc
    Real.exp (commonSourceLikelihoodExponent lower upper c N h z) *
        Real.exp (commonSourceLikelihoodExponent lower upper c M h z) =
      Real.exp (commonSourceLikelihoodExponent lower upper c N h z +
        commonSourceLikelihoodExponent lower upper c M h z) := by
          rw [← Real.exp_add]
    _ = Real.exp (commonSourceLikelihoodEnergy lower upper c N h +
        commonSourceLikelihoodExponent lower upper c M
          (commonSourceNestedShift N M h) z) :=
      congrArg Real.exp
        (commonLikelihoodExponent_cross_identity lower upper c N M hNM h z)
    _ = Real.exp (commonSourceLikelihoodEnergy lower upper c N h) *
        Real.exp (commonSourceLikelihoodExponent lower upper c M
          (commonSourceNestedShift N M h) z) := by
          rw [Real.exp_add]

theorem integrable_mul_and_integral_commonSourceLikelihoodReal
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c.val j)
    (hupper : ∀ j : ℕ, c.val j ≤ upper)
    (N M : ℕ) (hNM : N ≤ M) (h : ℤ → ℂ) :
    Integrable
      (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z *
        commonSourceLikelihoodReal lower upper c M h z)
      (fullWeightSequenceGaussian c.val) ∧
    (∫ z : ℤ → ℂ, commonSourceLikelihoodReal lower upper c N h z *
      commonSourceLikelihoodReal lower upper c M h z
      ∂fullWeightSequenceGaussian c.val) =
      Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
  obtain ⟨hfirstI, hfirstInt⟩ :=
    integrable_and_integral_commonSourceLikelihoodReal lower upper c
      hlower hbound hupper M (commonSourceNestedShift N M h)
  have hpoint (z : ℤ → ℂ) :=
    commonSourceLikelihoodReal_mul_eq_nestedShift lower upper c N M hNM h z
  have hprodI : Integrable
      (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z *
        commonSourceLikelihoodReal lower upper c M h z)
      (fullWeightSequenceGaussian c.val) := by
    have hconst := hfirstI.const_mul (Real.exp (commonSourceLikelihoodEnergy lower upper c N h))
    have hfun :
        (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z *
          commonSourceLikelihoodReal lower upper c M h z) =
        fun z => Real.exp (commonSourceLikelihoodEnergy lower upper c N h) *
          commonSourceLikelihoodReal lower upper c M
            (commonSourceNestedShift N M h) z := by
      funext z
      exact hpoint z
    rw [hfun]
    exact hconst
  refine ⟨hprodI, ?_⟩
  have hconstInt :
      (∫ z : ℤ → ℂ,
        Real.exp (commonSourceLikelihoodEnergy lower upper c N h) *
          commonSourceLikelihoodReal lower upper c M
            (commonSourceNestedShift N M h) z
        ∂fullWeightSequenceGaussian c.val) =
        Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
    rw [integral_const_mul, hfirstInt]
    ring
  calc
    (∫ z : ℤ → ℂ, commonSourceLikelihoodReal lower upper c N h z *
      commonSourceLikelihoodReal lower upper c M h z
      ∂fullWeightSequenceGaussian c.val) =
        ∫ z : ℤ → ℂ,
          Real.exp (commonSourceLikelihoodEnergy lower upper c N h) *
            commonSourceLikelihoodReal lower upper c M
              (commonSourceNestedShift N M h) z
          ∂fullWeightSequenceGaussian c.val := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := hconstInt

theorem integrable_sq_sub_and_integral_commonSourceLikelihoodReal
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c.val j)
    (hupper : ∀ j : ℕ, c.val j ≤ upper)
    (N M : ℕ) (hNM : N ≤ M) (h : ℤ → ℂ) :
    Integrable
      (fun z : ℤ → ℂ =>
        (commonSourceLikelihoodReal lower upper c M h z -
          commonSourceLikelihoodReal lower upper c N h z) ^ 2)
      (fullWeightSequenceGaussian c.val) ∧
    (∫ z : ℤ → ℂ,
      (commonSourceLikelihoodReal lower upper c M h z -
        commonSourceLikelihoodReal lower upper c N h z) ^ 2
      ∂fullWeightSequenceGaussian c.val) =
      Real.exp (commonSourceLikelihoodEnergy lower upper c M h) -
        Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
  obtain ⟨hMI, hM⟩ :=
    integrable_and_integral_sq_commonSourceLikelihoodReal lower upper c
      hlower hbound hupper M h
  obtain ⟨hNI, hN⟩ :=
    integrable_and_integral_sq_commonSourceLikelihoodReal lower upper c
      hlower hbound hupper N h
  obtain ⟨hcrossI, hcross⟩ :=
    integrable_mul_and_integral_commonSourceLikelihoodReal lower upper c
      hlower hbound hupper N M hNM h
  let μ := fullWeightSequenceGaussian c.val
  have hMI' : Integrable
      (fun z : ℤ → ℂ => (commonSourceLikelihoodReal lower upper c M h z) ^ 2) μ := by
    simpa [μ] using hMI
  have hNI' : Integrable
      (fun z : ℤ → ℂ => (commonSourceLikelihoodReal lower upper c N h z) ^ 2) μ := by
    simpa [μ] using hNI
  have hcrossRevI : Integrable
      (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c M h z *
        commonSourceLikelihoodReal lower upper c N h z) μ := by
    apply hcrossI.congr
    filter_upwards [] with z
    ring
  have hsubI : Integrable
      (fun z : ℤ → ℂ =>
        (commonSourceLikelihoodReal lower upper c M h z -
          commonSourceLikelihoodReal lower upper c N h z) ^ 2) μ := by
    have hsumI := hMI'.add hNI'
    have hscaledCrossI := hcrossRevI.const_mul (2 : ℝ)
    have hexpandedI : Integrable
        (fun z : ℤ → ℂ =>
          (commonSourceLikelihoodReal lower upper c M h z) ^ 2 +
            (commonSourceLikelihoodReal lower upper c N h z) ^ 2 -
              2 * (commonSourceLikelihoodReal lower upper c M h z *
                commonSourceLikelihoodReal lower upper c N h z)) μ := by
      exact hsumI.sub hscaledCrossI
    apply hexpandedI.congr
    filter_upwards [] with z
    ring
  refine ⟨hsubI, ?_⟩
  calc
    (∫ z : ℤ → ℂ,
      (commonSourceLikelihoodReal lower upper c M h z -
        commonSourceLikelihoodReal lower upper c N h z) ^ 2 ∂μ) =
      ∫ z : ℤ → ℂ,
        ((commonSourceLikelihoodReal lower upper c M h z) ^ 2 +
          (commonSourceLikelihoodReal lower upper c N h z) ^ 2 -
            2 * (commonSourceLikelihoodReal lower upper c M h z *
              commonSourceLikelihoodReal lower upper c N h z)) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          ring
    _ = (∫ z : ℤ → ℂ,
          (commonSourceLikelihoodReal lower upper c M h z) ^ 2 ∂μ) +
        (∫ z : ℤ → ℂ,
          (commonSourceLikelihoodReal lower upper c N h z) ^ 2 ∂μ) -
        2 * (∫ z : ℤ → ℂ,
          commonSourceLikelihoodReal lower upper c M h z *
            commonSourceLikelihoodReal lower upper c N h z ∂μ) := by
          have hsumI := hMI'.add hNI'
          have hscaledCrossI := hcrossRevI.const_mul (2 : ℝ)
          calc
            (∫ z : ℤ → ℂ,
              (commonSourceLikelihoodReal lower upper c M h z) ^ 2 +
                (commonSourceLikelihoodReal lower upper c N h z) ^ 2 -
                  2 * (commonSourceLikelihoodReal lower upper c M h z *
                    commonSourceLikelihoodReal lower upper c N h z) ∂μ) =
              (∫ z : ℤ → ℂ,
                (commonSourceLikelihoodReal lower upper c M h z) ^ 2 +
                  (commonSourceLikelihoodReal lower upper c N h z) ^ 2 ∂μ) -
                (∫ z : ℤ → ℂ,
                  2 * (commonSourceLikelihoodReal lower upper c M h z *
                    commonSourceLikelihoodReal lower upper c N h z) ∂μ) := by
                    exact integral_sub hsumI hscaledCrossI
            _ = (∫ z : ℤ → ℂ,
                  (commonSourceLikelihoodReal lower upper c M h z) ^ 2 ∂μ) +
                (∫ z : ℤ → ℂ,
                  (commonSourceLikelihoodReal lower upper c N h z) ^ 2 ∂μ) -
                2 * (∫ z : ℤ → ℂ,
                  commonSourceLikelihoodReal lower upper c M h z *
                    commonSourceLikelihoodReal lower upper c N h z ∂μ) := by
                    rw [integral_add hMI' hNI', integral_const_mul]
    _ = Real.exp (commonSourceLikelihoodEnergy lower upper c M h) -
        Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
          have hcross' :
              (∫ z : ℤ → ℂ,
                commonSourceLikelihoodReal lower upper c M h z *
                  commonSourceLikelihoodReal lower upper c N h z ∂μ) =
                Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := by
            calc
              (∫ z : ℤ → ℂ,
                commonSourceLikelihoodReal lower upper c M h z *
                  commonSourceLikelihoodReal lower upper c N h z ∂μ) =
                  ∫ z : ℤ → ℂ,
                    commonSourceLikelihoodReal lower upper c N h z *
                      commonSourceLikelihoodReal lower upper c M h z ∂μ := by
                    apply integral_congr_ae
                    filter_upwards [] with z
                    ring
              _ = Real.exp (commonSourceLikelihoodEnergy lower upper c N h) := hcross
          rw [hM, hN, hcross']
          ring

end NlsGge.Measure
