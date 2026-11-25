import NlsGge.Measure.CommonSourceLikelihoodFiniteAfterScalarPrerequisite
import NlsGge.Measure.FiniteFourierRestrictionAfterRawPrerequisite
import NlsGge.Measure.FiniteFourierGaussianTranslation
import NlsGge.Measure.CommonSourceLikelihoodCylinderPrerequisites
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace NlsGge.Measure

private lemma sum_symmetricModes_eq_sum_modeIndex_cylinder (N : ℕ) (f : ℤ → ℝ) :
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

private def cylinderModeProjection (M : ℕ) (z : ℤ → ℂ) : NlsGge.Pilot.FourierPlane M :=
  fun i => z (NlsGge.Pilot.modeIndex M i)

private lemma commonLikelihood_eq_cylinderFinite (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (M : ℕ)
    (h z : ℤ → ℂ) :
    commonSourceLikelihoodReal lower upper c M h z =
      fullWeightFourierLikelihoodReal c.val M
        (cylinderModeProjection M h) (cylinderModeProjection M z) := by
  unfold commonSourceLikelihoodReal commonSourceLikelihoodExponent
    fullWeightFourierLikelihoodReal cylinderModeProjection
  rw [sum_symmetricModes_eq_sum_modeIndex_cylinder]

private lemma cylinderLikelihood_measurable (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (M : ℕ)
    (h : NlsGge.Pilot.FourierPlane M) :
    Measurable (fun y : NlsGge.Pilot.FourierPlane M =>
      ENNReal.ofReal (fullWeightFourierLikelihoodReal c.val M h y)) := by
  unfold fullWeightFourierLikelihoodReal
  fun_prop

/-- On every measurable finite signed-coordinate cylinder inside the cutoff, the
actual source finite likelihood integrates to the translated finite Gaussian
product mass. This is a finite-cylinder identity only; it does not identify the
full countable translated law with a density. -/
theorem commonSourceLikelihood_cutoff_finiteCylinder
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (hLower : 0 < lower)
    (hBound : ∀ j, lower ≤ c.val j)
    (hUpper : ∀ j, c.val j ≤ upper)
    (M : ℕ) (h : ℤ → ℂ)
    (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes M)
    (B : Set ((u : U) → ℂ))
    (hB : MeasurableSet B) :
    (∫⁻ z in
        ((NlsGge.Measure.finiteModeRestrictionAfterRaw M U hU) ∘
          (cylinderModeProjection M)) ⁻¹' B,
        ENNReal.ofReal (commonSourceLikelihoodReal lower upper c M h z)
        ∂fullWeightSequenceGaussian c.val) =
      (Measure.pi (fun u : U =>
        (complexGaussian (fullWeightRate c.val u.1)).map
          (fun z : ℂ => z + h u.1))) B := by
  classical
  let μ : Measure (ℤ → ℂ) := fullWeightSequenceGaussian c.val
  let ν : Measure (NlsGge.Pilot.FourierPlane M) := fullWeightFourierGaussian M c.val
  let P : (ℤ → ℂ) → NlsGge.Pilot.FourierPlane M := cylinderModeProjection M
  let R : NlsGge.Pilot.FourierPlane M → (u : U) → ℂ :=
    finiteModeRestrictionAfterRaw M U hU
  let H : NlsGge.Pilot.FourierPlane M := fun i => h (NlsGge.Pilot.modeIndex M i)
  let T : NlsGge.Pilot.FourierPlane M → NlsGge.Pilot.FourierPlane M :=
    fun y i => y i + H i
  let D : NlsGge.Pilot.FourierPlane M → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (fullWeightFourierLikelihoodReal c.val M H y)
  let F : Set (NlsGge.Pilot.FourierPlane M) := R ⁻¹' B
  let E : Set (ℤ → ℂ) := P ⁻¹' F
  have hPmeas : Measurable P := by
    change Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * M + 1) =>
      z (NlsGge.Pilot.modeIndex M i))
    exact measurable_cylinderModeProjection M
  have hRmeas : Measurable R := by
    change Measurable (finiteModeRestrictionAfterRaw M U hU)
    exact measurable_finiteModeRestrictionAfterRaw M U hU
  have hTmeas : Measurable T := by
    dsimp [T]
    fun_prop
  have hDmeas : Measurable D := by
    dsimp [D]
    exact cylinderLikelihood_measurable lower upper c M H
  have hF : MeasurableSet F := hB.preimage hRmeas
  have hE : MeasurableSet E := hB.preimage (hRmeas.comp hPmeas)
  have hmap : μ.map P = ν := by
    change (fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun i : Fin (2 * M + 1) =>
          z (NlsGge.Pilot.modeIndex M i)) = fullWeightFourierGaussian M c.val
    exact fullWeightSequenceGaussian_map_modes M c.val
  have hRN : ν.map T = ν.withDensity D := by
    simpa [ν, T, H, D, fullWeightFourierLikelihoodReal] using
      (fullWeightFourierGaussian_map_add_withDensity_afterNormalization
        lower upper c.val hLower hBound hUpper M H)
  have hshift : ν.map (fun y : NlsGge.Pilot.FourierPlane M =>
      fun u : U => R y u + h u.1) =
      Measure.pi (fun u : U =>
        (complexGaussian (fullWeightRate c.val u.1)).map
          (fun z : ℂ => z + h u.1)) := by
    simpa [ν, R] using
      (fullWeightFourierGaussian_map_add_finiteModeRestriction_afterRaw
        M c.val U hU h)
  have hcompose :
      (fun y : NlsGge.Pilot.FourierPlane M => fun u : U => R (T y) u) =
        fun y u => R y u + h u.1 := by
    simpa [T, H, R] using
      (finiteModeRestrictionAfterRaw_translate_comp M U hU h)
  have hshiftMap :
      (ν.map T).map R = Measure.pi (fun u : U =>
        (complexGaussian (fullWeightRate c.val u.1)).map
          (fun z : ℂ => z + h u.1)) := by
    calc
      (ν.map T).map R = ν.map (R ∘ T) := by
        rw [Measure.map_map hRmeas hTmeas]
      _ = ν.map (fun y : NlsGge.Pilot.FourierPlane M =>
          fun u : U => R y u + h u.1) := by
            change ν.map (fun y : NlsGge.Pilot.FourierPlane M =>
              fun u : U => R (T y) u) = _
            rw [hcompose]
      _ = _ := hshift
  have hBprod :
      (Measure.pi (fun u : U =>
        (complexGaussian (fullWeightRate c.val u.1)).map
          (fun z : ℂ => z + h u.1))) B =
        ∫⁻ y in F, D y ∂ν := by
    calc
      (Measure.pi (fun u : U =>
        (complexGaussian (fullWeightRate c.val u.1)).map
          (fun z : ℂ => z + h u.1))) B = ((ν.map T).map R) B := by
            rw [hshiftMap]
      _ = (ν.map T) F := Measure.map_apply hRmeas hB
      _ = (ν.withDensity D) F := by rw [hRN]
      _ = ∫⁻ y in F, D y ∂ν := MeasureTheory.withDensity_apply D hF
  have hmappedIntegral :
      ∫⁻ y in F, D y ∂μ.map P = ∫⁻ z in E, D (P z) ∂μ := by
    simpa [F, E, R, P] using
      (MeasureTheory.setLIntegral_map (μ := μ) (g := P) (s := F)
        hF hDmeas hPmeas)
  have hplaneIntegral : ∫⁻ y in F, D y ∂μ.map P = ∫⁻ y in F, D y ∂ν := by
    rw [hmap]
  have hrawEq (z : ℤ → ℂ) :
      ENNReal.ofReal (commonSourceLikelihoodReal lower upper c M h z) = D (P z) := by
    rw [commonSourceLikelihoodReal_eq_finite_projection]
    rfl
  calc
    (∫⁻ z in E, ENNReal.ofReal (commonSourceLikelihoodReal lower upper c M h z) ∂μ) =
        ∫⁻ z in E, D (P z) ∂μ := by
          apply MeasureTheory.setLIntegral_congr_fun hE
          intro z hz
          exact hrawEq z
    _ = ∫⁻ y in F, D y ∂μ.map P := hmappedIntegral.symm
    _ = ∫⁻ y in F, D y ∂ν := hplaneIntegral
    _ = (Measure.pi (fun u : U =>
          (complexGaussian (fullWeightRate c.val u.1)).map
            (fun z : ℂ => z + h u.1))) B := hBprod.symm

end NlsGge.Measure
