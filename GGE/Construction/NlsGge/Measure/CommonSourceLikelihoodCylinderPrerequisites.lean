import NlsGge.Measure.CommonSourceLikelihoodFiniteAfterScalarPrerequisite
import NlsGge.Measure.FiniteFourierRestrictionAfterRawPrerequisite
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NlsGge.Measure

/-- Coordinate projection from the actual sequence space to the contiguous
finite Fourier plane is measurable. -/
theorem measurable_cylinderModeProjection (M : ℕ) :
    Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * M + 1) =>
      z (NlsGge.Pilot.modeIndex M i)) := by
  fun_prop

/-- Restriction of a finite Fourier plane to an arbitrary subset of its signed
modes is measurable. -/
theorem measurable_finiteModeRestrictionAfterRaw (M : ℕ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes M) :
    Measurable (finiteModeRestrictionAfterRaw M U hU) := by
  unfold finiteModeRestrictionAfterRaw
  fun_prop

/-- Restricting after translation on the full finite plane agrees coordinatewise
with translating the restricted coordinates. -/
theorem finiteModeRestrictionAfterRaw_translate_comp
    (M : ℕ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes M)
    (h : ℤ → ℂ) :
    (fun y : NlsGge.Pilot.FourierPlane M => fun u : U =>
      finiteModeRestrictionAfterRaw M U hU
        (fun i => y i + h (NlsGge.Pilot.modeIndex M i)) u) =
      fun y u => finiteModeRestrictionAfterRaw M U hU y u + h u.1 := by
  funext y u
  have hlo : (-(M : ℤ)) ≤ u.1 := by
    simpa [NlsGge.Pilot.symmetricModes] using
      (Finset.mem_Icc.mp (hU u.1 u.2)).1
  have hhi : u.1 ≤ (M : ℤ) := by
    simpa [NlsGge.Pilot.symmetricModes] using
      (Finset.mem_Icc.mp (hU u.1 u.2)).2
  have hmode := Classical.choose_spec
    (NlsGge.Pilot.modeIndex_covers M u.1 hlo hhi)
  change y (Classical.choose (NlsGge.Pilot.modeIndex_covers M u.1 hlo hhi)) +
      h (NlsGge.Pilot.modeIndex M
        (Classical.choose (NlsGge.Pilot.modeIndex_covers M u.1 hlo hhi))) =
    y (Classical.choose (NlsGge.Pilot.modeIndex_covers M u.1 hlo hhi)) + h u.1
  rw [hmode]

private lemma sum_symmetricModes_eq_sum_modeIndex_prerequisite
    (N : ℕ) (f : ℤ → ℝ) :
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

/-- Pointwise raw-source likelihood is the finite Fourier-plane likelihood
pulled back by the actual signed-mode projection. -/
theorem commonSourceLikelihoodReal_eq_finite_projection
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (M : ℕ) (h z : ℤ → ℂ) :
    commonSourceLikelihoodReal lower upper c M h z =
      fullWeightFourierLikelihoodReal c.val M
        (fun i => h (NlsGge.Pilot.modeIndex M i))
        (fun i => z (NlsGge.Pilot.modeIndex M i)) := by
  unfold commonSourceLikelihoodReal commonSourceLikelihoodExponent
    fullWeightFourierLikelihoodReal
  rw [sum_symmetricModes_eq_sum_modeIndex_prerequisite]

end NlsGge.Measure
