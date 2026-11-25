import NlsGge.Measure.ActualCountableGaussianFiniteRestriction
import NlsGge.Measure.FourierGaussian
import NlsGge.Sobolev.WeightedHilbert
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace NlsGge.Measure

private noncomputable def finiteModePositionAfterRaw (N : ℕ) (n : ℤ)
    (hn : n ∈ NlsGge.Pilot.symmetricModes N) : Fin (2 * N + 1) :=
  Classical.choose (NlsGge.Pilot.modeIndex_covers N n
    (by simpa [NlsGge.Pilot.symmetricModes] using (Finset.mem_Icc.mp hn).1)
    (by simpa [NlsGge.Pilot.symmetricModes] using (Finset.mem_Icc.mp hn).2))

private theorem modeIndex_finiteModePositionAfterRaw (N : ℕ) (n : ℤ)
    (hn : n ∈ NlsGge.Pilot.symmetricModes N) :
    NlsGge.Pilot.modeIndex N (finiteModePositionAfterRaw N n hn) = n :=
  Classical.choose_spec (NlsGge.Pilot.modeIndex_covers N n
    (by simpa [NlsGge.Pilot.symmetricModes] using (Finset.mem_Icc.mp hn).1)
    (by simpa [NlsGge.Pilot.symmetricModes] using (Finset.mem_Icc.mp hn).2))

/-- Restrict a finite contiguous Fourier plane to a finite signed-mode set. -/
def finiteModeRestrictionAfterRaw (N : ℕ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes N) :
    NlsGge.Pilot.FourierPlane N → (u : U) → ℂ :=
  fun y u => y (finiteModePositionAfterRaw N u.1 (hU u.1 u.2))

private theorem finiteModeRestriction_comp_projectionAfterRaw
    (N : ℕ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes N) :
    (fun y : NlsGge.Pilot.FourierPlane N =>
      fun u : U => finiteModeRestrictionAfterRaw N U hU y u) ∘
        (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
          z (NlsGge.Pilot.modeIndex N i)) =
      fun z : ℤ → ℂ => fun u : U => z u.1 := by
  funext z u
  exact congrArg z (modeIndex_finiteModePositionAfterRaw N u.1 (hU u.1 u.2))

/-- An arbitrary finite signed-coordinate marginal of the finite Fourier law is
the actual product of the corresponding source-coordinate Gaussian factors. -/
theorem fullWeightFourierGaussian_map_finiteModeRestriction_afterRaw
    (N : ℕ) (c : ℕ → ℝ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes N) :
    (NlsGge.Measure.fullWeightFourierGaussian N c).map
        (NlsGge.Measure.finiteModeRestrictionAfterRaw N U hU) =
      Measure.pi (fun u : U =>
        NlsGge.Measure.complexGaussian
          (NlsGge.Measure.fullWeightRate c (u.1))) := by
  let P : (ℤ → ℂ) → NlsGge.Pilot.FourierPlane N :=
    fun z i => z (NlsGge.Pilot.modeIndex N i)
  have hP := NlsGge.Measure.fullWeightSequenceGaussian_map_modes N c
  have hcomp :
      (fun y : NlsGge.Pilot.FourierPlane N =>
        NlsGge.Measure.finiteModeRestrictionAfterRaw N U hU y) ∘ P =
        fun z : ℤ → ℂ => fun u : U => z u.1 := by
    exact finiteModeRestriction_comp_projectionAfterRaw N U hU
  calc
    (NlsGge.Measure.fullWeightFourierGaussian N c).map
        (NlsGge.Measure.finiteModeRestrictionAfterRaw N U hU) =
        ((NlsGge.Measure.fullWeightSequenceGaussian c).map P).map
          (NlsGge.Measure.finiteModeRestrictionAfterRaw N U hU) := by rw [hP]
    _ = (NlsGge.Measure.fullWeightSequenceGaussian c).map
          ((NlsGge.Measure.finiteModeRestrictionAfterRaw N U hU) ∘ P) := by
          rw [Measure.map_map (by
            unfold NlsGge.Measure.finiteModeRestrictionAfterRaw
            fun_prop) (by fun_prop)]
    _ = (NlsGge.Measure.fullWeightSequenceGaussian c).map
          (fun z : ℤ → ℂ => fun u : U => z u.1) := by rw [hcomp]
    _ = Measure.pi (fun u : U =>
          NlsGge.Measure.complexGaussian
            (NlsGge.Measure.fullWeightRate c (u.1))) := by
          change Measure.map U.restrict
            (NlsGge.Measure.countableComplexGaussian
              (NlsGge.Measure.fullWeightRate c)) = _
          exact NlsGge.Measure.countableComplexGaussian_map_finiteRestriction
            (NlsGge.Measure.fullWeightRate c) U

/-- Restricting a translated finite Fourier Gaussian to U gives the product
of the true translated coordinate marginals. -/
theorem fullWeightFourierGaussian_map_add_finiteModeRestriction_afterRaw
    (N : ℕ) (c : ℕ → ℝ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes N)
    (h : ℤ → ℂ) :
    (NlsGge.Measure.fullWeightFourierGaussian N c).map
        (fun y : NlsGge.Pilot.FourierPlane N =>
          fun u : U =>
            finiteModeRestrictionAfterRaw N U hU y u + h (u.1)) =
      Measure.pi (fun u : U =>
        (NlsGge.Measure.complexGaussian
          (NlsGge.Measure.fullWeightRate c (u.1))).map
            (fun z : ℂ => z + h (u.1))) := by
  let P : (ℤ → ℂ) → NlsGge.Pilot.FourierPlane N :=
    fun z i => z (NlsGge.Pilot.modeIndex N i)
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c
  have hP := NlsGge.Measure.fullWeightSequenceGaussian_map_modes N c
  have hcomp :
      (fun y : NlsGge.Pilot.FourierPlane N =>
        fun u : U =>
          finiteModeRestrictionAfterRaw N U hU y u + h (u.1)) ∘ P =
        fun z : ℤ → ℂ => fun u : U => z u.1 + h (u.1) := by
    funext z u
    change z (NlsGge.Pilot.modeIndex N
      (finiteModePositionAfterRaw N u.1 (hU u.1 u.2))) + h u.1 = _
    rw [modeIndex_finiteModePositionAfterRaw]
  calc
    (NlsGge.Measure.fullWeightFourierGaussian N c).map
        (fun y : NlsGge.Pilot.FourierPlane N =>
          fun u : U =>
            finiteModeRestrictionAfterRaw N U hU y u + h (u.1)) =
        (μ.map P).map
          (fun y : NlsGge.Pilot.FourierPlane N =>
            fun u : U =>
              finiteModeRestrictionAfterRaw N U hU y u + h (u.1)) := by rw [hP]
    _ = μ.map ((fun y : NlsGge.Pilot.FourierPlane N =>
          fun u : U =>
            finiteModeRestrictionAfterRaw N U hU y u + h (u.1)) ∘ P) := by
          rw [Measure.map_map (by
            unfold NlsGge.Measure.finiteModeRestrictionAfterRaw
            fun_prop) (by fun_prop)]
    _ = μ.map (fun z : ℤ → ℂ => fun u : U => z u.1 + h (u.1)) := by rw [hcomp]
    _ = Measure.pi (fun u : U =>
          (NlsGge.Measure.complexGaussian
            (NlsGge.Measure.fullWeightRate c (u.1))).map
              (fun z : ℂ => z + h (u.1))) := by
          simpa [μ, NlsGge.Measure.fullWeightSequenceGaussian] using
            NlsGge.Measure.countableComplexGaussian_map_add_finiteRestriction
              (NlsGge.Measure.fullWeightRate c) h U

end NlsGge.Measure
