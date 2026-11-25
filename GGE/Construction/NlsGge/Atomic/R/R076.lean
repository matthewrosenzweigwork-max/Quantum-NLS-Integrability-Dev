import Mathlib
import NlsGge.Weights.TiltedMoments
import NlsGge.Weights.Regularity
import NlsGge.Definitions.PilotInterfaces

                                                                                                                                                                                                                                                         
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

def weightedPoissonFourth (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, c j * (NlsGge.Weights.poissonTerm t j) ^ 4

def tiltedPoissonFourth (c : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
  c j * (NlsGge.Weights.poissonTerm t j) ^ 4 / weightedPoissonFourth c t

def meanJ (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, (j : ℝ) * tiltedPoissonFourth c t j

def meanJ2 (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, (j : ℝ) ^ 2 * tiltedPoissonFourth c t j

theorem tiltedPoissonFourth_probabilityTerm
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hc : NlsGge.Pilot.AdmittedCoefficients lower upper c)
    (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => c j * (NlsGge.Weights.poissonTerm t j) ^ 4) ∧
    0 < weightedPoissonFourth c t ∧
    (∀ j : ℕ, tiltedPoissonFourth c t j = NlsGge.Weights.probabilityTerm c (t ^ 2) j) ∧
    HasSum (tiltedPoissonFourth c t) 1 := by
  obtain ⟨hlower, -, hbd⟩ := hc
  have hb1 : ∀ j : ℕ, lower ≤ c j := fun j => (hbd j).1
  have hb2 : ∀ j : ℕ, c j ≤ upper := fun j => (hbd j).2
  have hs := NlsGge.Weights.weightedPoissonFourth_summable lower upper c hlower hb1 hb2 t ht
  have hp := NlsGge.Weights.weightedPoissonFourth_pos lower upper c hlower hb1 hb2 t ht
  have hid : ∀ j : ℕ, tiltedPoissonFourth c t j = NlsGge.Weights.probabilityTerm c (t ^ 2) j := by
    intro j
    rw [NlsGge.Weights.probabilityTerm_poissonFourth_identity lower upper c hlower hb1 hb2 t ht j]
    rfl
  refine ⟨hs, hp, hid, ?_⟩
  have h := NlsGge.Weights.probabilityTerm_hasSum lower upper c hlower hb1 hb2 (t ^ 2)
  have hf : tiltedPoissonFourth c t = NlsGge.Weights.probabilityTerm c (t ^ 2) := funext hid
  rw [hf]
  exact h

theorem weightedPoissonFourth_uniform_bounds (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      ∀ c : ℕ → ℝ, NlsGge.Pilot.AdmittedCoefficients lower upper c →
      ∀ t : ℝ, 4 ≤ t →
        Summable (fun j : ℕ => c j * (NlsGge.Weights.poissonTerm t j) ^ 4) ∧
        L * Real.rpow t (-3 / 2 : ℝ) ≤ weightedPoissonFourth c t ∧
        weightedPoissonFourth c t ≤ U * Real.rpow t (-3 / 2 : ℝ) := by
  obtain ⟨L, U, hL, hU, h⟩ :=
    NlsGge.Weights.weightedPoissonFourth_uniform_bounds lower upper hlower hlower_upper
  refine ⟨L, U, hL, hU, fun c hc t ht => ?_⟩
  obtain ⟨hlo, -, hbd⟩ := hc
  have hb1 : ∀ j : ℕ, lower ≤ c j := fun j => (hbd j).1
  have hb2 : ∀ j : ℕ, c j ≤ upper := fun j => (hbd j).2
  obtain ⟨h1, h2⟩ := h c hb1 hb2 t ht
  have ht0 : 0 ≤ t := by linarith
  exact ⟨NlsGge.Weights.weightedPoissonFourth_summable lower upper c hlo hb1 hb2 t ht0, h1, h2⟩

end
end NlsGge.ThirdConsultation.R
