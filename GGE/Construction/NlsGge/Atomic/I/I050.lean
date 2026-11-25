import Mathlib
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Birkhoff.W12Tilt38e

set_option autoImplicit false

                                                                                                                                         
                                                                                                                                                                            
                                                                                                                                                                    
                                                                                                    

namespace NlsGge.Atomic.I050S1

open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
open scoped ENNReal ContDiff Real

noncomputable section

theorem coefficient_scaled (β : ℕ → ℝ) (j : ℕ) :
    NlsGge.coefficient (fun j => β j * ((Nat.factorial j : ℝ) ^ 4)) j = β j := by
  unfold NlsGge.coefficient
  have : ((Nat.factorial j : ℝ) ^ 4) ≠ 0 := by positivity
  field_simp

theorem I050_main_core : ((
  ∀ (β : ℕ → ℝ) (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
    (∀ j : ℕ, 0 ≤ β j) →
    (∀ r : ℝ, Summable (fun j : ℕ => β j * r ^ (2 * j))) →
    ENNReal.ofReal (2 / Real.pi) *
        ∫⁻ l : ℝ, ENNReal.ofReal ((∑' j : ℕ, β j * (2 * l) ^ (2 * j)) *
          actualGapHeightE02_38 (smoothL2_38 U hU hper) l)
      = ∑' j : ℕ, ENNReal.ofReal (β j * localCharge38 U j)
  : Prop)) := by
  intro β U hU hper hβ hsum
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun j => β j * ((Nat.factorial j : ℝ) ^ 4) := ⟨_, rfl⟩
  have hcj : ∀ j, NlsGge.coefficient c j = β j := fun j => by
    rw [hc]; exact coefficient_scaled β j
  have hcoef : ∀ j, 0 ≤ NlsGge.coefficient c j := fun j => by
    rw [hcj]; exact hβ j
  have hws : ∀ r, Summable (NlsGge.weightTerm c r) := fun r => by
    have : NlsGge.weightTerm c r = fun j : ℕ => β j * r ^ (2 * j) := by
      funext j
      unfold NlsGge.weightTerm
      rw [hcj]
    rw [this]; exact hsum r
  have h := NlsGge.Birkhoff.spectralEnergy_eq_chargeSeries_general38 c hcoef hws U hU hper
  have hw : ∀ l : ℝ, NlsGge.Weights.weight c (2 * l) = ∑' j : ℕ, β j * (2 * l) ^ (2 * j) := by
    intro l
    unfold NlsGge.Weights.weight NlsGge.weightTerm
    refine tsum_congr (fun j => ?_)
    rw [hcj]
  unfold NlsGge.Birkhoff.spectralEnergyW38 NlsGge.Birkhoff.chargeSeriesW38 at h
  simp only [hw, hcj] at h
  exact h

end

end NlsGge.Atomic.I050S1

namespace NlsGge.Atomic.I050S1.Final

set_option autoImplicit false
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
open scoped ENNReal ContDiff Real

theorem I050_main : ((
  ∀ (β : ℕ → ℝ) (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
    (∀ j : ℕ, 0 ≤ β j) →
    (∀ r : ℝ, Summable (fun j : ℕ => β j * r ^ (2 * j))) →
    ENNReal.ofReal (2 / Real.pi) *
        ∫⁻ l : ℝ, ENNReal.ofReal ((∑' j : ℕ, β j * (2 * l) ^ (2 * j)) *
          actualGapHeightE02_38 (smoothL2_38 U hU hper) l)
      = ∑' j : ℕ, ENNReal.ofReal (β j * localCharge38 U j)
  : Prop)) := NlsGge.Atomic.I050S1.I050_main_core


end NlsGge.Atomic.I050S1.Final
