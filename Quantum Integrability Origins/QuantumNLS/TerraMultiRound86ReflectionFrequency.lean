import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound85DynamicsInput
import QuantumNLS.TerraMultiRound85ReflectionFlow
import QuantumNLS.GlobalCompatFinalR47a
import QuantumNLS.ChartFrequencies

/-! Reflection-frequency intermediate using the sole named predecessor input. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound86ReflectionFrequency
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound85ReflectionFlow
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

/-- The physical frequency at a reflected field is the original frequency
at the reversed index; the same witness satisfies the predecessor rotations. -/
theorem reflection_frequency_intermediate
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν : ℤ → QuantumNLS.ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
        Φ κ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n) ∧
      ∀ (u : L2T L) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 (-n) →
        ν n (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u)) =
          ν (-n) (QuantumNLS.RootIndexedMasses.masses hκ u) := by
  obtain ⟨ν, hrot, -⟩ := (QuantumNLS.REF88Final.global_physical_dynamics hκ (chart_of_extension h hc)).1
  refine ⟨ν, hrot, ?_⟩
  intro u n ha
  let R := QuantumNLS.ResetNormalizationUniqueness.reflectR L
  have hchart (v : L2T L) : Φ κ (R v) n = Φ κ v (-n) := ((hc.1 κ hκ).1 v n).2.2.2.1
  have hact : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (R u)).1 n := by
    rw [← h.moduli, hchart, h.moduli]
    exact ha
  have hw : Φ κ (R u) n ≠ 0 := by
    intro hz
    rw [← h.moduli, hz, norm_zero] at hact
    norm_num at hact
  apply QuantumNLS.ChartFrequencies.freq_eq_of_char_eq hw
  intro t
  calc
    _ = Φ κ (flowMap hκ.le (R u) t) n := (hrot (R u) t n hact).symm
    _ = Φ κ (R (flowMap hκ.le u t)) n := by rw [reflect_flow hκ.le u t]
    _ = Φ κ (flowMap hκ.le u t) (-n) := hchart _
    _ = Complex.exp (-Complex.I * ((t * ν (-n) (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u (-n) := hrot u t (-n) ha
    _ = _ := by rw [hchart]

#print axioms reflection_frequency_intermediate
end QuantumNLS.TerraMultiRound86ReflectionFrequency
