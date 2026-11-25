import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound85DynamicsInput
import QuantumNLS.TerraMultiRound85FlowScalingL2
import QuantumNLS.GlobalCompatFinalR47a
import QuantumNLS.ChartFrequencies

/-! Scaling-frequency intermediate. R-EF8C2837 is instantiated at both couplings. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound86FrequencyScaling
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound85FlowScalingL2
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

/-- Frequency scaling on every realized action vector. The input is the
printed physical-dynamics predecessor at every positive coupling. -/
theorem frequency_scaling_intermediate (s : ℝ) (hs : 0 < s)
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hscaled : Extension (κ*s^2) (mul_pos hκ (sq_pos_of_pos hs)) d
      (Φl (κ*s^2)) (Ψl (κ*s^2)) (Φ (κ*s^2)) (Ψ (κ*s^2)))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν ν' : ℤ → QuantumNLS.ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
        Φ κ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ),
        0 < (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u).1 n →
        Φ (κ*s^2) (flowMap (mul_pos hκ (sq_pos_of_pos hs)).le u t) n =
          Complex.exp (-Complex.I * ((t * ν' n (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u) : ℝ) : ℂ)) * Φ (κ*s^2) u n) ∧
      ∀ (u : L2T L) (n : ℤ),
        0 < (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u).1 n →
        ν n (QuantumNLS.RootIndexedMasses.masses hκ (s • u)) =
          ν' n (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u) := by
  let hκ' : 0 < κ*s^2 := mul_pos hκ (sq_pos_of_pos hs)
  obtain ⟨ν, hrot, -⟩ := (QuantumNLS.REF88Final.global_physical_dynamics hκ (chart_of_extension h hc)).1
  obtain ⟨ν', hrot', -⟩ := (QuantumNLS.REF88Final.global_physical_dynamics hκ' (chart_of_extension hscaled hc)).1
  refine ⟨ν, ν', hrot, hrot', ?_⟩
  intro u n ha
  have hscale (v : L2T L) : Φ κ (s • v) n = (s • Φ (κ*s^2) v) n :=
    congrArg (fun z : QuantumNLS.D01LocalPrimitive.K => z n) (hc.2.1 κ hκ s hs v)
  have hact : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (s • u)).1 n := by
    rw [← h.moduli, hscale]
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
      hscaled.moduli]
    exact mul_pos (sq_pos_of_pos hs) ha
  have hw : Φ κ (s • u) n ≠ 0 := by
    intro hz
    rw [← h.moduli, hz, norm_zero] at hact
    norm_num at hact
  apply QuantumNLS.ChartFrequencies.freq_eq_of_char_eq hw
  intro t
  calc
    _ = Φ κ (flowMap hκ.le (s • u) t) n := (hrot (s • u) t n hact).symm
    _ = Φ κ (s • flowMap hκ'.le u t) n := by
      apply congrArg (fun v : L2T L => Φ κ v n)
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      exact flow_scaling hκ.le s u t
    _ = (s • Φ (κ*s^2) (flowMap hκ'.le u t)) n := hscale _
    _ = _ := by
      rw [hscale]
      simp only [lp.coeFn_smul, Pi.smul_apply, RCLike.real_smul_eq_coe_mul]
      rw [hrot' u t n ha]
      ring

#print axioms frequency_scaling_intermediate
end QuantumNLS.TerraMultiRound86FrequencyScaling
