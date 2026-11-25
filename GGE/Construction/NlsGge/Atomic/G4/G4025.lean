import Mathlib
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G4.G4027
import NlsGge.Atomic.G4.G4045
import NlsGge.ThirdConsultation.G4.Basic

                                                                                                                                                 
                                                                                                                                                      
                                                                                                                                                   
                                                                                                                                               
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4025Aux

theorem noWinding (γ τ μ : ℂ) (hγ : γ ≠ 0) :
    NoWindingElementaryValue γ τ μ (elementarySlitIntegral γ τ μ) := by
  refine ⟨hγ, ?_, ?_⟩
  · exact G4027Aux.exp_slit _
  · unfold elementarySlitIntegral slitPrimitive
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _

theorem logbound (B g : ℝ) (hB : 0 ≤ B) (hg0 : 0 < g) (hg1 : g < 1) (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ B) :
    Real.log (1 + 2 * b / g) ≤ Real.log (1 + 2 * B) + |Real.log g| := by
  have hlg : Real.log g < 0 := Real.log_neg hg0 hg1
  have hab : |Real.log g| = -Real.log g := abs_of_neg hlg
  have h1g : 1 ≤ 1 / g := by rw [le_div_iff₀ hg0]; linarith
  have h2 : 2 * b / g ≤ 2 * B / g := by gcongr
  have h3 : (1 + 2 * B) / g = 1 / g + 2 * B / g := by ring
  have h1 : 1 + 2 * b / g ≤ (1 + 2 * B) / g := by rw [h3]; linarith
  have hpos : 0 < 1 + 2 * b / g := by positivity
  calc Real.log (1 + 2 * b / g) ≤ Real.log ((1 + 2 * B) / g) := Real.log_le_log hpos h1
    _ = Real.log (1 + 2 * B) - Real.log g := Real.log_div (by positivity) hg0.ne'
    _ = Real.log (1 + 2 * B) + |Real.log g| := by rw [hab]; ring

end G4025Aux

open G4025Aux in
theorem G4025 (n : ℤ) (ψ : PotPair) (hψ : ψ ∈ offGapSet n)
    (hgap : gamma2 ψ n = 0) :
  ∃ V : Set PotPair, V ∈ 𝓝 ψ ∧ V ⊆ offGapSet n ∧
  ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ φ ∈ V,
    0 < ‖lamPlus φ n - lamMinus φ n‖ → ‖lamPlus φ n - lamMinus φ n‖ < r →
    ‖elementaryEtaIntegral n φ‖ ≤ C *
      (1 + |Real.log ‖lamPlus φ n - lamMinus φ n‖|) := by
  have gk : ψ ∈ gkW := G4017Aux.sourceBetaW_gkW hψ.1
  have hμ : ContinuousAt (fun φ : PotPair => muSeq φ n) ψ :=
    ((analyticOnNhd_muSeq_complex38 n) ψ gk).continuousAt
  have hτ : ContinuousAt (fun φ : PotPair => tauN φ n) ψ :=
    ((tauN_analytic n) ψ gk).continuousAt
  have hcont : ContinuousAt (fun φ : PotPair => muSeq φ n - tauN φ n) ψ := hμ.sub hτ
  set B : ℝ := ‖muSeq ψ n - tauN ψ n‖ + 1 with hBdef
  have hB0 : 0 < B := by positivity
  have hVB : {φ : PotPair | ‖muSeq φ n - tauN φ n‖ < B} ∈ 𝓝 ψ :=
    hcont.norm.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  have hK : 0 ≤ Real.pi + Real.log 2 + Real.log (1 + 2 * B) := by
    have h1 : 0 ≤ Real.log (1 + 2 * B) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 := Real.pi_pos
    linarith
  refine ⟨offGapSet n ∩ {φ : PotPair | ‖muSeq φ n - tauN φ n‖ < B},
    inter_mem ((G4017Aux.offGap_open n).mem_nhds hψ) hVB, inter_subset_left,
    Real.pi + Real.log 2 + Real.log (1 + 2 * B) + 1, 1, by linarith, one_pos, ?_⟩
  intro φ hφ hpos hlt
  have hne : lamPlus φ n ≠ lamMinus φ n := fun h => by
    rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  have hγ : lamPlus φ n - lamMinus φ n ≠ 0 := sub_ne_zero.mpr hne
  unfold elementaryEtaIntegral
  rw [if_neg hne]
  have h45 := G4045 _ _ _ _ (noWinding (lamPlus φ n - lamMinus φ n) (tauN φ n) (muSeq φ n) hγ)
  have hlb := logbound B ‖lamPlus φ n - lamMinus φ n‖ hB0.le hpos hlt ‖muSeq φ n - tauN φ n‖
    (norm_nonneg _) (le_of_lt hφ.2)
  have hL := abs_nonneg (Real.log ‖lamPlus φ n - lamMinus φ n‖)
  nlinarith

end
end NlsGge.GKDefinitionDesign
