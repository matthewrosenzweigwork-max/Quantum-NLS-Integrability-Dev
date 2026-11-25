import Mathlib
import NlsGge.Atomic.G4.G4046

                                                                                                        
                                                                                                                              
                                                                                                                                  
                                                                                                                                  
                                                                                                                               
                                                                                                                               
                                                                                                                                
                                                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.G4036Cauchy

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G4030Aux

open G4046Core in
theorem g4030_regular_bound (V : Set PotPair) (hV : V ⊆ sourceBetaW)
    (C : ℤ → ℂ) (R r : ℤ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hrR : ∀ n : ℤ, r n ≤ R n)
    (hfamily : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (hcollar : ∀ φ ∈ V, ∀ n : ℤ,
      gapSegment φ n ⊆ Metric.ball (C n) (r n) ∧
      muSeq φ n ∈ Metric.ball (C n) (r n))
    (hderiv : ∀ φ ∈ V, ∀ n : ℤ, ∀ lam ∈ Metric.ball (C n) (r n),
      DifferentiableAt ℂ (normalizedZeta n φ) lam ∧
      ‖deriv (normalizedZeta n φ) lam‖ ≤ L) :
  ∀ φ ∈ V, ∀ n : ℤ,
    ‖regularEtaIntegral n φ‖ ≤ (Real.pi / 2) * L *
      (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
  intro φ hφ n
  have hφS : φ ∈ sourceBetaW := hV hφ
  have hgk : φ ∈ gkW := G4017Aux.sourceBetaW_gkW hφS
  obtain ⟨c, N, hg, hs⟩ := hfamily φ hφ
  obtain ⟨hTanR, hodeR⟩ := g4036_family_ode φ hgk C R c N hg hs n
    (g4036_zero_period_family n φ hφS C R c N hg hs)
  have hid := g4036_identify n φ hφS C R c N hg hs
  have hsub : Metric.ball (C n) (r n) ⊆ Metric.ball (C n) (R n) :=
    Metric.ball_subset_ball (hrR n)
  have hTan := hTanR.mono hsub
  have hode := fun z (hz : z ∈ Metric.ball (C n) (r n)) => hodeR z (hsub hz)
  have hballgap : ∀ z ∈ gapSegment φ n, z ∈ Metric.ball (C n) (r n) :=
    fun z hz => (hcollar φ hφ n).1 hz
  have hlm : lamMinus φ n ∈ Metric.ball (C n) (r n) :=
    hballgap _ (left_mem_segment ℝ _ _)
  have hlp : lamPlus φ n ∈ Metric.ball (C n) (r n) :=
    hballgap _ (right_mem_segment ℝ _ _)
  have hτ : tauN φ n ∈ Metric.ball (C n) (r n) :=
    hballgap _ (g4036_tau_mem φ hgk n)
  have hμ : muSeq φ n ∈ Metric.ball (C n) (r n) := (hcollar φ hφ n).2
  have hKL : ∀ z ∈ Metric.ball (C n) (r n),
      ‖normalizedZeta n φ z - normalizedZeta n φ (tauN φ n)‖ ≤ L * ‖z - tauN φ n‖ := by
    intro z hz
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := normalizedZeta n φ)
      (f' := deriv (normalizedZeta n φ)) (C := L)
      (fun x hx => ((hderiv φ hφ n x hx).1.hasDerivAt).hasDerivWithinAt)
      (fun x hx => (hderiv φ hφ n x hx).2) (convex_ball (C n) (r n)) hτ hz
    exact this
  have hγ2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  have hτv : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hgk n
  have hodeC : ∀ z ∈ Metric.ball (C n) (r n),
      ((z - tauN φ n) ^ 2 - (lamPlus φ n - lamMinus φ n) ^ 2 / 4) *
          deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
        (z - tauN φ n) * cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := by
    intro z hz
    have := hode z hz
    rwa [hγ2] at this
  by_cases hne : lamPlus φ n = lamMinus φ n
  · -- collapsed gap: lamPlus = lamMinus
    have hreg : regularEtaIntegral n φ =
        (tauN φ n - muSeq φ n) *
          cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) (muSeq φ n) := by
      unfold regularEtaIntegral localRootAtDirichlet constantEtaCorrection elementaryEtaIntegral
      rw [dif_pos hne, if_pos hne, hid]
      simp
    have hode0 : ∀ z ∈ Metric.ball (C n) (r n),
        (z - tauN φ n) ^ 2 *
            deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
          (z - tauN φ n) *
            cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := by
      intro z hz
      have := hodeC z hz
      rw [hne, sub_self] at this
      simpa using this
    have hdeg := degenerate_bound hL hTan hode0 hKL hτ (muSeq φ n) hμ
    rw [hreg]
    have hg0 : ‖lamPlus φ n - lamMinus φ n‖ = 0 := by rw [hne, sub_self, norm_zero]
    rw [hg0, zero_add]
    refine hdeg.trans ?_
    have hn : 0 ≤ L * ‖muSeq φ n - tauN φ n‖ := by positivity
    have hpi := Real.pi_gt_three
    nlinarith
  · -- genuine gap
    have hγ : lamPlus φ n - lamMinus φ n ≠ 0 := sub_ne_zero.mpr hne
    set γ : ℂ := lamPlus φ n - lamMinus φ n with hγdef
    set ρ : ℂ := 2 * (muSeq φ n - tauN φ n) / γ with hρ
    set u : ℂ := slitPrimitive ρ with hu
    have hexp : Complex.exp u = -ρ - slitRoot ρ := G4027Aux.exp_slit ρ
    have hexpn : Complex.exp (-u) = -ρ + slitRoot ρ := G4027Aux.exp_slit_neg ρ
    have hcosh : Complex.cosh u = -ρ := by
      show (Complex.exp u + Complex.exp (-u)) / 2 = -ρ
      rw [hexp, hexpn]; ring
    have hsinh : Complex.sinh u = -slitRoot ρ := by
      rw [Complex.sinh, show (Complex.exp u - Complex.exp (-u)) / 2 = -slitRoot ρ by
        rw [hexp, hexpn]; ring]
    have hz : zOf (tauN φ n) γ u = muSeq φ n := by
      unfold zOf
      rw [hcosh, hρ]
      field_simp
      ring
    have him : |u.im| ≤ Real.pi := by
      rw [hu]
      unfold slitPrimitive
      rw [Complex.log_im]
      exact Complex.abs_arg_le_pi _
    have hm : tauN φ n - γ / 2 ∈ Metric.ball (C n) (r n) := by
      have : tauN φ n - γ / 2 = lamMinus φ n := by rw [hτv, hγdef]; ring
      rw [this]; exact hlm
    have hp : tauN φ n + γ / 2 ∈ Metric.ball (C n) (r n) := by
      have : tauN φ n + γ / 2 = lamPlus φ n := by rw [hτv, hγdef]; ring
      rw [this]; exact hlp
    have hodeC' : ∀ z ∈ Metric.ball (C n) (r n),
        ((z - tauN φ n) ^ 2 - γ ^ 2 / 4) *
            deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
          (z - tauN φ n) *
            cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := hodeC
    have hfin := psi_final hL hTan hodeC' hKL hm hp u (by rw [hz]; exact hμ) him
    rw [hz] at hfin
    have hreg : regularEtaIntegral n φ =
        -Psi (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n))
          (tauN φ n) γ (normalizedZeta n φ (tauN φ n) - 1) u := by
      unfold regularEtaIntegral localRootAtDirichlet constantEtaCorrection elementaryEtaIntegral
      rw [dif_neg hne, if_neg hne, hid]
      unfold Psi
      rw [hz, hsinh]
      change γ / 2 * slitRoot ρ * _ - _ * u = _
      ring
    rw [hreg, norm_neg]
    exact hfin

end G4030Aux
end
end NlsGge.GKDefinitionDesign
