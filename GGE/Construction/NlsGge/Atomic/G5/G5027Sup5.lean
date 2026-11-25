import Mathlib
import NlsGge.Atomic.G5.G5027Sup3
import NlsGge.Atomic.G5.G5027Sup4
import NlsGge.Atomic.G5.G5028Sup1
import NlsGge.Atomic.G5.G5028Sup2
import NlsGge.Atomic.G5.G5018Host
import NlsGge.Atomic.G5.G5024
import NlsGge.Atomic.G6.G6020

                                                                                       
                                                                                        
                                                                                                                           
                                                                                                                 
                                                                                                                     
                                                                                                                             
                                                                                                                     
                                                                                                                        
                                                                                                          
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5027Aux
noncomputable section

theorem g5027_core (k m : ℤ) (u₀ : PhysicalL2) (u : ℕ → PhysicalL2)
    (hgap : gamma2 (realSlice u₀) k ≠ 0)
    (hleft : gkMu u₀ k = actualGapLowerAllE02_38 u₀ k)
    (hinterior : ∀ j : ℕ, InteriorRealDirichletGap k (u j))
    (hlim : Tendsto u atTop (𝓝 u₀))
    (hβ : AnalyticOnNhd ℂ (betaSum k) sourceBetaW) :
  (∀ j : ℕ, antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) k) ≠ 0) ∧
  Tendsto (fun j : ℕ =>
    let φ := realSlice (u j)
    pairGradientCLM (angleIntegralDerivative k m φ) -
      (psiAt m (muSeq φ k) φ / antiDiscrim φ (muSeq φ k)) •
        (pairGradient (fun ψ => muSeq ψ k) φ -
          pairGradient (fun ψ => lamMinus ψ k) φ)) atTop (𝓝 0) := by
  have hanti : ∀ j : ℕ, antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) k) ≠ 0 :=
    fun j => g5018_antiDiscrim_ne_zero (u j) k (hinterior j)
  refine ⟨hanti, ?_⟩
  obtain ⟨V, a, b, c, hc, hVo, hφ0V, hVsub, haA, hbA, hrA, hVall, hdiag⟩ :=
    tip_package k u₀ hgap hβ
  have hgkV : ∀ φ ∈ V, φ ∈ gkW := fun φ hφ => sourceFamily.W_gk (hVsub hφ).1
  have hgapV : ∀ φ ∈ V, gap φ k ≠ 0 := fun φ hφ => G3024Endpoint.gap_ne k φ (hVsub hφ)
  have hzb : ∀ φ ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, a φ + (t : ℂ) * (muSeq φ k - a φ) - b φ ≠ 0 := by
    intro φ hφ t ht h
    have hb := ((hVall φ hφ).2.2 t ht).1
    rw [h, norm_zero] at hb
    have : 0 < ‖gap φ k‖ := norm_pos_iff.2 (hgapV φ hφ)
    linarith
  -- the tip: mu = lamMinus = a, b = lamPlus at realSlice u₀
  have hL := (NlsGge.Atomic.G5028.lower_endpoint_simple u₀ k hgap).1
  have hμL : muSeq (realSlice u₀) k = lamMinus (realSlice u₀) k := by
    rw [muSeq_eq_gkMu38, hleft, hL]
  have haμ : a (realSlice u₀) = muSeq (realSlice u₀) k :=
    a_eq_mu_of_lower k (realSlice u₀) _ _ (hVall _ hφ0V).1
      ((hVall _ hφ0V).2.2 1 ⟨zero_le_one, le_rfl⟩).1 (hgapV _ hφ0V) hμL
  have hbP : b (realSlice u₀) = lamPlus (realSlice u₀) k := by
    rcases Set.pair_eq_pair_iff.1 (hVall _ hφ0V).1 with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exfalso
      apply hgapV _ hφ0V
      show lamPlus (realSlice u₀) k - lamMinus (realSlice u₀) k = 0
      rw [← h1, haμ, hμL, sub_self]
  have hlt : (lamMinus (realSlice u₀) k).re < (lamPlus (realSlice u₀) k).re := by
    obtain ⟨hP, hM⟩ := lamPlus_real u₀ k
    rw [hP, hM, Complex.ofReal_re, Complex.ofReal_re]
    exact NlsGge.Atomic.G5028.open_gap_lt u₀ k hgap
  have hpairEv : ∀ᶠ ψ in 𝓝 (realSlice u₀),
      (a ψ = lamMinus ψ k ∧ b ψ = lamPlus ψ k) ∨ (a ψ = lamPlus ψ k ∧ b ψ = lamMinus ψ k) := by
    filter_upwards [hVo.mem_nhds hφ0V] with ψ hψ
    exact Set.pair_eq_pair_iff.1 (hVall ψ hψ).1
  have hevL : ∀ᶠ ψ in 𝓝 (realSlice u₀), lamMinus ψ k = a ψ :=
    NlsGge.Atomic.G5028.eventually_lamMinus_eq k (realSlice u₀) a b (haA _ hφ0V) (hbA _ hφ0V)
      hpairEv (by rw [haμ, hμL]) hbP hlt
  obtain ⟨W, hWsub, hWo, hφ0W⟩ := _root_.mem_nhds_iff.1 (hevL.and (hVo.mem_nhds hφ0V))
  -- nonvanishing of the delta-fixed root
  have hr_ne : ∀ φ ∈ V, antiDiscrim φ (muSeq φ k) ≠ 0 → tipRoot k b c φ ≠ 0 := by
    intro φ hφ hA h0
    have hsq := (hVall φ hφ).2.1
    rw [h0] at hsq
    have hμa : muSeq φ k = a φ := by linear_combination -hsq
    have hmem : a φ ∈ ({lamMinus φ k, lamPlus φ k} : Set ℂ) := by rw [← (hVall φ hφ).1]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    apply hA
    apply (pow_eq_zero_iff two_ne_zero).1
    rw [G3024Endpoint.anti_sq k φ (hgkV φ hφ), hμa]
    rcases hmem with h | h <;> rw [h] <;> ring
  -- the integrand factor is analytic at the tip
  have hW0 : realSlice u₀ ∈ sourceW := (hVsub hφ0V).1
  have hs0 : c * (a (realSlice u₀) - b (realSlice u₀)) ∈ Complex.slitPlane := by
    have h := ((hVall _ hφ0V).2.2 0 ⟨le_rfl, zero_le_one⟩).2
    simpa using h
  have hz0 : a (realSlice u₀) - b (realSlice u₀) ≠ 0 := by
    have h := hzb _ hφ0V 0 ⟨le_rfl, zero_le_one⟩
    simpa using h
  have hgA : AnalyticAt ℂ (tipG m k b c) (realSlice u₀, a (realSlice u₀)) :=
    tipG_analyticAt m k b c hc _ _ hW0
      (mem_disc_of_pair k _ (hgkV _ hφ0V) _ _ (hVall _ hφ0V).1) (hbA _ hφ0V) hs0 hz0
  have hμA : AnalyticOnNhd ℂ (fun ψ : PotPair => muSeq ψ k) V := fun φ hφ =>
    analyticOnNhd_muSeq_complex38 k φ (hgkV φ hφ)
  -- the approximants, shifted into W
  have hφs : Tendsto (fun j => realSlice (u j)) atTop (𝓝 (realSlice u₀)) :=
    (realSlice.continuous.tendsto u₀).comp hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hφs.eventually (hWo.mem_nhds hφ0W))
  have hψW : ∀ j : ℕ, realSlice (u (j + N)) ∈ W := fun j => hN (j + N) (by omega)
  have hψV : ∀ j : ℕ, realSlice (u (j + N)) ∈ V := fun j => (hWsub (hψW j)).2
  have hψne : ∀ j : ℕ, tipRoot k b c (realSlice (u (j + N))) ≠ 0 := fun j =>
    hr_ne _ (hψV j) (hanti (j + N))
  have hT := tip_asymptotic V hVo (realSlice u₀) hφ0V a (fun ψ => muSeq ψ k) (tipRoot k b c)
    haA hμA hrA (fun φ hφ => (hVall φ hφ).2.1) haμ.symm (tipG m k b c) hgA
    (fun j => realSlice (u (j + N))) (hφs.comp (tendsto_add_atTop_nat N)) hψne
  have hP := ((NlsGge.ThirdConsultation.G5017Support1.pairGradientL).continuous.tendsto 0).comp hT
  rw [map_zero] at hP
  rw [← Filter.tendsto_add_atTop_iff_nat N]
  refine Tendsto.congr (fun j => ?_) hP
  set φ := realSlice (u (j + N)) with hφdef
  have hφV := hψV j
  have hφW := hψW j
  -- (i) the angle-integral derivative is the derivative of the explicit lift
  have hi : angleIntegralDerivative k m φ =
      fderiv ℂ (fun ψ => tipRoot k b c ψ * segK (tipG m k b c) a (fun ψ => muSeq ψ k) ψ) φ := by
    by_cases hkm : k = m
    · subst hkm
      simp only [angleIntegralDerivative, ite_true]
      exact hdiag φ hφV
    · simp only [angleIntegralDerivative, hkm, ite_false, beta]
      apply Filter.EventuallyEq.fderiv_eq
      have hev1 : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V := hVo.mem_nhds hφV
      have hev : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V ∧ tipRoot k b c ψ ≠ 0 :=
        hev1.and ((hrA φ hφV).continuousAt.eventually_ne (hψne j))
      filter_upwards [hev] with ψ hψ
      exact offdiag_rep m k hkm a b c hc ψ (hVsub hψ.1) (hbA ψ hψ.1) (hVall ψ hψ.1).1
        (fun t ht => ((hVall ψ hψ.1).2.2 t ht).2) (hzb ψ hψ.1) (hVall ψ hψ.1).2.1 hψ.2
  -- (ii) lamMinus = a near the approximant
  have hii : fderiv ℂ (fun ψ => lamMinus ψ k) φ = fderiv ℂ a φ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hWo.mem_nhds hφW] with ψ hψ
    exact (hWsub hψ).1
  -- (iii) the coefficient
  have hiii : tipG m k b c (φ, muSeq φ k) / tipRoot k b c φ =
      psiAt m (muSeq φ k) φ / antiDiscrim φ (muSeq φ k) := by
    have hgk := hgkV φ hφV
    have hrP0 : rootProduct k (φ, muSeq φ k) ≠ 0 :=
      (G2_021 k).2.2 _ ⟨hgk, G3014Aux.avoids_other φ hgk k⟩
    have hS1 : G3014Aux.sqrtB c (muSeq φ k - b φ) ≠ 0 := by
      have h := hzb φ hφV 1 ⟨zero_le_one, le_rfl⟩
      refine G3014Aux.sqrtB_ne hc ?_
      intro h'
      apply h
      push_cast
      linear_combination h'
    have hA := hanti (j + N)
    simp only [tipG, tipRoot, psiAt, psi]
    field_simp
  dsimp only
  rw [← hiii, hi]
  simp only [Function.comp_apply, map_sub, map_smul,
    NlsGge.ThirdConsultation.G5017Support1.pairGradientL_apply, pairGradient, hii]
  rfl

end
end G5027Aux
end NlsGge.GKDefinitionDesign
