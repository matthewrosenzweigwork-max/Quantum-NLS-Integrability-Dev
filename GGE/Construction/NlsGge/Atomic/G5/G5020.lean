import Mathlib
import NlsGge.Atomic.G3.G3023
import NlsGge.Atomic.G3.G3031All
import NlsGge.Atomic.G4.G4001
import NlsGge.ThirdConsultation.G3.G3026Support
import NlsGge.ThirdConsultation.G3.G3026Host
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G5.G5018Host

                                                                                                    
                                                                           
                                                                                                                                                    
                                                                                                                                    
                                                                                                                                                           
                                                                                                                                                      
                                                                                                                                                              
                                                                                                                          

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5020Aux
noncomputable section

theorem term_analytic (n m : ℤ) : AnalyticOnNhd ℂ (offDiagonalBeta n m) sourceW := by
  by_cases hmn : m = n
  · subst hmn
    have h0 : offDiagonalBeta m m = fun _ => (0 : ℂ) :=
      funext fun φ => offDiagonalBeta_diag m φ
    rw [h0]
    exact analyticOnNhd_const
  · exact (G3_023 n m hmn).1

theorem partial_analytic (n : ℤ) (s : Finset ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => ∑ m ∈ s, offDiagonalBeta n m φ) sourceW :=
  Finset.analyticOnNhd_fun_sum (𝕜 := ℂ) (f := fun m => offDiagonalBeta n m) _ fun m _ => term_analytic n m

theorem fderiv_term (n m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) :
    fderiv ℂ (offDiagonalBeta n m) φ =
      if m = n then 0 else fderiv ℂ (beta m n) φ := by
  by_cases hmn : m = n
  · subst hmn
    have h0 : offDiagonalBeta m m = fun _ => (0 : ℂ) :=
      funext fun φ => offDiagonalBeta_diag m φ
    rw [h0]
    simp
  · simp [hmn, beta]

theorem fderiv_partial (n : ℤ) (s : Finset ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) :
    fderiv ℂ (fun ψ : PotPair => ∑ m ∈ s, offDiagonalBeta n m ψ) φ =
      ∑ m ∈ s, if m = n then 0 else fderiv ℂ (beta m n) φ := by
  rw [fderiv_fun_sum (fun m _ => ((term_analytic n m) φ hφ).differentiableAt)]
  exact Finset.sum_congr rfl fun m _ => fderiv_term n m φ hφ

theorem tail_norm (n : ℤ) (R : ℕ) (s : Finset ℤ) (hs : Finset.Icc (-(R : ℤ)) (R : ℤ) ⊆ s)
    (ψ : PotPair) (hψ : ψ ∈ sourceBetaW)
    (hsum : Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m ψ‖ else 0)) :
    ‖betaSum n ψ - ∑ m ∈ s, offDiagonalBeta n m ψ‖ ≤
      ∑' m : ℤ, (if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m ψ‖ else 0) := by
  classical
  have h := hasSum_offDiagonalBeta_betaSum n ψ hψ
  have hg : HasSum (fun m : ℤ => if m ∈ s then offDiagonalBeta n m ψ else 0)
      (∑ m ∈ s, offDiagonalBeta n m ψ) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ)
      (f := fun m : ℤ => if m ∈ s then offDiagonalBeta n m ψ else 0)
      (s := s) (fun b hb => by simp [hb])
    have e : ∑ m ∈ s, (if m ∈ s then offDiagonalBeta n m ψ else 0) =
        ∑ m ∈ s, offDiagonalBeta n m ψ :=
      Finset.sum_congr rfl fun m hm => by simp [hm]
    rwa [e] at this
  have hd := h.sub hg
  refine hd.norm_le_of_bounded hsum.hasSum (fun m => ?_)
  by_cases hm : m ∈ s
  · simp only [hm, if_true, sub_self, norm_zero]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  · have hm' : (R : ℝ) < |(m : ℝ)| := by
      have hnot : ¬ (-(R : ℤ) ≤ m ∧ m ≤ (R : ℤ)) := fun h2 =>
        hm (hs (Finset.mem_Icc.mpr h2))
      rw [not_and_or, not_le, not_le] at hnot
      rcases hnot with h2 | h2
      · have : ((m : ℤ) : ℝ) < -(R : ℝ) := by exact_mod_cast h2
        calc (R : ℝ) < -(m : ℝ) := by linarith
          _ ≤ |(m : ℝ)| := neg_le_abs _
      · have : (R : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast h2
        exact lt_of_lt_of_le this (le_abs_self _)
    simp [hm, hm']

theorem key_estimate (n : ℤ) (φ0 : PotPair) (ρ : ℝ) (hρ : 0 < ρ)
    (C M : ℝ) (U2 : Set PotPair)
    (hU2 : AnalyticOnNhd ℂ (betaSum n) U2)
    (hball : ball φ0 ρ ⊆ U2 ∩ sourceBetaW)
    (hR : ∀ R : ℕ, ∀ φ ∈ ball φ0 ρ,
      Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ∧
      (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ≤
        C * M * fixedIndexReciprocalTail n R)
    (R : ℕ) (s : Finset ℤ) (hs : Finset.Icc (-(R : ℤ)) (R : ℤ) ⊆ s)
    (φ : PotPair) (hφ : φ ∈ ball φ0 (ρ / 2)) :
    ‖fderiv ℂ (betaSum n) φ - ∑ m ∈ s, (if m = n then 0 else fderiv ℂ (beta m n) φ)‖ ≤
      (C * M * fixedIndexReciprocalTail n R) / (ρ / 2) := by
  have hr : 0 < ρ / 2 := by positivity
  have hsub : ball φ (ρ / 2) ⊆ ball φ0 ρ := by
    intro x hx
    rw [mem_ball] at hx hφ ⊢
    have := dist_triangle x φ φ0
    linarith
  have hφB : φ ∈ ball φ0 ρ := hsub (mem_ball_self hr)
  have hφW : φ ∈ sourceW := sourceFamily.V_W (hball hφB).2
  have han : AnalyticOnNhd ℂ
      (fun ψ : PotPair => betaSum n ψ - ∑ m ∈ s, offDiagonalBeta n m ψ) (ball φ (ρ / 2)) := by
    refine AnalyticOnNhd.sub (hU2.mono fun x hx => (hball (hsub hx)).1) ?_
    exact (partial_analytic n s).mono fun x hx => sourceFamily.V_W (hball (hsub hx)).2
  have hb : ∀ v ∈ ball φ (ρ / 2),
      ‖betaSum n v - ∑ m ∈ s, offDiagonalBeta n m v‖ ≤ C * M * fixedIndexReciprocalTail n R := by
    intro v hv
    have hvB := hsub hv
    obtain ⟨hsm, hle⟩ := hR R v hvB
    exact (tail_norm n R s hs v (hball hvB).2 hsm).trans hle
  have hc := NlsGge.Atomic.G4.norm_fderiv_le_of_ball_bound hr han hb
  have hdb : DifferentiableAt ℂ (betaSum n) φ := (hU2 φ (hball hφB).1).differentiableAt
  have hdp : DifferentiableAt ℂ (fun ψ : PotPair => ∑ m ∈ s, offDiagonalBeta n m ψ) φ :=
    ((partial_analytic n s) φ hφW).differentiableAt
  have hfd : fderiv ℂ (fun ψ : PotPair => betaSum n ψ - ∑ m ∈ s, offDiagonalBeta n m ψ) φ =
      fderiv ℂ (betaSum n) φ - ∑ m ∈ s, (if m = n then 0 else fderiv ℂ (beta m n) φ) := by
    rw [fderiv_fun_sub hdb hdp, fderiv_partial n s φ hφW]
  rw [hfd] at hc
  exact hc

end
end G5020Aux

noncomputable section

theorem G5020 (n : ℤ) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ IsOpen V ∧ V ⊆ sourceBetaW ∧
    (∀ φ ∈ V, HasSum
      (fun m : ℤ => if m = n then 0 else fderiv ℂ (beta m n) φ)
      (fderiv ℂ (betaSum n) φ)) ∧
    TendstoUniformlyOn
      (fun s : Finset ℤ => fun φ =>
        ∑ m ∈ s, if m = n then 0 else fderiv ℂ (beta m n) φ)
      (fun φ => fderiv ℂ (betaSum n) φ) atTop V := by
  obtain ⟨V1, C, M, hV1o, hφ0V1, hV1S, hC, hM, hV⟩ :=
    G3031AllAux.betaLocalDataAll φ₀ hφ₀
  obtain ⟨ρ, hρ, hball0⟩ := Metric.isOpen_iff.mp hV1o φ₀ hφ0V1
  have hball : ball φ₀ ρ ⊆ sourceBetaW ∩ sourceBetaW := fun x hx =>
    ⟨hV1S (hball0 hx), hV1S (hball0 hx)⟩
  have hR : ∀ R : ℕ, ∀ φ ∈ ball φ₀ ρ,
      Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ∧
      (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ≤
        C * M * fixedIndexReciprocalTail n R := fun R φ hφ => by
    obtain ⟨hs, hspec, hb⟩ := hV φ (hball0 hφ)
    exact tail_bounds hC n R φ hs hspec (fun m => hb n m)
  have htail := tendsto_fixedIndexReciprocalTail n
  have hr : 0 < ρ / 2 := by positivity
  have hVsub : ball φ₀ (ρ / 2) ⊆ sourceBetaW := fun x hx =>
    (hball (ball_subset_ball (by linarith) hx)).2
  have hunif : TendstoUniformlyOn
      (fun s : Finset ℤ => fun φ =>
        ∑ m ∈ s, if m = n then 0 else fderiv ℂ (beta m n) φ)
      (fun φ => fderiv ℂ (betaSum n) φ) atTop (ball φ₀ (ρ / 2)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε' : 0 < ε * (ρ / 2) / (C * M + 1) := by positivity
    have hT : ∀ᶠ R : ℕ in atTop, fixedIndexReciprocalTail n R < ε * (ρ / 2) / (C * M + 1) :=
      htail.eventually (gt_mem_nhds hε')
    obtain ⟨R, hRlt⟩ := hT.exists
    have hev : ∀ᶠ s : Finset ℤ in atTop, Finset.Icc (-(R : ℤ)) (R : ℤ) ⊆ s :=
      eventually_ge_atTop _
    refine hev.mono fun s hs φ hφ => ?_
    have h1 := G5020Aux.key_estimate n φ₀ ρ hρ C M sourceBetaW
      (betaSum_analyticOnNhd_sourceBetaW n) hball hR R s hs φ hφ
    rw [dist_eq_norm]
    have hCM : 0 ≤ C * M := mul_nonneg hC.le hM
    have hc1 : 0 < C * M + 1 := by linarith
    calc ‖fderiv ℂ (betaSum n) φ - ∑ m ∈ s, (if m = n then 0 else fderiv ℂ (beta m n) φ)‖
        ≤ (C * M * fixedIndexReciprocalTail n R) / (ρ / 2) := h1
      _ ≤ (C * M * (ε * (ρ / 2) / (C * M + 1))) / (ρ / 2) := by
          gcongr
      _ = ε * (C * M / (C * M + 1)) := by
          field_simp
      _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one hc1).2 (by linarith))
  exact ⟨ball φ₀ (ρ / 2), ball_mem_nhds φ₀ hr, isOpen_ball, hVsub,
    fun φ hφ => hunif.tendsto_at hφ, hunif⟩

end
end NlsGge.GKDefinitionDesign
