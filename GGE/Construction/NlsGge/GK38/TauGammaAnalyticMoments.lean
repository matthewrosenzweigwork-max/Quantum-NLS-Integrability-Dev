import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.TauGammaSpectralDerivatives
import NlsGge.GK38.Lib.ParamCircleAnalytic

/-! Analyticity is proved on local fixed circles only after the same-pair contour gluing. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem moment_joint_boundary_analytic38 (V : Set PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (Function.uncurry (fun φ => momentIntegrand38 φ k))
      (V ×ˢ sphere (C n) (R n)) := by
  intro p hp
  exact ((analyticAt_snd.pow k).mul (analyticOnNhd_perCharDeriv_joint38 p (mem_univ _))).div
    (analyticOnNhd_perChar_joint38 p (mem_univ _))
    (isolating_periodic_boundary38 (hf p.1 hp.1) n p.2 hp.2)

theorem fixedMoment_analytic38 (V : Set PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hV : IsOpen V) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ V) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun φ => fixedMoment38 φ C R n k) V := by
  have h := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
    (fun φ => momentIntegrand38 φ k) hV (isolating_radius_pos38 (hf φ₀ hφ₀) n)
    (moment_joint_boundary_analytic38 V C R hf n k)
  have hint := h.1
  exact analyticOnNhd_const.mul h.2

theorem symmetric_pair_powers_analytic38 (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun φ => (lamMinus φ n) ^ k + (lamPlus φ n) ^ k) gkW := by
  intro φ hφ
  obtain ⟨V, hV, _, hVo, _, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV := mem_of_mem_nhds hV
  have h := fixedMoment_analytic38 V C R hVo hf φ hφV n k
  apply (h φ hφV).congr
  filter_upwards [hV] with ψ hψ
  exact fixedMoment_pair38 ψ C R (hf ψ hψ) n k

theorem tauN_analytic38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => tauN38 C R φ n) gkW := by
  have h : AnalyticOnNhd ℂ (fun φ => (lamPlus φ n + lamMinus φ n) / 2) gkW := by
    simpa only [pow_one, add_comm] using (symmetric_pair_powers_analytic38 n 1).div_const (c := (2 : ℂ))
  intro φ hφ
  apply (h φ hφ).congr
  filter_upwards [isOpen_gkW.mem_nhds hφ] with ψ hψ
  exact (tau_pair_mean38 C R hsel ψ hψ n).symm

theorem q2N_analytic38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => q2N38 C R φ n) gkW := by
  intro φ hφ
  apply (symmetric_pair_powers_analytic38 n 2 φ hφ).congr
  filter_upwards [isOpen_gkW.mem_nhds hφ] with ψ hψ
  exact (add_comm _ _).trans (q2_pair_squares38 C R hsel ψ hψ n).symm

theorem tauGamma_analytic38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => tauN38 C R φ n) gkW ∧
      AnalyticOnNhd ℂ (fun φ => gamma2N38 C R φ n) gkW := by
  have ht := tauN_analytic38 C R hsel n
  have hq := q2N_analytic38 C R hsel n
  exact ⟨ht, (analyticOnNhd_const.mul hq).sub (analyticOnNhd_const.mul (ht.pow 2))⟩

theorem pair_polynomial_analytic38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => (tauN38 C R p.1 n - p.2) ^ 2 -
      gamma2N38 C R p.1 n / 4) (gkW ×ˢ univ) := by
  intro p hp
  have h := tauGamma_analytic38 C R hsel n
  exact (((h.1 p.1 hp.1).comp analyticAt_fst).sub analyticAt_snd).pow 2 |>.sub
    (((h.2 p.1 hp.1).comp analyticAt_fst).div_const (c := (4 : ℂ)))

end
end NlsGge.GK38
