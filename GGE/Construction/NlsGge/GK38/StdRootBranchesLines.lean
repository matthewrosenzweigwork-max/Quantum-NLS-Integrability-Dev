import NlsGge.GK38.StdRootBranchesFactors
import NlsGge.GK38.Lib.AnalyticL2Majorant

/-! The actual symmetric mean-shift Hilbert map earns the scalar-disc majorant.
No Banach-ball compactness or uniform coordinate-tail inference is used. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def rootTauQ38 (p : PotPair × ℂ) (n : ℤ) : ℝ :=
  ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖^2

theorem rootTauQ_nonneg38 (p : PotPair × ℂ) (n : ℤ) : 0 ≤ rootTauQ38 p n := sq_nonneg _

theorem rootTau_l2_analytic38 : ∃ A : PotPair → Lib.L2Z,
    (∀ φ ∈ gkW, ∀ n : ℤ, A φ n = tauN φ n - (n : ℂ) * (Real.pi : ℂ)) ∧
      AnalyticOnNhd ℂ A gkW := by
  exact local_l2_analytic_realization38 gkW _ isOpen_gkW
    (fun n => (tauN_analytic n).sub analyticOnNhd_const)
    (fun φ hφ => (tauGamma_l2 φ hφ).1)

theorem rootTauQ_line_majorant38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38)
    (h : PotPair × ℂ) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ q : ℤ → ℝ, Summable q ∧
      ∀ ζ : ℂ, ‖ζ‖ < ρ → p + ζ • h ∈ rootDomain38 →
        ∀ n : ℤ, rootTauQ38 (p + ζ • h) n ≤ q n := by
  obtain ⟨A, hAv, hAa⟩ := rootTau_l2_analytic38
  let L : ℂ → PotPair := fun ζ => p.1 + ζ • h.1
  have hL : ∀ ζ, AnalyticAt ℂ L ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hW : IsOpen {ζ : ℂ | L ζ ∈ gkW} :=
    isOpen_gkW.preimage (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW 0 (by simpa [L] using hp.1)
  have ha : AnalyticOnNhd ℂ (fun ζ => A (L ζ)) (ball 0 r) := by
    intro ζ hζ
    exact (hAa (L ζ) (hball hζ)).comp (hL ζ)
  obtain ⟨q, hq, hbound⟩ := Lib.summable_sup_sq_of_analytic (fun ζ => A (L ζ)) r ha
    (ρ' := r / 2) ⟨by linarith, by linarith⟩
  refine ⟨r / 2, by linarith, q, hq, fun ζ hζ hζW n => ?_⟩
  have h := hbound ζ (mem_ball_zero_iff.mpr hζ) n
  rw [hAv (L ζ) (by simpa [L] using hζW.1) n] at h
  exact h

theorem rootTauQ_local_mass38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ q ∈ ball p r, q ∈ rootDomain38 →
      Summable (rootTauQ38 q) ∧ (∑' n : ℤ, rootTauQ38 q n) ≤ B := by
  obtain ⟨V, hV, B, hB⟩ := (tauGamma_l2 p.1 hp.1).1
  have hprod : {q : PotPair × ℂ | q.1 ∈ V} ∈ 𝓝 p :=
    continuous_fst.continuousAt.preimage_mem_nhds hV
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hprod
  exact ⟨r, hr, B, fun q hq _ => hB q.1 (hsub hq)⟩

end
end NlsGge.GK38
