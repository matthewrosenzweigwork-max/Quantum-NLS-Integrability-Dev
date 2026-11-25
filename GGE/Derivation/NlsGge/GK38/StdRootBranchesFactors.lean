import NlsGge.GK38.StdRootBranchesSlit

/-! Actual factors on the full complex cut complement. Only symmetric spectral
data are composed; individual endpoint labels need no analytic choice. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem rootDomain_avoids38 {p : PotPair × ℂ} (hp : p ∈ rootDomain38) (n : ℤ) :
    p.2 ∉ segment ℝ (lamMinus p.1 n) (lamPlus p.1 n) := by
  intro hz
  exact hp.2 (mem_iUnion.mpr ⟨n, hz⟩)

theorem segment_spectral_iff38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ) :
    z ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) ↔
      ∃ t : ℝ, t ∈ Icc 0 1 ∧ (z - tauN φ n)^2 = (t : ℂ)^2 * gamma2 φ n / 4 := by
  rw [tauN_value38 φ hφ n, gamma2_value38 φ hφ n]
  simpa only [add_comm, ← neg_sub (lamMinus φ n) (lamPlus φ n), neg_sq] using
    segment_symmetric_iff38 (lamMinus φ n) (lamPlus φ n) z

theorem rootFactor_sq38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    rootFactor38 n p ^ 2 =
      ((lamMinus p.1 n - p.2) * (lamPlus p.1 n - p.2)) / (Lib.piN n : ℂ)^2 := by
  rw [rootFactor38, div_pow, tauN_value38 p.1 hp.1 n, gamma2_value38 p.1 hp.1 n]
  rw [add_comm (lamPlus p.1 n), stdRoot_sq38 _ _ _ (rootDomain_avoids38 hp n)]

theorem rootFactor_ne_zero38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    rootFactor38 n p ≠ 0 := by
  rw [rootFactor38, tauN_value38 p.1 hp.1 n, gamma2_value38 p.1 hp.1 n]
  rw [add_comm (lamPlus p.1 n)]
  exact div_ne_zero (stdRoot_ne_zero38 _ _ _ (rootDomain_avoids38 hp n))
    (by exact_mod_cast Lib.piN_ne_zero n)

theorem rootFactor_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (rootFactor38 n) rootDomain38 := by
  intro p hp
  have hs := stdRoot_slit38 (lamMinus p.1 n) (lamPlus p.1 n) p.2
    (rootDomain_avoids38 hp n)
  rw [add_comm (lamMinus p.1 n), ← tauN_value38 p.1 hp.1 n,
    ← gamma2_value38 p.1 hp.1 n] at hs
  exact (stdRoot_analyticAt38 ((tauN_analytic n p.1 hp.1).comp analyticAt_fst)
    ((gamma2_analytic n p.1 hp.1).comp analyticAt_fst) analyticAt_snd hs.1 hs.2).div_const

end
end NlsGge.GK38
