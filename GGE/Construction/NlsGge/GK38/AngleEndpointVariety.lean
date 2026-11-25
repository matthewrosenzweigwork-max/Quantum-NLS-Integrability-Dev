import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.TauGamma

/-! Source-only actual scalar zero-set data for the two angle subvarieties.
No psi-family, path integral or removable-extension conclusion is assumed. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def angleEndpointDetector38 (m : ℤ) (φ : PotPair) : ℂ :=
  perChar φ (muSeq φ m)

theorem angleEndpointDetector_analytic38 (m : ℤ) :
    AnalyticOnNhd ℂ (angleEndpointDetector38 m) gkW := by
  intro φ hφ
  change AnalyticAt ℂ (fun ψ : PotPair => perChar ψ (muSeq ψ m)) φ
  exact AnalyticAt.comp
    (g := fun p : PotPair × ℂ => perChar p.1 p.2)
    (f := fun ψ : PotPair => (ψ, muSeq ψ m))
    (analyticOnNhd_perChar_joint38 (φ, muSeq φ m) (mem_univ _))
    ((analyticAt_id (𝕜 := ℂ)).prod (analyticOnNhd_muSeq_complex38 m φ hφ))

theorem angleEndpointDetector_zero_iff38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    angleEndpointDetector38 m φ = 0 ↔
      muSeq φ m = lamMinus φ m ∨ muSeq φ m = lamPlus φ m := by
  obtain ⟨c, N, hg, hs⟩ := isolating_family38 φ hφ
  have hmu := (hs.1 m).2.1
  obtain ⟨w, hw⟩ : (sphere (discC φ m) (discR φ m)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (hg.1 m).1.le
  have hboundary := ((hs.1 m).2.2.2.2.2.2.2.2.2.2.2.2 w hw).1
  have hmem := Lib.mem_zeroMultiset_iff_zero (z := muSeq φ m)
    ((analyticOnNhd_perChar_z φ).mono (subset_univ _)) ball_subset_closedBall
    ⟨w, sphere_subset_closedBall hw, hboundary⟩
  have hpair := (hs.1 m).2.2.2.2.1
  constructor
  · intro hzero
    have hm := hmem.mpr ⟨hmu, hzero⟩
    rw [← hpair] at hm
    simpa only [Multiset.mem_cons, Multiset.notMem_zero, or_false] using hm
  · intro hzero
    have hm : muSeq φ m ∈
        Lib.zeroMultiset (perChar φ) (ball (discC φ m) (discR φ m)) := by
      rw [← hpair]
      simpa only [Multiset.mem_cons, Multiset.notMem_zero, or_false] using hzero
    exact (hmem.mp hm).2

theorem angleClosedGap_zero_iff38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    gamma2 φ m = 0 ↔ lamPlus φ m = lamMinus φ m := by
  rw [gamma2_value38 φ hφ m, sq_eq_zero_iff, sub_eq_zero]

end
end NlsGge.GK38
