import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.GradEigenDirichlet

/-! Source-only concrete angle prerequisite: the actual globally enumerated
Dirichlet label is complex analytic on the existing certified gkW. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleDirichlet_unique_in_circle38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) (z : ℂ)
    (hz : z ∈ ball (C n) (R n)) (hroot : dirichletChar φ z = 0) :
    z = muSeq φ n := by
  obtain ⟨c, N, hg, hs⟩ := hf
  obtain ⟨w, hw⟩ : (sphere (C n) (R n)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (hg.1 n).1.le
  have hboundary := ((hs.1 n).2.2.2.2.2.2.2.2.2.2.2.2 w hw).2.1
  have hmem := (Lib.mem_zeroMultiset_iff_zero
    ((analyticOnNhd_dirichletChar_z φ).mono (subset_univ _))
    ball_subset_closedBall ⟨w, sphere_subset_closedBall hw, hboundary⟩).mpr
      ⟨hz, hroot⟩
  rw [← (hs.1 n).2.2.2.2.2.1] at hmem
  simpa only [Multiset.mem_singleton] using hmem

theorem angleDirichlet_analytic_derivative38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ ∧
    HasFDerivAt (fun ψ : PotPair => muSeq ψ n)
      (GradEigen38.bilinearGradient
        (GradEigen38.state φ (muSeq φ n) (![1, 1] : PairVec38))) φ := by
  obtain ⟨V, hV, _, _, _, C, R, c, N, hg, hs⟩ :=
    local_isolatingFamily_common38 φ hφ
  have hbase := hs φ (mem_of_mem_nhds hV)
  have hf : IsolatingFamily38 φ C R := ⟨c, N, hg, hbase⟩
  have ha := analyticOnNhd_dirichletChar_z φ (muSeq φ n) (mem_univ _)
  have horder := (isolating_aux_simple38 φ C R hf n).1
  have hsimple : deriv (dirichletChar φ) (muSeq φ n) ≠ 0 := by
    have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha (n := 1)).mp horder
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h.2
  obtain ⟨_, _, U, κ, hU, hφU, hκ, hvalue, hroot, hder⟩ :=
    GradEigen38.complex_dirichlet_simple_target φ (muSeq φ n)
      (muSeq_root38 φ n) hsimple
  have hκbase : κ φ ∈ ball (C n) (R n) := by
    rw [hvalue]
    exact (hbase.1 n).2.1
  have hstay : ∀ᶠ ψ in nhds φ, κ ψ ∈ ball (C n) (R n) :=
    (hκ φ hφU).continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hκbase)
  have heq : κ =ᶠ[nhds φ] fun ψ : PotPair => muSeq ψ n := by
    filter_upwards [hV, hU.mem_nhds hφU, hstay] with ψ hψV hψU hψB
    exact angleDirichlet_unique_in_circle38 ψ C R ⟨c, N, hg, hs ψ hψV⟩ n (κ ψ)
      hψB (hroot ψ hψU)
  exact ⟨(hκ φ hφU).congr heq, hder.congr_of_eventuallyEq heq.symm⟩

theorem analyticOnNhd_muSeq_complex38 (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => muSeq φ n) gkW :=
  fun φ hφ => (angleDirichlet_analytic_derivative38 φ hφ n).1

end
end NlsGge.GK38
