import NlsGge.GK38.AngleCollapsedEndpointContinuity
import NlsGge.GK38.AngleDirichletAnalytic

/-! Source-only actual prerequisites for the book15.2 sequence argument at
Z_m minus E_m. A single open neighborhood gives all three positive distances.
No ordered-label regularity away from the collapsed base point is used. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleCollapsed_center_values38 (φ : PotPair) (hφ : φ ∈ gkW)
    (m : ℤ) (hgap : gamma2 φ m = 0) :
    lamMinus φ m = tauN φ m ∧ lamPlus φ m = tauN φ m := by
  have hends := (angleClosedGap_zero_iff38 φ hφ m).mp hgap
  have hminus : lamMinus φ m = tauN φ m := by
    rw [tauN_value38 φ hφ m, hends]
    ring
  exact ⟨hminus, hends.trans hminus⟩

theorem angleCollapsed_Dirichlet_distance_ne_zero38 (φ : PotPair) (hφ : φ ∈ gkW)
    (m : ℤ) (hgap : gamma2 φ m = 0) (hdet : angleEndpointDetector38 m φ ≠ 0) :
    muSeq φ m - tauN φ m ≠ 0 := by
  intro hz
  have hμ : muSeq φ m = lamMinus φ m :=
    (sub_eq_zero.mp hz).trans (angleCollapsed_center_values38 φ hφ m hgap).1.symm
  exact hdet ((angleEndpointDetector_zero_iff38 φ hφ m).mpr (Or.inl hμ))

/-- The exact nonzero-distance assumptions used in the book's convergent
sequence proof are earned simultaneously BEFORE every varying potential.
The neighborhood may include both collapsed and open pairs. -/
theorem angleActual_collapsed_Dirichlet_separation38 (φ : PotPair) (hφ : φ ∈ gkW)
    (m : ℤ) (hgap : gamma2 φ m = 0) (hdet : angleEndpointDetector38 m φ ≠ 0) :
    ∃ (U : Set PotPair) (d : ℝ),
      U ∈ nhds φ ∧ IsOpen U ∧ U ⊆ gkW ∧ 0 < d ∧
      ∀ ψ ∈ U, d ≤ ‖muSeq ψ m - tauN ψ m‖ ∧
        d ≤ ‖muSeq ψ m - lamMinus ψ m‖ ∧ d ≤ ‖muSeq ψ m - lamPlus ψ m‖ := by
  have hne := angleCollapsed_Dirichlet_distance_ne_zero38 φ hφ m hgap hdet
  have hnorm : 0 < ‖muSeq φ m - tauN φ m‖ := norm_pos_iff.mpr hne
  let d : ℝ := ‖muSeq φ m - tauN φ m‖ / 2
  have hd : 0 < d := half_pos hnorm
  have hb : d < ‖muSeq φ m - tauN φ m‖ := by dsimp only [d]; linarith
  have hμ := (analyticOnNhd_muSeq_complex38 m φ hφ).continuousAt
  have hc := angleActual_collapsed_endpoint_continuity38 φ hφ m hgap
  have hcenter := angleCollapsed_center_values38 φ hφ m hgap
  have ht : ∀ᶠ ψ in nhds φ, d < ‖muSeq ψ m - tauN ψ m‖ :=
    (hμ.sub (tauN_analytic m φ hφ).continuousAt).norm.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds hb)
  have hm : ∀ᶠ ψ in nhds φ, d < ‖muSeq ψ m - lamMinus ψ m‖ :=
    (hμ.sub hc.1).norm.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (by
        change d < ‖muSeq φ m-lamMinus φ m‖
        simpa only [hcenter.1] using hb))
  have hp : ∀ᶠ ψ in nhds φ, d < ‖muSeq ψ m - lamPlus ψ m‖ :=
    (hμ.sub hc.2).norm.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (by
        change d < ‖muSeq φ m-lamPlus φ m‖
        simpa only [hcenter.2] using hb))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (isOpen_gkW.mem_nhds hφ) ht) hm) hp)
  refine ⟨ball φ r, d, ball_mem_nhds φ hr, isOpen_ball,
    fun ψ hψ => (hsub hψ).1.1.1, hd, ?_⟩
  intro ψ hψ
  exact ⟨(hsub hψ).1.1.2.le, (hsub hψ).1.2.le, (hsub hψ).2.le⟩

end
end NlsGge.GK38
