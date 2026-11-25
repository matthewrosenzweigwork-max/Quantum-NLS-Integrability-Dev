import NlsGge.GK38.PairCompactFund

/-! # F6: compactness and joint L2 continuity of the discriminant

Source: GK, Chapter I, Proposition 1.2. Weak convergence controls every compact
spectral set, through the full-time fundamental-entry Volterra compactness theorem.
-/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- Componentwise weak L2 convergence yields locally uniform convergence on ℂ. -/
theorem discrim_weakContinuous {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) :
    TendstoLocallyUniformly (fun k z => discrim (φ k) z) (discrim φ₀) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [fundPair_weakContinuous_uniform38 hw hK (half_pos hε)] with k hk z hz
  rw [dist_eq_norm, norm_sub_rev, discrim_eq, discrim_eq]
  simp only [monodromyPair_eq_fundPair]
  have h0 := hk z hz ⟨1, zero_le_one, le_rfl⟩ 0 0
  have h1 := hk z hz ⟨1, zero_le_one, le_rfl⟩ 1 1
  calc
    _ = ‖(fundPair (φ k) z ⟨1, zero_le_one, le_rfl⟩ 0 0 -
            fundPair φ₀ z ⟨1, zero_le_one, le_rfl⟩ 0 0) +
          (fundPair (φ k) z ⟨1, zero_le_one, le_rfl⟩ 1 1 -
            fundPair φ₀ z ⟨1, zero_le_one, le_rfl⟩ 1 1)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

/-- Joint continuity in the accepted L2 product norm and complex spectral parameter. -/
theorem discrim_L2_continuous : Continuous (fun p : PotPair × ℂ => discrim p.1 p.2) :=
  continuousOn_univ.mp analyticOnNhd_discrim.continuousOn

end
end NlsGge.GK38
