import NlsGge.GK38.ActionBranchScalar

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionBranch
noncomputable section

-- Reviewed minimum replan: pointwise root continuity, not broad domain-composition inference.
theorem continuous_root_ray (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun t : ℝ => canonRoot38 (realSlice (t • u)) z) := by
  have hpot : Continuous (fun t : ℝ => realSlice (t • u)) :=
    continuous_realSlice.comp (continuous_id.smul continuous_const)
  have hpath : Continuous (fun t : ℝ => (realSlice (t • u), z)) :=
    hpot.prodMk continuous_const
  apply continuous_iff_continuousAt.mpr
  intro t
  have hr : AnalyticAt ℂ (fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (realSlice (t • u), z) :=
    canonRoot_analytic38 (realSlice (t • u), z) (root_domain (t • u) z hz)
  have hrc : ContinuousAt (fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (realSlice (t • u), z) := hr.continuousAt
  exact ContinuousAt.comp (f := fun s : ℝ => (realSlice (s • u), z))
    (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (x := t)
    hrc hpath.continuousAt

theorem continuous_rho_ray (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun t : ℝ => rho (t • u) z) := by
  have hpot : Continuous (fun t : ℝ => realSlice (t • u)) :=
    continuous_realSlice.comp (continuous_id.smul continuous_const)
  have hDc : Continuous (fun φ : PotPair => discrim φ z) :=
    continuousOn_univ.mp (analyticOnNhd_discrim_phi z).continuousOn
  have hD : Continuous (fun t : ℝ => discrim (realSlice (t • u)) z) := hDc.comp hpot
  exact (hD.sub (continuous_root_ray u z hz)).div_const 2

end
end NlsGge.GK38.ActionBranch
