import NlsGge.GK38.EigenvalueCompactnessClusters
import NlsGge.GK38.DirichletRealWeakTransport
import Mathlib.Topology.MetricSpace.Algebra

/-! # S7: F6 and exact endpoint circles preserve analytic multiplicity -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem perChar_function_eq38 (φ : PotPair) :
    perChar φ = fun z => discrim φ z * discrim φ z - 4 := by
  funext z
  simp only [perChar, perCharOf, pow_two]

theorem perChar_weak_locallyUniform38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    (hw : IsWeakLim u u₀) :
    TendstoLocallyUniformly (fun k z => perChar (realSlice (u k)) z)
      (perChar (realSlice u₀)) atTop := by
  have hd := discrim_weakContinuous (weakLim_realSlice38 hw)
  have hc : Continuous (discrim (realSlice u₀)) :=
    continuousOn_univ.mp (analyticOnNhd_discrim_z (realSlice u₀)).continuousOn
  have hp := hd.mul₀ hd hc hc
  have h4 : TendstoLocallyUniformly (fun _ : ℕ => fun _ : ℂ => (4 : ℂ)) (fun _ => 4) atTop :=
    (tendsto_const_nhds.tendstoUniformly_const).tendstoLocallyUniformly
  simp_rw [perChar_function_eq38]
  simpa only [Pi.mul_def, Pi.sub_def] using! hp.sub h4

theorem endpoint_weak_cluster38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (n : ℤ) (x : ℝ) (hx : EndpointAt38 u₀ n x)
    (ε : ℝ) (hε : 0 < ε) : ∃ r : ℝ, 0 < r ∧ r < ε ∧
    ∀ᶠ k in atTop,
      Multiset.card (Lib.zeroMultiset (perChar (realSlice (u k))) (ball (x : ℂ) r)) =
        if actualGapLowerAllE02_38 u₀ n = actualGapUpperAllE02_38 u₀ n then 2 else 1 := by
  obtain ⟨r, hr, hrε, hiso, hcard⟩ := endpoint_reference_cluster38 u₀ n x hx ε hε
  have hne : ∀ z ∈ sphere (x : ℂ) r, perChar (realSlice u₀) z ≠ 0 := by
    intro z hz
    apply hiso z (sphere_subset_closedBall hz)
    intro he
    have hh : dist z (x : ℂ) = r := hz
    rw [he, dist_self] at hh
    linarith
  have hu : TendstoUniformlyOn (fun k z => perChar (realSlice (u k)) z)
      (perChar (realSlice u₀)) atTop (sphere (x : ℂ) r) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp (perChar_weak_locallyUniform38 hw))
      _ (isCompact_sphere _ _)
  refine ⟨r, hr, hrε, ?_⟩
  have he := Lib.hurwitz_circle atTop hr
    (Eventually.of_forall (fun k => (analyticOnNhd_perChar_z (realSlice (u k))).mono (subset_univ _)))
    ((analyticOnNhd_perChar_z (realSlice u₀)).mono (subset_univ _)) hne hu
  simpa only [hcard] using he

end
end NlsGge.GK38
