import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.PairCompact
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # K1: weak sequential compactness of scalar spectral quantities.
GK Chapter I, Theorem4.1 and Lemma4.2. Weak convergence uses the accepted F6
fundamental-entry theorem; complex derivative convergence follows holomorphy.
-/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem antiDiscrim_weakContinuous38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) :
    TendstoLocallyUniformly (fun k z => antiDiscrim (φ k) z) (antiDiscrim φ₀) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [fundPair_weakContinuous_uniform38 hw hK (half_pos hε)] with k hk z hz
  rw [dist_eq_norm, norm_sub_rev]
  unfold antiDiscrim
  simp only [monodromyPair_eq_fundPair]
  have h0 := hk z hz ⟨1, zero_le_one, le_rfl⟩ 0 1
  have h1 := hk z hz ⟨1, zero_le_one, le_rfl⟩ 1 0
  calc
    _ = ‖(fundPair (φ k) z ⟨1, zero_le_one, le_rfl⟩ 0 1 -
            fundPair φ₀ z ⟨1, zero_le_one, le_rfl⟩ 0 1) +
          (fundPair (φ k) z ⟨1, zero_le_one, le_rfl⟩ 1 0 -
            fundPair φ₀ z ⟨1, zero_le_one, le_rfl⟩ 1 0)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

/-- Derivative convergence is established only after entire differentiability. -/
theorem discrimDeriv_weakContinuous38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) :
    TendstoLocallyUniformly (fun k z => deriv (discrim (φ k)) z)
      (deriv (discrim φ₀)) atTop := by
  rw [← tendstoLocallyUniformlyOn_univ]
  apply (discrim_weakContinuous hw).tendstoLocallyUniformlyOn.deriv
  · exact Filter.Eventually.of_forall (fun k z _ =>
      (analyticOnNhd_discrim_z (φ k) z (Set.mem_univ _)).differentiableAt.differentiableWithinAt)
  · exact isOpen_univ

theorem antiDiscrimDeriv_weakContinuous38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) :
    TendstoLocallyUniformly (fun k z => deriv (antiDiscrim (φ k)) z)
      (deriv (antiDiscrim φ₀)) atTop := by
  rw [← tendstoLocallyUniformlyOn_univ]
  apply (antiDiscrim_weakContinuous38 hw).tendstoLocallyUniformlyOn.deriv
  · exact Filter.Eventually.of_forall (fun k z _ =>
      (analyticOnNhd_antiDiscrim_z (φ k) z (Set.mem_univ _)).differentiableAt.differentiableWithinAt)
  · exact isOpen_univ


/-- Spectral differentiation preserves joint analyticity in the potential and parameter. -/
theorem analyticOnNhd_discrimDeriv_joint38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => deriv (discrim p.1) p.2) Set.univ := by
  let F : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  have heq (p : PotPair × ℂ) : deriv (discrim p.1) p.2 =
      fderiv ℂ F p (0, 1) := by
    have h := ((analyticOnNhd_discrim p (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp_hasDerivAt
      p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    simpa only [F, Function.comp_def, id_eq, zero_add, one_mul] using h.deriv
  intro p hp
  have h := (ContinuousLinearMap.apply ℂ ℂ ((0 : PotPair), (1 : ℂ)) :
    ((PotPair × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ).analyticAt (fderiv ℂ F p)
  have hcomp := h.comp ((analyticOnNhd_discrim p hp).fderiv)
  change AnalyticAt ℂ (fun q => fderiv ℂ F q ((0 : PotPair), (1 : ℂ))) p at hcomp
  have hfun : (fun q => fderiv ℂ F q ((0 : PotPair), (1 : ℂ))) =
      (fun q : PotPair × ℂ => deriv (discrim q.1) q.2) :=
    funext (fun q => (heq q).symm)
  rw [hfun] at hcomp
  exact hcomp

end
end NlsGge.GK38
