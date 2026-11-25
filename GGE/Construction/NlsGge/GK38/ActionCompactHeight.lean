import NlsGge.GK38.EigenvalueCompactnessHeight
import NlsGge.GK38.DirichletRealWeakTransport

/-! # A4 real helper: uniform height convergence under actual weak L2 convergence

GK I.13, Proposition 13.2 real-integral prerequisite. Compact-open
postcomposition packages continuity on the compact spectral range, including
height zero. The source complex-contour identification remains an A2 obligation.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

/-- F6, followed by continuous compact-open postcomposition and restriction. -/
theorem gapHeight_uniform_weak38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (A B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ Icc A B,
      |actualGapHeightE02_38 (u k) x - actualGapHeightE02_38 u₀ x| < ε := by
  let D (v : PhysicalL2) : C(ℂ, ℂ) :=
    ⟨discrim (realSlice v), analyticOnNhd_discrim_z (realSlice v) |>.continuous⟩
  have hd : Tendsto (fun k => D (u k)) atTop (𝓝 (D u₀)) :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
      (discrim_weakContinuous (weakLim_realSlice38 hw))
  let H : C(ℂ, ℝ) := ⟨fun z => Real.arcosh (max 1 ‖z / 2‖),
    Real.continuousOn_arcosh.comp_continuous
      (continuous_const.max ((continuous_id.div_const (2 : ℂ)).norm))
      (fun _ => mem_Ici.mpr (le_max_left _ _))⟩
  let : CompactSpace (Icc A B) := isCompact_iff_compactSpace.mp isCompact_Icc
  let R : C(Icc A B, ℂ) :=
    ⟨fun x => (x.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have hh := ((ContinuousMap.continuous_precomp R).tendsto (H.comp (D u₀))).comp
    (((ContinuousMap.continuous_postcomp H).tendsto (D u₀)).comp hd)
  have he : ∀ᶠ k in atTop,
      dist ((H.comp (D (u k))).comp R) ((H.comp (D u₀)).comp R) < ε :=
    hh.eventually (ball_mem_nhds _ hε)
  filter_upwards [he] with k hk x hx
  have hp := (ContinuousMap.dist_apply_le_dist
    (f := (H.comp (D (u k))).comp R) (g := (H.comp (D u₀)).comp R) ⟨x, hx⟩).trans_lt hk
  have ht (v : PhysicalL2) : discrim (realSlice v) (x : ℂ) / 2 =
      actualPhysicalUnitHalfTrace32 v (x : ℂ) := by rw [discrim_realSlice]; ring
  simpa only [ContinuousMap.comp_apply, H, D, R, ContinuousMap.coe_mk,
    ht, Real.dist_eq, actualGapHeightE02_38] using hp

end
end NlsGge.GK38
