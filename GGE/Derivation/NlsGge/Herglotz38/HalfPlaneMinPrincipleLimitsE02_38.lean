import NlsGge.Herglotz38.HalfPlaneMinPrincipleE02_38
import Mathlib.Topology.ExtendFrom
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations

/-! # Half-plane minimum principle stated through boundary LIMITS (campaign 38)

Version of `halfPlane_im_nonneg_of_boundary_E02_38` for a function given only on the open
upper half-plane: boundary data are limits along `𝓝[UHP] x`. -/

theorem mem_closure_upperHalfPlane_E02_38 {z : ℂ} (hz : 0 ≤ z.im) :
    z ∈ closure {w : ℂ | 0 < w.im} := by
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun m : ℕ => z + Complex.I * ((1/((m:ℝ)+1) : ℝ) : ℂ), ?_, ?_⟩
  · intro m
    show 0 < (z + Complex.I * ((1/((m:ℝ)+1) : ℝ) : ℂ)).im
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, add_zero]
    have : 0 < 1/((m:ℝ)+1) := by positivity
    linarith
  · have h : Tendsto (fun m : ℕ => ((1/((m:ℝ)+1) : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (h.const_mul Complex.I).const_add z
    simpa using h2

theorem halfPlane_im_nonneg_of_boundary_limits_E02_38 (Φ : ℂ → ℂ) (E : Finset ℝ)
    (hΦ : DifferentiableOn ℂ Φ {z | 0 < z.im})
    (hlim : ∀ x : ℝ, x ∉ E → ∃ y : ℂ, Tendsto Φ (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) (𝓝 y) ∧ 0 ≤ y.im)
    (hbdd : ∀ e ∈ E, ∃ r > 0, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖z - (e : ℂ)‖ < r → ‖Φ z‖ ≤ M)
    (hinf : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ → ‖Φ z‖ < ε) :
    ∀ z : ℂ, 0 < z.im → 0 ≤ (Φ z).im := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  set F := extendFrom U Φ with hF
  have hFU : ∀ z ∈ U, F z = Φ z := extendFrom_extends hΦc
  set E' : Set ℂ := (fun e : ℝ => (e : ℂ)) '' (E : Set ℝ)
  -- limits at every point of the closed half-plane off E
  have hlimall : ∀ x ∈ {z : ℂ | 0 ≤ z.im} \ E', ∃ y, Tendsto Φ (𝓝[U] x) (𝓝 y) := by
    rintro x ⟨hx0, hxE⟩
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ x.im from hx0) with hpos | hzero
    · refine ⟨Φ x, ?_⟩
      have := (hΦc x hpos).tendsto
      rwa [nhdsWithin_eq_nhds.mpr (hUo.mem_nhds hpos)] at this ⊢
    · have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hnot : x.re ∉ E := fun h => hxE ⟨x.re, h, hxr.symm⟩
      obtain ⟨y, hy, -⟩ := hlim x.re hnot
      exact ⟨y, by rw [hxr]; exact hy⟩
  suffices hmain : ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im by
    intro z hz; rw [← hFU z hz]; exact hmain z hz
  apply halfPlane_im_nonneg_of_boundary_E02_38 F E
  · exact hΦ.congr (fun z hz => hFU z hz)
  · exact continuousOn_extendFrom
      (fun x hx => mem_closure_upperHalfPlane_E02_38 hx.1) hlimall
  · intro e he
    obtain ⟨r, hr, M, hM⟩ := hbdd e he
    exact ⟨r, hr, M, fun z hz hzr => by rw [hFU z hz]; exact hM z hz hzr⟩
  · intro x hx
    obtain ⟨y, hy, hyim⟩ := hlim x hx
    rw [hF, extendFrom_eq (mem_closure_upperHalfPlane_E02_38 (by simp)) hy]
    exact hyim
  · intro ε hε
    obtain ⟨R, hR⟩ := hinf (ε/2) (by linarith)
    refine ⟨R + 1, ?_⟩
    intro z hz0 hzR hzE
    rcases lt_or_eq_of_le hz0 with hpos | hzero
    · rw [hFU z hpos]; exact lt_of_lt_of_le (hR z hpos (by linarith)) (by linarith)
    · obtain ⟨y, hy⟩ := hlimall z ⟨hz0, hzE⟩
      have hFz : F z = y := extendFrom_eq (mem_closure_upperHalfPlane_E02_38 hz0) hy
      rw [hFz]
      have hev : ∀ᶠ w in 𝓝[U] z, ‖Φ w‖ ≤ ε/2 := by
        have hball : U ∩ Metric.ball z 1 ∈ 𝓝[U] z :=
          inter_mem_nhdsWithin U (Metric.ball_mem_nhds z one_pos)
        filter_upwards [hball] with w hw'
        have hw : w ∈ Metric.ball z 1 ∧ w ∈ U := ⟨hw'.2, hw'.1⟩
        have hwz : ‖z‖ ≤ ‖w‖ + 1 := by
          have := norm_le_insert' z w
          have h1 : ‖z - w‖ < 1 := by rw [← dist_eq_norm, dist_comm]; exact hw.1
          linarith
        exact (hR w hw.2 (by linarith)).le
      have : (𝓝[U] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
        (mem_closure_upperHalfPlane_E02_38 hz0)
      have := le_of_tendsto hy.norm hev
      linarith

end NlsGge.SpectralFoundations
end
