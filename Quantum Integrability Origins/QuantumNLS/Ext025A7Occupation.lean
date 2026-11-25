import QuantumNLS.Ext025A7Joint
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The GP-03 application wrapper for LOCAL-009, in the source's original
(unscaled) spectral and target coordinates and with the exact disk margins. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A7

def spectralInverse (κ L R : ℝ) (z y : ℂ) : ℂ :=
  diskInverse κ L R z ((y - spectralMap κ L z 0) / spectralLinear κ L z)

theorem spectral_target_margin (κ L : ℝ) {z y : ℂ} {R : ℝ}
    (hD : spectralLinear κ L z ≠ 0)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    (y - spectralMap κ L z 0) / spectralLinear κ L z ∈ ball (0 : ℂ) (3 / 4 * R) := by
  rw [mem_ball, dist_zero_right, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hD)]
  nlinarith

/-- The source's original disk is filled with a unique preimage in the open
source disk; the selected inverse is jointly analytic in (z,y). The bounds
on the original derivative, not inverse maps or derivatives, are premises. -/
theorem local009_spectral_inverse (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    spectralInverse κ L R z y ∈ ball (0 : ℂ) R ∧
      spectralMap κ L z (spectralInverse κ L R z y) = y ∧
      (∀ v ∈ closedBall (0 : ℂ) R, spectralMap κ L z v = y →
        v = spectralInverse κ L R z y) ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => spectralInverse κ L R p.1 p.2) (z, y) := by
  let t := (y - spectralMap κ L z 0) / spectralLinear κ L z
  have ht := spectral_target_margin κ L (hD z hz) hy
  obtain ⟨hw, he, hu, han⟩ := local009_normalized_inverse κ L hR hU hD hb z hz t ht
  have heq : spectralMap κ L z (spectralInverse κ L R z y) = y := by
    change (spectralMap κ L z (spectralInverse κ L R z y) - spectralMap κ L z 0) /
      spectralLinear κ L z = (y - spectralMap κ L z 0) / spectralLinear κ L z at he
    exact sub_left_injective ((div_left_inj' (hD z hz)).mp he)
  refine ⟨hw, heq, ?_, ?_⟩
  · intro v hv hv'
    apply hu v hv
    simp only [normalizedSpectral, hv', t]
  · have hfzero : AnalyticAt ℂ (fun p : ℂ × ℂ => spectralMap κ L p.1 0) (z, y) :=
      (spectralMap_analyticAt κ L (z, (0 : ℂ))).comp (x := (z, y)) (f := fun p : ℂ × ℂ => (p.1, (0 : ℂ)))
        (analyticAt_fst.prod analyticAt_const)
    have hphase : AnalyticAt ℂ
        (fun p : ℂ × ℂ => Complex.exp (Complex.I * p.1 * L)) (z, y) :=
      ((analyticAt_const.mul analyticAt_fst).mul analyticAt_const).cexp
    have hlin : AnalyticAt ℂ (fun p : ℂ × ℂ => spectralLinear κ L p.1) (z, y) :=
      analyticAt_const.mul (analyticAt_const.sub hphase)
    have hcoord : AnalyticAt ℂ (fun p : ℂ × ℂ =>
        (p.2 - spectralMap κ L p.1 0) / spectralLinear κ L p.1) (z, y) :=
      (analyticAt_snd.sub hfzero).div hlin (hD z hz)
    exact han.comp (f := fun p : ℂ × ℂ =>
      (p.1, (p.2 - spectralMap κ L p.1 0) / spectralLinear κ L p.1))
      (analyticAt_fst.prod hcoord)

/-- The first inverse derivative is derived from the constructed right
inverse on the entire source target disk, rather than assumed. -/
theorem local009_inverse_hasDerivAt (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    HasDerivAt (spectralInverse κ L R z)
      (spectralDerivative κ L z (spectralInverse κ L R z y))⁻¹ y := by
  obtain ⟨hw, _, _, han⟩ := local009_spectral_inverse κ L hR hU hD hb hz hy
  have ha : AnalyticAt ℂ (spectralInverse κ L R z) y :=
    han.comp (f := fun v : ℂ => (z, v)) (analyticAt_const.prod analyticAt_id)
  have hr : ∀ᶠ v in 𝓝 y, spectralMap κ L z (spectralInverse κ L R z v) = v := by
    have hnear : ∀ᶠ v in 𝓝 y,
        ‖v - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
    exact hnear.mono fun v hv => (local009_spectral_inverse κ L hR hU hD hb hz hv).2.1
  exact HasDerivAt.of_local_left_inverse ha.continuousAt
    (spectralMap_hasDerivAt κ L z _)
    (spectralDerivative_nonzero κ L (hD z hz) (hb z hz _ (ball_subset_closedBall hw))) hr
end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.spectralInverse
#print axioms QuantumNLS.Ext025A7.spectral_target_margin
#print axioms QuantumNLS.Ext025A7.local009_spectral_inverse
#print axioms QuantumNLS.Ext025A7.local009_inverse_hasDerivAt
