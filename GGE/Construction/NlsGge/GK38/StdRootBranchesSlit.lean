import NlsGge.GK38.StdRootBranchesScalar

/-! Full complex slit geometry and infinity normalization of the standard branch.
The proof uses the real segment's symmetric squared characterization. -/

set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem stdRoot_slit38 (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    (a + b) / 2 - z ≠ 0 ∧
      1 - (((b - a)^2) / 4) / (((a + b) / 2 - z)^2) ∈ Complex.slitPlane := by
  have hw := stdRoot_midpoint_ne38 hz
  refine ⟨hw, ?_⟩
  let w : ℂ := (a + b) / 2 - z
  let rad : ℂ := 1 - (((b - a)^2) / 4) / w^2
  change rad ∈ Complex.slitPlane
  by_contra hcut
  rw [Complex.mem_slitPlane_iff] at hcut
  push Not at hcut
  have hr : rad = (rad.re : ℂ) := by
    apply Complex.ext <;> simp [hcut.2]
  let d : ℝ := 1 - rad.re
  have hd : 1 ≤ d := by dsimp [d]; linarith [hcut.1]
  have hdp : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hrform : rad * w^2 = w^2 - (b - a)^2 / 4 := by
    dsimp [rad]
    field_simp [show w ≠ 0 from hw]
  have he : (b - a)^2 / 4 = w^2 * (d : ℂ) := by
    rw [hr] at hrform
    dsimp [d]
    push_cast
    linear_combination hrform
  let t : ℝ := (Real.sqrt d)⁻¹
  have hsq : (Real.sqrt d)^2 = d := Real.sq_sqrt hdp.le
  have hs1 : 1 ≤ Real.sqrt d := by nlinarith [Real.sqrt_nonneg d]
  have ht0 : 0 ≤ t := inv_nonneg.mpr (Real.sqrt_nonneg d)
  have ht1 : t ≤ 1 := by
    simpa [t] using inv_anti₀ (by norm_num : 0 < (1 : ℝ)) hs1
  have htd : t^2 * d = 1 := by
    dsimp [t]
    rw [inv_pow, hsq, inv_mul_cancel₀ hdp.ne']
  have htc : (t : ℂ)^2 * (d : ℂ) = 1 := by exact_mod_cast htd
  apply hz
  apply (segment_symmetric_iff38 a b z).mpr
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  calc
    (z - (a + b) / 2)^2 = w^2 := by dsimp [w]; ring
    _ = (t : ℂ)^2 * (w^2 * (d : ℂ)) := by linear_combination -w^2 * htc
    _ = (t : ℂ)^2 * (b - a)^2 / 4 := by rw [← he]; ring

/-- The normalization approaches the linear prefactor at infinity, with an
explicit inverse-square error. It is not the principal root of the product. -/
theorem stdRoot_ratio_bound38 {τ g2 z : ℂ} (h : τ - z ≠ 0) :
    ‖stdRoot38 τ g2 z / (τ - z) - 1‖ ≤ ‖g2‖ / (4 * ‖τ - z‖^2) := by
  have he : stdRoot38 τ g2 z / (τ - z) - 1 =
      Complex.sqrt (1 - (g2 / 4) / (τ - z)^2) - 1 := by
    rw [stdRoot38, mul_comm (τ - z), mul_div_cancel_right₀ _ h]
  rw [he]
  calc
    _ ≤ ‖(g2 / 4) / (τ - z)^2‖ :=
      Lib.norm_sqrt_one_sub_sub_one_le ((g2 / 4) / (τ - z)^2)
    _ = ‖g2‖ / (4 * ‖τ - z‖^2) := by
      rw [norm_div, norm_div, norm_pow, Complex.norm_ofNat, div_div]

theorem stdRoot_analyticAt38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {τ g2 z : E → ℂ} {x : E} (hτ : AnalyticAt ℂ τ x) (hg : AnalyticAt ℂ g2 x)
    (hz : AnalyticAt ℂ z x) (hne : τ x - z x ≠ 0)
    (hslit : 1 - (g2 x / 4) / (τ x - z x)^2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun y => stdRoot38 (τ y) (g2 y) (z y)) x := by
  have hw := hτ.sub hz
  have hr : AnalyticAt ℂ (fun y => 1 - (g2 y / 4) / (τ y - z y)^2) x :=
    analyticAt_const.sub ((hg.div_const (c := (4 : ℂ))).div (hw.pow 2)
      (pow_ne_zero 2 hne))
  exact hw.mul (hr.cpow analyticAt_const hslit)

end
end NlsGge.GK38
