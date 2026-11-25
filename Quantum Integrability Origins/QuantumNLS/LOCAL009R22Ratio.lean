import QuantumNLS.LOCAL009R22Inverse

/-! Uniform bounds and Lipschitz control of the source correction f_z/f'_z.
These are bounds on the original scalar exponential map, not assumptions on
the reconstructed occupation expression. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Complex Set Metric
namespace QuantumNLS.LOCAL009R22Ratio
open QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Inverse

def ratio (κ L : ℝ) (z w : ℂ) : ℂ :=
  spectralMap κ L z w / spectralDerivative κ L z w

def ratioBound (κ R : ℝ) : ℝ := (9 * Real.exp (κ * R)) / (3 * κ / 8)
def ratioLipschitz (κ R : ℝ) : ℝ := 1 + κ^2 * (ratioBound κ R)^2

theorem derivative_lower {κ L R : ℝ} (hκ : 0 < κ)
    (hradius : κ * R ≤ 1 / 1000) {z w : ℂ}
    (hexp : ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    (hw : w ∈ closedBall (0 : ℂ) R) :
    3 * κ / 8 ≤ ‖spectralDerivative κ L z w‖ := by
  have hquarter := local009_quarter_from_source hκ hradius hexp hgap hw
  have hl := spectralDerivative_lower κ L hquarter
  have hn : κ / 2 ≤ ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm, abs_of_pos hκ]
    nlinarith
  linarith

theorem ratio_norm_le {κ L R : ℝ} (hκ : 0 < κ)
    (hradius : κ * R ≤ 1 / 1000) {z w : ℂ}
    (hexp : ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    (hw : w ∈ closedBall (0 : ℂ) R) :
    ‖ratio κ L z w‖ ≤ ratioBound κ R := by
  have hnum := spectralMap_norm_le hκ.le (mem_closedBall_zero_iff.mp hw)
    (by norm_num : (0 : ℝ) ≤ 8) hexp
  have hden := derivative_lower hκ hradius hexp hgap hw
  simp only [show (1 + 8 : ℝ) = 9 by norm_num] at hnum
  unfold ratio ratioBound
  rw [norm_div]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

theorem ratio_hasDerivAt {κ L R : ℝ} (hκ : 0 < κ)
    (hradius : κ * R ≤ 1 / 1000) {z w : ℂ}
    (hexp : ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    (hw : w ∈ closedBall (0 : ℂ) R) :
    HasDerivAt (ratio κ L z) (1 + (κ : ℂ)^2 * (ratio κ L z w)^2) w := by
  have hl := derivative_lower hκ hradius hexp hgap hw
  have hn : spectralDerivative κ L z w ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hd := (spectralMap_hasDerivAt κ L z w).div
    (spectralDerivative_hasDerivAt κ L z w) hn
  convert hd using 1
  · ext u
    rfl
  · unfold ratio
    field_simp [hn]
    ring

theorem ratio_derivative_bound {κ L R : ℝ} (hκ : 0 < κ)
    (hradius : κ * R ≤ 1 / 1000) {z w : ℂ}
    (hexp : ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    (hw : w ∈ closedBall (0 : ℂ) R) :
    ‖deriv (ratio κ L z) w‖ ≤ ratioLipschitz κ R := by
  rw [(ratio_hasDerivAt hκ hradius hexp hgap hw).deriv]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(κ : ℂ)^2 * (ratio κ L z w)^2‖ := norm_add_le _ _
    _ = 1 + κ^2 * ‖ratio κ L z w‖^2 := by
      simp only [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ ratioLipschitz κ R := by
      unfold ratioLipschitz
      gcongr
      exact ratio_norm_le hκ hradius hexp hgap hw

theorem ratio_sub_bound {κ L R : ℝ} (hκ : 0 < κ)
    (hradius : κ * R ≤ 1 / 1000) {z w v : ℂ}
    (hexp : ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    (hw : w ∈ closedBall (0 : ℂ) R) (hv : v ∈ closedBall (0 : ℂ) R) :
    ‖ratio κ L z w - ratio κ L z v‖ ≤ ratioLipschitz κ R * ‖w-v‖ := by
  exact (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (ratio_hasDerivAt hκ hradius hexp hgap hu).differentiableAt)
    (fun u hu => ratio_derivative_bound hκ hradius hexp hgap hu) hv hw

end QuantumNLS.LOCAL009R22Ratio
#print axioms QuantumNLS.LOCAL009R22Ratio.derivative_lower
#print axioms QuantumNLS.LOCAL009R22Ratio.ratio_norm_le
#print axioms QuantumNLS.LOCAL009R22Ratio.ratio_hasDerivAt
#print axioms QuantumNLS.LOCAL009R22Ratio.ratio_derivative_bound
#print axioms QuantumNLS.LOCAL009R22Ratio.ratio_sub_bound
