import QuantumNLS.Ext025A7Occupation

/-! The source inverse's first and second scalar derivatives, with uniform
norm bounds derived from the original derivative estimates. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A7

theorem spectralDerivative_lower (κ L : ℝ) {z w : ℂ}
    (hb : ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
      ‖spectralLinear κ L z‖ / 4) :
    3 / 4 * ‖spectralLinear κ L z‖ ≤ ‖spectralDerivative κ L z w‖ := by
  have ht : ‖spectralLinear κ L z‖ ≤ ‖spectralDerivative κ L z w‖ +
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ := by
    calc
      ‖spectralLinear κ L z‖ = ‖spectralDerivative κ L z w -
        (spectralDerivative κ L z w - spectralLinear κ L z)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  linarith

theorem local009_inverse_derivative_bound (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    ‖deriv (spectralInverse κ L R z) y‖ ≤ (3 / 4 * ‖spectralLinear κ L z‖)⁻¹ := by
  have hw := (local009_spectral_inverse κ L hR hU hD hb hz hy).1
  rw [(local009_inverse_hasDerivAt κ L hR hU hD hb hz hy).deriv, norm_inv]
  have hpos : 0 < ‖spectralLinear κ L z‖ := norm_pos_iff.mpr (hD z hz)
  exact inv_anti₀ (by positivity : 0 < 3 / 4 * ‖spectralLinear κ L z‖)
    (spectralDerivative_lower κ L (hb z hz _ (ball_subset_closedBall hw)))

/-- The second derivative of the literal source map, without an assumed
Taylor coefficient or derivative of the inverse. -/
theorem spectralDerivative_hasDerivAt (κ L : ℝ) (z w : ℂ) :
    HasDerivAt (spectralDerivative κ L z)
      (-((κ : ℂ) ^ 2) * spectralMap κ L z w) w := by
  unfold spectralDerivative spectralMap
  convert ((((hasDerivAt_id w).const_mul (Complex.I * κ)).cexp).const_mul
    (Complex.I * κ)).add
    (((((hasDerivAt_id w).const_mul (-Complex.I * κ)).cexp).const_mul
      (-Complex.I * κ)).const_mul (Complex.exp (Complex.I * z * L))) using 1
  · rfl
  · simp only [id_eq]
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- The second inverse derivative follows by differentiating the proved
first inverse derivative on the common target disk. -/
theorem local009_inverse_second (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    HasDerivAt (deriv (spectralInverse κ L R z))
      ((κ : ℂ)^2 * y / (spectralDerivative κ L z (spectralInverse κ L R z y))^3) y := by
  have hw := (local009_spectral_inverse κ L hR hU hD hb hz hy).1
  have he := (local009_spectral_inverse κ L hR hU hD hb hz hy).2.1
  have hn := spectralDerivative_nonzero κ L (hD z hz) (hb z hz _ (ball_subset_closedBall hw))
  have hg := local009_inverse_hasDerivAt κ L hR hU hD hb hz hy
  have hd := ((spectralDerivative_hasDerivAt κ L z _).comp y hg).inv hn
  have hevent : deriv (spectralInverse κ L R z) =ᶠ[𝓝 y]
      (fun v => (spectralDerivative κ L z (spectralInverse κ L R z v))⁻¹) := by
    have hnear : ∀ᶠ v in 𝓝 y,
        ‖v - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
    exact hnear.mono fun v hv => (local009_inverse_hasDerivAt κ L hR hU hD hb hz hv).deriv
  apply (hd.congr_of_eventuallyEq hevent).congr_deriv
  simp only [Function.comp_apply]
  rw [he]
  field_simp [hn]

/-- The common second derivative norm bound retains the source target
value explicitly; source exponential bounds can replace it uniformly. -/
theorem local009_inverse_second_bound (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    ‖deriv (deriv (spectralInverse κ L R z)) y‖ ≤
      |κ|^2 * ‖y‖ / (3 / 4 * ‖spectralLinear κ L z‖)^3 := by
  have hw := (local009_spectral_inverse κ L hR hU hD hb hz hy).1
  have hl := spectralDerivative_lower κ L (hb z hz _ (ball_subset_closedBall hw))
  have hpos : 0 < ‖spectralLinear κ L z‖ := norm_pos_iff.mpr (hD z hz)
  rw [(local009_inverse_second κ L hR hU hD hb hz hy).deriv,
    norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  gcongr
end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.spectralDerivative_lower
#print axioms QuantumNLS.Ext025A7.local009_inverse_derivative_bound
#print axioms QuantumNLS.Ext025A7.spectralDerivative_hasDerivAt
#print axioms QuantumNLS.Ext025A7.local009_inverse_second
#print axioms QuantumNLS.Ext025A7.local009_inverse_second_bound
