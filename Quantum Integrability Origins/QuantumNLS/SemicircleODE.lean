import Mathlib

/-!
# The Stieltjes transform of the semicircle weight satisfies a quadratic equation

Source use: `ROOT_spectral_measure.tex`, `prop:root-free`, plane-wave clause ("its Stieltjes transform is the analytic root of `(κ/L)g² − (z−p)g + 1 = 0` ...;
the elementary substitution evaluates that root").  Here (centered case `p = 0`, parameter `a = κ/L > 0`, weight `w(t) = √(4a − t²)`, support `[-b, b]`, `b = 2√a`),
for `S(z) = ∫_{-b}^{b} w(t)/(z−t) dt`, `M₀ = ∫ w` and `h = S/M₀` (`Im z > 0`) we prove, with no contour integration and no branch of a square root:

* `ode_S`: `(z² − 4a) S'(z) = z S(z) − 2 M₀` (differentiation under the integral sign and one integration by parts of `d/dt[w³/(z−t)]`);
* `quadratic_h`: `a h(z)² − z h(z) + 1 = 0` for `Im z > 0` (`Q = a h² − z h + 1` satisfies `(z²−4a)Q' = 2zQ`, hence `Q/(z²−4a)` is constant on the upper half-plane,
  and boundedness of `Q` on the imaginary axis forces the constant to vanish).
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace QuantumNLS.SemicircleODE

/-- `w(t) = √(4a − t²)`. -/
def w (a t : ℝ) : ℝ := Real.sqrt (4 * a - t ^ 2)

/-- `b = 2√a`. -/
def bnd (a : ℝ) : ℝ := 2 * Real.sqrt a

theorem bnd_sq {a : ℝ} (ha : 0 ≤ a) : bnd a ^ 2 = 4 * a := by
  unfold bnd; rw [mul_pow, Real.sq_sqrt ha]; ring

theorem bnd_nonneg (a : ℝ) : 0 ≤ bnd a := by unfold bnd; positivity

theorem w_nonneg (a t : ℝ) : 0 ≤ w a t := Real.sqrt_nonneg _

theorem continuous_w (a : ℝ) : Continuous (w a) := by
  unfold w; fun_prop

theorem w_sq {a t : ℝ} (ht : t ∈ Icc (-bnd a) (bnd a)) (ha : 0 ≤ a) : w a t ^ 2 = 4 * a - t ^ 2 := by
  unfold w
  rw [Real.sq_sqrt]
  have := bnd_sq ha
  nlinarith [ht.1, ht.2, bnd_nonneg a]

theorem w_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : w a t ≤ bnd a := by
  unfold w bnd
  have : Real.sqrt (4 * a - t ^ 2) ≤ Real.sqrt (4 * a) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  have e : Real.sqrt (4 * a) = 2 * Real.sqrt a := by
    rw [show (4 : ℝ) * a = 2 ^ 2 * a by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  linarith

theorem w_bnd {a : ℝ} (ha : 0 ≤ a) : w a (bnd a) = 0 := by
  unfold w
  rw [Real.sqrt_eq_zero']
  have := bnd_sq ha; nlinarith

theorem w_neg_bnd {a : ℝ} (ha : 0 ≤ a) : w a (-bnd a) = 0 := by
  unfold w
  rw [neg_sq]
  exact w_bnd ha

theorem w_pos {a t : ℝ} (ha : 0 < a) (ht : t ∈ Ioo (-bnd a) (bnd a)) : 0 < w a t := by
  unfold w
  apply Real.sqrt_pos.2
  have := bnd_sq ha.le
  nlinarith [ht.1, ht.2, bnd_nonneg a]

theorem norm_inv_sub_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) : ‖(z - (t : ℂ))⁻¹‖ ≤ (z.im)⁻¹ := by
  rw [norm_inv]
  have hzq : z.im ≤ ‖z - (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  exact inv_anti₀ hz hzq

theorem sub_ne_zero' {z : ℂ} (hz : 0 < z.im) (t : ℝ) : z - (t : ℂ) ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp at this; linarith

/-- `S(z) = ∫_{-b}^{b} w(t)/(z − t) dt`. -/
def S (a : ℝ) (z : ℂ) : ℂ := ∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ))

/-- `M₀ = ∫ w`. -/
def M0 (a : ℝ) : ℝ := ∫ t in (-bnd a)..(bnd a), w a t

theorem continuous_integrand1 (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun t : ℝ => ((w a t : ℝ) : ℂ) / (z - (t : ℂ))) :=
  Continuous.div (Complex.continuous_ofReal.comp (continuous_w a)) (by fun_prop) (sub_ne_zero' hz)

theorem continuous_integrand2 (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun t : ℝ => ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) :=
  Continuous.div (Complex.continuous_ofReal.comp (continuous_w a)) (by fun_prop)
    (fun t => pow_ne_zero 2 (sub_ne_zero' hz t))

/-- Differentiability of `S` under the integral sign. -/
theorem hasDerivAt_S {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (S a) (-∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) z := by
  have hb := bnd_nonneg a
  have hle : -bnd a ≤ bnd a := by linarith
  have hε : 0 < z.im / 2 := by positivity
  have hball : ∀ z' ∈ Metric.ball z (z.im / 2), z.im / 2 ≤ z'.im := by
    intro z' hz'
    rw [Metric.mem_ball] at hz'
    have h1 := Complex.abs_im_le_norm (z' - z)
    simp only [Complex.sub_im] at h1
    rw [dist_eq_norm] at hz'
    have := (neg_abs_le (z'.im - z.im)).trans (le_trans (le_abs_self _) h1)
    linarith [abs_le.1 (h1.trans hz'.le)]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc (-bnd a) (bnd a)))
    (F := fun (z' : ℂ) (t : ℝ) => ((w a t : ℝ) : ℂ) / (z' - (t : ℂ)))
    (F' := fun (z' : ℂ) (t : ℝ) => -(((w a t : ℝ) : ℂ) / (z' - (t : ℂ)) ^ 2))
    (x₀ := z) (bound := fun _ => bnd a * ((z.im / 2)⁻¹) ^ 2) (Metric.ball_mem_nhds z hε)
    ?_ ?_ ?_ ?_ ?_ ?_
  · have e : S a = fun z' => ∫ t, ((w a t : ℝ) : ℂ) / (z' - (t : ℂ)) ∂(volume.restrict (Ioc (-bnd a) (bnd a))) := by
      funext z'; unfold S; rw [intervalIntegral.integral_of_le hle]
    rw [e]
    have e2 : (-∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) =
        ∫ t, -(((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) ∂(volume.restrict (Ioc (-bnd a) (bnd a))) := by
      rw [intervalIntegral.integral_of_le hle, integral_neg]
    rw [e2]
    exact key.2
  · have hpos : ∀ᶠ z' in 𝓝 z, 0 < z'.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
    filter_upwards [hpos] with z' hz'
    exact (continuous_integrand1 a hz').aestronglyMeasurable
  · exact (continuous_integrand1 a hz).integrableOn_Ioc
  · exact (continuous_integrand2 a hz).neg.aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    intro z' hz'
    have hzp : 0 < z'.im := lt_of_lt_of_le hε (hball z' hz')
    rw [norm_neg, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (w_nonneg a t)]
    have hn : z.im / 2 ≤ ‖z' - (t : ℂ)‖ := by
      have h0 := Complex.abs_im_le_norm (z' - (t : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h0
      exact (hball z' hz').trans ((le_abs_self _).trans h0)
    have hhalf : 0 < z.im / 2 := hε
    calc w a t / ‖z' - (t : ℂ)‖ ^ 2 ≤ bnd a / ‖z' - (t : ℂ)‖ ^ 2 := by
          gcongr; exact w_le ha t
      _ ≤ bnd a / (z.im / 2) ^ 2 := by gcongr
      _ = bnd a * ((z.im / 2)⁻¹) ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  · exact integrable_const _
  · refine Eventually.of_forall fun t => ?_
    intro z' hz'
    have hzp : 0 < z'.im := lt_of_lt_of_le hε (hball z' hz')
    have h1 : HasDerivAt (fun y : ℂ => y - (t : ℂ)) 1 z' := (hasDerivAt_id z').sub_const _
    have h2 := (h1.inv (sub_ne_zero' hzp t)).const_mul ((w a t : ℝ) : ℂ)
    convert h2 using 1
    · funext y; simp [div_eq_mul_inv]
    · field_simp

/-! ### The ODE for `S` -/

theorem ode_S {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    (z ^ 2 - 4 * a) * (-∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) =
      z * S a z - 2 * (M0 a : ℂ) := by
  have hb := bnd_nonneg a
  have hle : -bnd a ≤ bnd a := by linarith
  have ha0 := ha.le
  -- the function whose derivative integrates to zero
  let φ : ℝ → ℂ := fun t => (((w a t) ^ 3 : ℝ) : ℂ) / (z - (t : ℂ))
  let φ' : ℝ → ℂ := fun t => ((-(3 * t * w a t) : ℝ) : ℂ) / (z - (t : ℂ)) +
    (((w a t) ^ 3 : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2
  have hφc : Continuous φ := by
    refine Continuous.div (Complex.continuous_ofReal.comp ((continuous_w a).pow 3)) (by fun_prop)
      (sub_ne_zero' hz)
  have hφ'c : Continuous φ' := by
    refine Continuous.add ?_ ?_
    · exact Continuous.div (Complex.continuous_ofReal.comp (by have := continuous_w a; fun_prop)) (by fun_prop)
        (sub_ne_zero' hz)
    · exact Continuous.div (Complex.continuous_ofReal.comp ((continuous_w a).pow 3)) (by fun_prop)
        (fun t => pow_ne_zero 2 (sub_ne_zero' hz t))
  have hderiv : ∀ x ∈ Ioo (-bnd a) (bnd a), HasDerivWithinAt φ (φ' x) (Ioi x) x := by
    intro x hx
    have hwpos : 0 < w a x := w_pos ha hx
    have hf : HasDerivAt (fun t : ℝ => 4 * a - t ^ 2) (-(2 * x)) x := by
      have := ((hasDerivAt_pow 2 x).const_sub (4 * a))
      simpa using this
    have hsq : HasDerivAt (w a) (-(2 * x) / (2 * Real.sqrt (4 * a - x ^ 2))) x := by
      unfold w; exact hf.sqrt (ne_of_gt (by unfold w at hwpos; exact Real.sqrt_pos.1 hwpos))
    have hcube : HasDerivAt (fun t : ℝ => (w a t) ^ 3) (-(3 * x * w a x)) x := by
      have := hsq.pow 3
      convert this using 1
      unfold w
      have hne : Real.sqrt (4 * a - x ^ 2) ≠ 0 := ne_of_gt (by unfold w at hwpos; exact hwpos)
      field_simp
      ring
    have hnum : HasDerivAt (fun t : ℝ => (((w a t) ^ 3 : ℝ) : ℂ)) ((-(3 * x * w a x) : ℝ) : ℂ) x :=
      hcube.ofReal_comp
    have hden : HasDerivAt (fun t : ℝ => z - (t : ℂ)) (-1) x := by
      have h := (hasDerivAt_const x z).sub (HasDerivAt.ofReal_comp (hasDerivAt_id x))
      exact h.congr_deriv (by simp)
    have := (hnum.div hden (sub_ne_zero' hz x))
    refine HasDerivAt.hasDerivWithinAt ?_
    convert this using 1
    simp only [φ']
    field_simp
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hle hφc.continuousOn hderiv
    (hφ'c.intervalIntegrable _ _)
  have hφb : φ (bnd a) = 0 := by simp [φ, w_bnd ha0]
  have hφnb : φ (-bnd a) = 0 := by simp [φ, w_neg_bnd ha0]
  rw [hφb, hφnb, sub_zero] at hint
  -- pointwise reduction
  have hpt : ∀ t ∈ uIcc (-bnd a) (bnd a), φ' t = ((w a t : ℝ) : ℂ) * ((4 * (a : ℂ) - z ^ 2) / (z - (t : ℂ)) ^ 2 -
      z / (z - (t : ℂ)) + 2) := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    have hws := w_sq ht ha0
    have hD := sub_ne_zero' hz t
    have hW : (((w a t : ℝ) : ℂ)) ^ 2 = 4 * (a : ℂ) - (t : ℂ) ^ 2 := by exact_mod_cast hws
    simp only [φ']
    push_cast
    field_simp
    linear_combination (((w a t : ℝ) : ℂ) * (z - (t : ℂ))) ^ 0 * (((w a t : ℝ) : ℂ)) * hW
  rw [intervalIntegral.integral_congr hpt] at hint
  have i1 : IntervalIntegrable (fun t : ℝ => ((w a t : ℝ) : ℂ) * ((4 * (a : ℂ) - z ^ 2) / (z - (t : ℂ)) ^ 2)) volume
      (-bnd a) (bnd a) := by
    refine Continuous.intervalIntegrable ?_ _ _
    refine Continuous.mul (Complex.continuous_ofReal.comp (continuous_w a)) ?_
    exact Continuous.div continuous_const (by fun_prop) (fun t => pow_ne_zero 2 (sub_ne_zero' hz t))
  have i2 : IntervalIntegrable (fun t : ℝ => ((w a t : ℝ) : ℂ) * (z / (z - (t : ℂ)))) volume (-bnd a) (bnd a) := by
    refine Continuous.intervalIntegrable ?_ _ _
    refine Continuous.mul (Complex.continuous_ofReal.comp (continuous_w a)) ?_
    exact Continuous.div continuous_const (by fun_prop) (sub_ne_zero' hz)
  have i3 : IntervalIntegrable (fun t : ℝ => ((w a t : ℝ) : ℂ) * 2) volume (-bnd a) (bnd a) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (Complex.continuous_ofReal.comp (continuous_w a)).mul continuous_const
  have e1 : ∀ t : ℝ, ((w a t : ℝ) : ℂ) * ((4 * (a : ℂ) - z ^ 2) / (z - (t : ℂ)) ^ 2 - z / (z - (t : ℂ)) + 2) =
      ((w a t : ℝ) : ℂ) * ((4 * (a : ℂ) - z ^ 2) / (z - (t : ℂ)) ^ 2) -
        ((w a t : ℝ) : ℂ) * (z / (z - (t : ℂ))) + ((w a t : ℝ) : ℂ) * 2 := fun t => by ring
  simp_rw [e1] at hint
  rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2] at hint
  have c1 : ∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) * ((4 * (a : ℂ) - z ^ 2) / (z - (t : ℂ)) ^ 2) =
      (4 * (a : ℂ) - z ^ 2) * ∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have c2 : ∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) * (z / (z - (t : ℂ))) = z * S a z := by
    unfold S
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have c3 : ∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) * 2 = 2 * (M0 a : ℂ) := by
    unfold M0
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [c1, c2, c3] at hint
  linear_combination hint

end QuantumNLS.SemicircleODE

#print axioms QuantumNLS.SemicircleODE.hasDerivAt_S
#print axioms QuantumNLS.SemicircleODE.ode_S
