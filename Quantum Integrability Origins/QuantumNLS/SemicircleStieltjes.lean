import Mathlib
import QuantumNLS.SemicircleODE
import QuantumNLS.CauchyUniqueness

/-!
# The semicircle law and its Stieltjes transform (quadratic equation)

Source use: `ROOT_spectral_measure.tex`, `prop:root-free`, plane-wave clause: the density `√(4κ/L − t²)₊/(2πκ/L)` (here `a = κ/L`, `w(t)=√(4a−t²)`) is a probability measure whose
Cauchy transform `h(z) = ∫ (z−t)⁻¹ dσ(t)` satisfies `a h² − z h + 1 = 0` for `Im z > 0` (the printed "analytic root of `(κ/L)g² − (z−p)g + 1 = 0`"), proved from
`SemicircleODE.ode_S` without contour integration.

* `M0_eq`: `∫ w = 2π a`;  `scMeasure a` (density `w/(2πa)` on `[-b,b]`) is a probability measure (`scMeasure_univ`);
* `cauchy_scMeasure`: `cauchyTransform (scMeasure a) z = S a z/(2πa)`;
* `norm_hh_le`: `‖h(z)‖ ≤ 1/Im z`;  `ode_hh`: `(z²−4a) h'(z) = z h(z) − 2`;
* `quadratic_hh`: `a h(z)² − z h(z) + 1 = 0` for `Im z > 0` (the function `Q/(z²−4a)` has zero derivative on the upper half plane and vanishes along the imaginary axis).
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

namespace QuantumNLS.SemicircleStieltjes

open QuantumNLS.SemicircleODE
open QuantumNLS.CauchyUniqueness (cauchyTransform)

theorem bnd_pos {a : ℝ} (ha : 0 < a) : 0 < bnd a := by
  unfold bnd; have := Real.sqrt_pos.2 ha; positivity

/-- `∫ w = 2π a`. -/
theorem M0_eq {a : ℝ} (ha : 0 < a) : M0 a = 2 * π * a := by
  have hb := bnd_pos ha
  have hb2 := bnd_sq ha.le
  unfold M0
  have h1 : ∫ x in (-1 : ℝ)..1, w a (bnd a * x) = (bnd a)⁻¹ • ∫ x in (bnd a * -1)..(bnd a * 1), w a x :=
    intervalIntegral.integral_comp_mul_left (w a) hb.ne'
  have h2 : ∀ x : ℝ, w a (bnd a * x) = bnd a * √(1 - x ^ 2 : ℝ) := by
    intro x
    unfold w
    have : 4 * a - (bnd a * x) ^ 2 = bnd a ^ 2 * (1 - x ^ 2) := by rw [mul_pow, hb2]; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le]
  simp_rw [h2] at h1
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq] at h1
  rw [mul_neg_one, mul_one] at h1
  have h3 : ∫ x in (-bnd a)..(bnd a), w a x = bnd a * (bnd a * (π / 2)) := by
    calc ∫ x in (-bnd a)..(bnd a), w a x = bnd a * ((bnd a)⁻¹ • ∫ x in (-bnd a)..(bnd a), w a x) := by
          rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
      _ = bnd a * (bnd a * (π / 2)) := by rw [← h1]
  have e : bnd a * (bnd a * (π / 2)) = bnd a ^ 2 * (π / 2) := by ring
  rw [h3, e, hb2]; ring

/-- The semicircle law: density `w/(2πa)` on `(-b, b]`. -/
def scMeasure (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (-bnd a) (bnd a))).withDensity (fun t => ENNReal.ofReal (w a t / (2 * π * a)))

theorem measurable_dens (a : ℝ) : Measurable (fun t : ℝ => ENNReal.ofReal (w a t / (2 * π * a))) :=
  (((continuous_w a).measurable).div_const _).ennreal_ofReal

theorem scMeasure_univ {a : ℝ} (ha : 0 < a) : scMeasure a univ = 1 := by
  have hb := bnd_pos ha
  have hle : -bnd a ≤ bnd a := by linarith
  unfold scMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hle, intervalIntegral.integral_div, ← M0, M0_eq ha]
    have : (2 * π * a) / (2 * π * a) = 1 := div_self (by positivity)
    simp [this]
  · exact (((continuous_w a).div_const _).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact Eventually.of_forall fun t => div_nonneg (w_nonneg a t) (by positivity)

theorem isProb_sc {a : ℝ} (ha : 0 < a) : IsProbabilityMeasure (scMeasure a) := ⟨scMeasure_univ ha⟩

theorem cauchy_scMeasure {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    cauchyTransform (scMeasure a) z = S a z / ((2 * π * a : ℝ) : ℂ) := by
  have hb := bnd_pos ha
  have hle : -bnd a ≤ bnd a := by linarith
  unfold cauchyTransform scMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_dens a) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ t : ℝ, (ENNReal.ofReal (w a t / (2 * π * a))).toReal • (z - (t : ℂ))⁻¹ =
      ((2 * π * a : ℝ) : ℂ)⁻¹ * (((w a t : ℝ) : ℂ) / (z - (t : ℂ))) := by
    intro t
    rw [ENNReal.toReal_ofReal (div_nonneg (w_nonneg a t) (by positivity)), Complex.real_smul]
    push_cast
    field_simp
  simp_rw [e]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hle]
  unfold S
  rw [div_eq_inv_mul]

/-- The normalized transform `h = S/(2πa)`. -/
def hh (a : ℝ) (z : ℂ) : ℂ := S a z / ((2 * π * a : ℝ) : ℂ)

theorem norm_hh_le {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) : ‖hh a z‖ ≤ (z.im)⁻¹ := by
  haveI := isProb_sc ha
  have : hh a z = cauchyTransform (scMeasure a) z := (cauchy_scMeasure ha hz).symm
  rw [this]
  unfold cauchyTransform
  have := norm_integral_le_of_norm_le_const (μ := scMeasure a) (f := fun t : ℝ => (z - (t : ℂ))⁻¹)
    (C := (z.im)⁻¹) (Eventually.of_forall fun t => norm_inv_sub_le hz t)
  simpa using this

theorem hasDerivAt_hh {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (hh a) ((-∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) /
      ((2 * π * a : ℝ) : ℂ)) z :=
  (hasDerivAt_S ha.le hz).div_const _

theorem ode_hh {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    (z ^ 2 - 4 * a) * ((-∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) /
      ((2 * π * a : ℝ) : ℂ)) = z * hh a z - 2 := by
  have h := ode_S ha hz
  have hM : ((2 * π * a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π * a : ℝ) ≠ 0)
  have hM0 : (M0 a : ℂ) = ((2 * π * a : ℝ) : ℂ) := by rw [M0_eq ha]
  rw [hM0] at h
  unfold hh
  field_simp
  linear_combination h

theorem sq_ne {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) : z ^ 2 - 4 * (a : ℂ) ≠ 0 := by
  have hb := bnd_sq ha.le
  have e : z ^ 2 - 4 * (a : ℂ) = (z - (bnd a : ℂ)) * (z + (bnd a : ℂ)) := by
    have : (4 * a : ℂ) = ((bnd a : ℝ) : ℂ) ^ 2 := by exact_mod_cast hb.symm
    rw [this]; ring
  rw [e]
  refine mul_ne_zero ?_ ?_ <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;> linarith

/-- **The quadratic equation**: `a h(z)² − z h(z) + 1 = 0` for `Im z > 0`. -/
theorem quadratic_hh {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    (a : ℂ) * hh a z ^ 2 - z * hh a z + 1 = 0 := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : Convex ℝ U := by
    intro x hx y hy s t hs ht hst
    simp only [hU, mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with h | h
    · subst h; have : t = 1 := by linarith
      subst this; simpa using hy
    · nlinarith
  let Q : ℂ → ℂ := fun z => (a : ℂ) * hh a z ^ 2 - z * hh a z + 1
  let T : ℂ → ℂ := fun z => Q z / (z ^ 2 - 4 * a)
  let d : ℂ → ℂ := fun z => (-∫ t in (-bnd a)..(bnd a), ((w a t : ℝ) : ℂ) / (z - (t : ℂ)) ^ 2) /
      ((2 * π * a : ℝ) : ℂ)
  have hT : ∀ z ∈ U, HasDerivAt T 0 z := by
    intro z hz'
    have hz'' : 0 < z.im := hz'
    have hd := hasDerivAt_hh ha hz''
    have hQ : HasDerivAt Q (2 * (a : ℂ) * hh a z * d z - (hh a z + z * d z)) z := by
      have h1 := ((hd.pow 2).const_mul (a : ℂ))
      have h2 := ((hasDerivAt_id z).mul hd)
      have := (h1.sub h2).add_const 1
      convert this using 1
      all_goals first
        | (show 2 * (a : ℂ) * hh a z * d z - (hh a z + z * d z) =
            (a : ℂ) * (((2 : ℕ) : ℂ) * hh a z ^ (2 - 1) * d z) - (1 * hh a z + z * d z)
           norm_num
           try ring)
        | (funext x
           simp only [Q, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id]
           try ring)
    have hden : HasDerivAt (fun z : ℂ => z ^ 2 - 4 * (a : ℂ)) (2 * z) z := by
      have := (hasDerivAt_pow 2 z).sub_const (4 * (a : ℂ))
      simpa using this
    have := hQ.div hden (sq_ne ha hz'')
    have hode := ode_hh ha hz''
    have hD := sq_ne ha hz''
    convert this using 1
    have hode' : (z ^ 2 - 4 * (a : ℂ)) * d z = z * hh a z - 2 := hode
    have hN : (2 * (a : ℂ) * hh a z * d z - (hh a z + z * d z)) * (z ^ 2 - 4 * (a : ℂ)) - Q z * (2 * z) = 0 := by
      simp only [Q]
      linear_combination (2 * (a : ℂ) * hh a z - z) * hode'
    rw [hN]; simp
  have hdiff : DifferentiableOn ℂ T U := fun z hz' => (hT z hz').differentiableAt.differentiableWithinAt
  have hconst : ∀ y ∈ U, T y = T Complex.I := by
    intro y hy
    exact hUo.is_const_of_deriv_eq_zero hUc.isPreconnected hdiff (fun x hx => (hT x hx).deriv) hy
      (by simp [hU])
  set C := T Complex.I with hC
  -- boundedness along the imaginary axis forces `C = 0`
  have hbound : ∀ y : ℝ, 1 ≤ y → ‖C‖ * y ^ 2 ≤ a + 2 := by
    intro y hy
    have hyU : Complex.I * (y : ℂ) ∈ U := by simp [hU]; linarith
    have hyim : (Complex.I * (y : ℂ)).im = y := by simp
    have hT' := hconst _ hyU
    have hz2 : (Complex.I * (y : ℂ)) ^ 2 - 4 * (a : ℂ) = -((y ^ 2 + 4 * a : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hhb := norm_hh_le ha (show 0 < (Complex.I * (y : ℂ)).im by rw [hyim]; linarith)
    rw [hyim] at hhb
    have hQb : ‖Q (Complex.I * (y : ℂ))‖ ≤ a + 2 := by
      simp only [Q]
      have b1 : ‖(a : ℂ) * hh a (Complex.I * (y : ℂ)) ^ 2‖ ≤ a * (y⁻¹) ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
        gcongr
      have b2 : ‖(Complex.I * (y : ℂ)) * hh a (Complex.I * (y : ℂ))‖ ≤ 1 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        calc y * ‖hh a (Complex.I * (y : ℂ))‖ ≤ y * y⁻¹ := by gcongr
          _ = 1 := by field_simp
      have b3 : a * (y⁻¹) ^ 2 ≤ a := by
        have : (y⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hy)
        nlinarith
      calc _ ≤ ‖(a : ℂ) * hh a (Complex.I * (y : ℂ)) ^ 2‖ + ‖(Complex.I * (y : ℂ)) * hh a (Complex.I * (y : ℂ))‖ + ‖(1 : ℂ)‖ := by
            refine (norm_add_le _ _).trans ?_
            exact add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ a + 1 + 1 := by rw [norm_one]; linarith
        _ = a + 2 := by ring
    have hTv : T (Complex.I * (y : ℂ)) = Q (Complex.I * (y : ℂ)) / (-((y ^ 2 + 4 * a : ℝ) : ℂ)) := by
      simp only [T]; rw [hz2]
    rw [hTv] at hT'
    have hpos : (0 : ℝ) < y ^ 2 + 4 * a := by positivity
    have hn : ‖Q (Complex.I * (y : ℂ))‖ = ‖C‖ * (y ^ 2 + 4 * a) := by
      have : Q (Complex.I * (y : ℂ)) = C * (-((y ^ 2 + 4 * a : ℝ) : ℂ)) := by
        rw [← hT', div_mul_cancel₀]
        rw [neg_ne_zero]; exact_mod_cast hpos.ne'
      rw [this, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hn] at hQb
    nlinarith [norm_nonneg C]
  have hC0 : C = 0 := by
    by_contra hne
    have hCp : 0 < ‖C‖ := norm_pos_iff.2 hne
    set y : ℝ := Real.sqrt (2 * (a + 2) / ‖C‖ + 1) with hy
    have hy1 : 1 ≤ y := by
      rw [hy]; apply Real.one_le_sqrt.2; have : 0 ≤ 2 * (a + 2) / ‖C‖ := by positivity
      linarith
    have hy2 : y ^ 2 = 2 * (a + 2) / ‖C‖ + 1 := by rw [hy, Real.sq_sqrt (by positivity)]
    have := hbound y hy1
    rw [hy2, mul_add, mul_div_cancel₀ _ hCp.ne'] at this
    nlinarith
  have hTz := hconst z hz
  rw [hC0] at hTz
  have hD := sq_ne ha hz
  have : Q z = 0 := by
    have h2 : Q z / (z ^ 2 - 4 * a) = 0 := hTz
    rcases div_eq_zero_iff.1 h2 with h | h
    · exact h
    · exact absurd h hD
  exact this

end QuantumNLS.SemicircleStieltjes

#print axioms QuantumNLS.SemicircleStieltjes.M0_eq
#print axioms QuantumNLS.SemicircleStieltjes.scMeasure_univ
#print axioms QuantumNLS.SemicircleStieltjes.cauchy_scMeasure
#print axioms QuantumNLS.SemicircleStieltjes.norm_hh_le
#print axioms QuantumNLS.SemicircleStieltjes.quadratic_hh
