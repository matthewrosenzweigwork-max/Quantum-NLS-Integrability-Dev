import Mathlib

/-!
# Exponential decay of Fourier coefficients from Cauchy-type derivative bounds

Source: `paper/v2.tex`, lines 1466-1473.  Documented departure from the manuscript: the
contour shift is replaced by repeated integration by parts on `[0,1]`, using only the
derivative bounds `‖g^{(m)}‖ ≤ K m! / s^m`.  The integration by parts is carried out directly
for functions with values in a complex Banach space `E`.

Note on smoothness: in this mathlib `ContDiff ℝ ⊤` means `ContDiff ℝ ω` (analytic).  The main
theorem `fourierCoeff_norm_le_of_iteratedDeriv_infty` assumes only `∀ m : ℕ, ContDiff ℝ m`,
which is weaker (hence a stronger theorem); the literal `⊤` statement
`fourierCoeff_norm_le_of_iteratedDeriv` is an immediate corollary.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Composition

open MeasureTheory Complex Real

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Integration by parts on `[0,1]` for a differentiable function with continuous derivative
and equal values at the endpoints. -/
lemma integral_fourier_smul_deriv {g g' : ℝ → E} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') (hper : g 1 = g 0) (n : ℤ) :
    ∫ x in (0:ℝ)..1, fourier (-n) (x : AddCircle (1:ℝ)) • g' x
      = (2 * π * I * n) • ∫ x in (0:ℝ)..1, fourier (-n) (x : AddCircle (1:ℝ)) • g x := by
  set e : ℝ → ℂ := fun y => fourier (-n) (y : AddCircle (1:ℝ)) with he_def
  have hec : Continuous e :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hed : ∀ x, HasDerivAt e (-2 * π * I * n / ((1:ℝ):ℂ) * e x) x := fun x =>
    hasDerivAt_fourier_neg (1:ℝ) n x
  set c : ℂ := -2 * π * I * n / ((1:ℝ):ℂ) with hc
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hderiv : ∀ x, HasDerivAt (fun y => e y • g y) (e x • g' x + (c * e x) • g x) x :=
    fun x => ((hed x).smul (hg x)).congr_deriv (by rw [add_comm])
  have hint1 : IntervalIntegrable (fun x => e x • g' x) volume 0 1 :=
    (hec.smul hg').intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => (c * e x) • g x) volume 0 1 :=
    ((continuous_const.mul hec).smul hgc).intervalIntegrable _ _
  have hftc : ∫ x in (0:ℝ)..1, (e x • g' x + (c * e x) • g x) = e 1 • g 1 - e 0 • g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hint1.add hint2)
  have he1 : e 1 = e 0 := by
    simp only [he_def]
    have : ((1:ℝ) : AddCircle (1:ℝ)) = ((0:ℝ) : AddCircle (1:ℝ)) := by
      simp
    rw [this]
  rw [he1, hper, sub_self, intervalIntegral.integral_add hint1 hint2] at hftc
  have h3 : ∫ x in (0:ℝ)..1, (c * e x) • g x = c • ∫ x in (0:ℝ)..1, e x • g x := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [mul_smul]
  rw [h3] at hftc
  have hc' : c = -(2 * π * I * n) := by
    simp only [hc]; push_cast; ring
  rw [hc', neg_smul] at hftc
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact hftc)

omit [CompleteSpace E] in
/-- If `g : ℝ → E` has period `1`, so does its derivative. -/
lemma deriv_periodic_one {g : ℝ → E} (h : ∀ x, g (x + 1) = g x) (x : ℝ) :
    deriv g (x + 1) = deriv g x := by
  have : g = fun y => g (y + 1) := funext fun y => (h y).symm
  conv_rhs => rw [this]
  exact (deriv_comp_add_const (f := g) 1 x).symm

omit [CompleteSpace E] in
/-- Iterated derivatives of a `1`-periodic function are `1`-periodic. -/
lemma iteratedDeriv_periodic_one {g : ℝ → E} (h : ∀ x, g (x + 1) = g x) (m : ℕ) (x : ℝ) :
    iteratedDeriv m g (x + 1) = iteratedDeriv m g x := by
  induction m generalizing x with
  | zero => simpa using h x
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact deriv_periodic_one ih x

/-- Fourier coefficient of the `m`-th derivative: `a_m = (2πin)^m a_0`, in interval-integral
form, for a smooth `1`-periodic function. -/
lemma integral_fourier_smul_iteratedDeriv {g : ℝ → E} (hg : ∀ m : ℕ, ContDiff ℝ m g)
    (h : ∀ x, g (x + 1) = g x) (n : ℤ) (m : ℕ) :
    ∫ x in (0:ℝ)..1, fourier (-n) (x : AddCircle (1:ℝ)) • iteratedDeriv m g x
      = (2 * π * I * n) ^ m • ∫ x in (0:ℝ)..1, fourier (-n) (x : AddCircle (1:ℝ)) • g x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : ∀ x, HasDerivAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g x) x := fun x => by
      rw [iteratedDeriv_succ]
      exact ((hg (m + 1)).differentiable_iteratedDeriv m (by exact_mod_cast Nat.lt_succ_self m)
        x).hasDerivAt
    have hper : iteratedDeriv m g 1 = iteratedDeriv m g 0 := by
      simpa using iteratedDeriv_periodic_one h m 0
    rw [integral_fourier_smul_deriv hd ((hg (m + 1)).continuous_iteratedDeriv (m + 1) le_rfl)
      hper n, ih, smul_smul, pow_succ, mul_comm]

/-- Main estimate, with `C^∞` smoothness (`∀ m : ℕ, ContDiff ℝ m`). -/
theorem fourierCoeff_norm_le_of_iteratedDeriv_infty
    (U : AddCircle (1:ℝ) → E) (hU : ∀ m : ℕ, ContDiff ℝ m (fun x : ℝ => U x))
    {K s : ℝ} (hs : 0 < s)
    (hK : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m (fun x : ℝ => U x) x‖ ≤ K * m.factorial / s ^ m)
    (n : ℤ) :
    ‖fourierCoeff U n‖ ≤ 2 * K * Real.exp (-(Real.pi * s) * |(n:ℝ)|) := by
  set g : ℝ → E := fun x : ℝ => U x with hg_def
  have hper : ∀ x, g (x + 1) = g x := fun x => by
    simp only [hg_def]
    have : ((x + 1 : ℝ) : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) :=
      AddCircle.coe_add_period (1:ℝ) x
    rw [this]
  set A : ℝ := ‖fourierCoeff U n‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hcoeff : fourierCoeff U n
      = ∫ x in (0:ℝ)..1, fourier (-n) (x : AddCircle (1:ℝ)) • g x := by
    rw [fourierCoeff_eq_intervalIntegral U n 0]
    simp [hg_def]
  -- bound on the m-th derivative's Fourier integral
  have hm : ∀ m : ℕ, (2 * π * |(n:ℝ)|) ^ m * A ≤ K * m.factorial / s ^ m := by
    intro m
    have h1 := integral_fourier_smul_iteratedDeriv hU hper n m
    have h2 : ‖∫ x in (0:ℝ)..1, fourier (-n) (x : AddCircle (1:ℝ)) • iteratedDeriv m g x‖
        ≤ K * m.factorial / s ^ m * |(1:ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      exact hK m x
    rw [h1, norm_smul, ← hcoeff, norm_pow] at h2
    have : ‖(2 * π * I * n : ℂ)‖ = 2 * π * |(n:ℝ)| := by
      simp [abs_of_pos Real.pi_pos]
    rw [this] at h2
    simpa using h2
  set x : ℝ := π * s * |(n:ℝ)| with hx
  have hterm : ∀ m : ℕ, A * (x ^ m / m.factorial) ≤ K * (1 / 2 : ℝ) ^ m := by
    intro m
    have hfac : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hsm : (0:ℝ) < s ^ m := pow_pos hs m
    have h := hm m
    rw [le_div_iff₀ hsm] at h
    have e1 : A * (x ^ m / m.factorial) * (2 ^ m * m.factorial)
        = ((2 * π * |(n:ℝ)|) ^ m * A) * s ^ m := by
      simp only [hx]; field_simp; ring
    have e2 : K * (1 / 2 : ℝ) ^ m * (2 ^ m * m.factorial) = K * m.factorial := by
      have : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
      calc K * (1 / 2 : ℝ) ^ m * (2 ^ m * m.factorial)
          = K * ((1 / 2 : ℝ) ^ m * 2 ^ m) * m.factorial := by ring
        _ = K * m.factorial := by rw [this]; ring
    have h2m : (0:ℝ) < 2 ^ m * m.factorial := by positivity
    refine le_of_mul_le_mul_right ?_ h2m
    rw [e1, e2]
    exact h
  have hsum1 : HasSum (fun m : ℕ => A * (x ^ m / m.factorial)) (A * Real.exp x) := by
    have := (NormedSpace.expSeries_div_hasSum_exp x).mul_left A
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hsum2 : HasSum (fun m : ℕ => K * (1 / 2 : ℝ) ^ m) (K * 2) :=
    hasSum_geometric_two.mul_left K
  have hle : A * Real.exp x ≤ K * 2 := hasSum_le hterm hsum1 hsum2
  have hexp : Real.exp (-(Real.pi * s) * |(n:ℝ)|) = (Real.exp x)⁻¹ := by
    rw [← Real.exp_neg]; congr 1; simp only [hx]; ring
  rw [hexp, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos x)]
  nlinarith

/-- Literal form of the requested target (`ContDiff ℝ ⊤`, which is `ContDiff ℝ ω` here). -/
theorem fourierCoeff_norm_le_of_iteratedDeriv
    (U : AddCircle (1:ℝ) → E) (hU : ContDiff ℝ ⊤ (fun x : ℝ => U x))
    {K s : ℝ} (hs : 0 < s)
    (hK : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m (fun x : ℝ => U x) x‖ ≤ K * m.factorial / s ^ m)
    (n : ℤ) :
    ‖fourierCoeff U n‖ ≤ 2 * K * Real.exp (-(Real.pi * s) * |(n:ℝ)|) :=
  fourierCoeff_norm_le_of_iteratedDeriv_infty U (fun _ => hU.of_le le_top) hs hK n

end

end NlsGge.Composition
