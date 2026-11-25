import QuantumNLS.BetheFiniteNAction
import QuantumNLS.BethePhysicalTransfer
import QuantumNLS.HighMomentsFinal
import QuantumNLS.ProductPreparation

/-!
# R-FFA8D3F2 `lem:root-placement`, part 1: the sharp kernel bound `‖K_{r,z}‖ ≤ 2 (Im z)^{-r}`
(`ROOT_spectral_measure.tex:54–80`)

Following the printed proof: the alternating-simplex kernels `K̃^±_{r,z}` have row and column integrals at most
`η^{-r}` (`η = Im z > 0`), the Schur test gives `‖K̃^±‖ ≤ η^{-r}`, and `K_{r,z} = P_r(K̃⁺+K̃⁻)P_r` is a
compression.  Everything is proved internally (EXT-025 is discharged by internal proof): the Schur test for
the frozen bounded integral operators (`schur_form_le`, `norm_operator_le_schur`), the one-dimensional
exponential integrals, Fubini on the product cube (mathlib `integral_fintype_prod_volume_eq_prod`), and
the chamber box decompositions of the frozen `BetheFiniteNAction` (`plusOrder_box`, `minusOrder_box`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace BigOperators

noncomputable section

namespace QuantumNLS.RootPlacementBound

open QuantumNLS.BetheIntegralOperator QuantumNLS.BetheTransferKernelAdjoint
  QuantumNLS.BetheTransferOperators QuantumNLS.BetheWeakGradient QuantumNLS.BetheWavefunctions
  QuantumNLS.BetheFiniteNAction

/-! ### The Schur test for bounded integral operators -/

section Schur

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_norm_sq (f : H μ) : Integrable (fun x => ‖f x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

theorem integral_norm_sq_eq (f : H μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) f f
  have e1 : ⟪f, f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have e2 : ∀ a : X, inner ℂ (f a : ℂ) (f a : ℂ) = ((‖f a‖ ^ 2 : ℝ) : ℂ) := fun a => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [e2] at h
  rw [integral_complex_ofReal, e1] at h
  exact_mod_cast h.symm

/-- **Schur test (weak form)**: if the row and column integrals of `|k|` are at most `a`, then
`|⟨f, T g⟩| ≤ (a/2)(‖f‖² + ‖g‖²)`. -/
theorem schur_form_le (k : Kernel μ) (a : ℝ) (hrow : ∀ x, ∫ y, ‖k.fn (x, y)‖ ∂μ ≤ a)
    (hcol : ∀ y, ∫ x, ‖k.fn (x, y)‖ ∂μ ≤ a) (f g : H μ) :
    ‖k.form f g‖ ≤ (a / 2) * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have hkm : Measurable fun p : X × X => ‖k.fn p‖ := k.measurable.norm
  have hf2 := integrable_norm_sq f
  have hg2 := integrable_norm_sq g
  have hone : Integrable (fun _ : X => (1 : ℝ)) μ := integrable_const 1
  have A1 : Integrable (fun p : X × X => ‖k.fn p‖ * ‖f p.1‖ ^ 2) (μ.prod μ) := by
    have hb := (hf2.mul_prod hone).const_mul k.bound
    refine hb.mono' (hkm.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_fst.norm.pow 2)) ?_
    filter_upwards with p
    simp only [norm_mul, norm_norm, norm_pow, mul_one]
    exact mul_le_mul_of_nonneg_right (k.norm_le p) (by positivity)
  have A2 : Integrable (fun p : X × X => ‖k.fn p‖ * ‖g p.2‖ ^ 2) (μ.prod μ) := by
    have hb := (hone.mul_prod hg2).const_mul k.bound
    refine hb.mono' (hkm.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable g).comp_snd.norm.pow 2)) ?_
    filter_upwards with p
    simp only [norm_mul, norm_norm, norm_pow, one_mul]
    exact mul_le_mul_of_nonneg_right (k.norm_le p) (by positivity)
  have I1 : ∫ p, ‖k.fn p‖ * ‖f p.1‖ ^ 2 ∂(μ.prod μ) ≤ a * ‖f‖ ^ 2 := by
    rw [integral_prod _ A1]
    have hin : ∀ x, ∫ y, ‖k.fn (x, y)‖ * ‖f x‖ ^ 2 ∂μ ≤ a * ‖f x‖ ^ 2 := fun x => by
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (hrow x) (by positivity)
    calc ∫ x, ∫ y, ‖k.fn (x, y)‖ * ‖f x‖ ^ 2 ∂μ ∂μ ≤ ∫ x, a * ‖f x‖ ^ 2 ∂μ :=
          integral_mono A1.integral_prod_left (hf2.const_mul a) hin
      _ = a * ‖f‖ ^ 2 := by rw [integral_const_mul, integral_norm_sq_eq]
  have I2 : ∫ p, ‖k.fn p‖ * ‖g p.2‖ ^ 2 ∂(μ.prod μ) ≤ a * ‖g‖ ^ 2 := by
    rw [integral_prod_symm _ A2]
    have hin : ∀ y, ∫ x, ‖k.fn (x, y)‖ * ‖g y‖ ^ 2 ∂μ ≤ a * ‖g y‖ ^ 2 := fun y => by
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (hcol y) (by positivity)
    calc ∫ y, ∫ x, ‖k.fn (x, y)‖ * ‖g y‖ ^ 2 ∂μ ∂μ ≤ ∫ y, a * ‖g y‖ ^ 2 ∂μ :=
          integral_mono A2.integral_prod_right (hg2.const_mul a) hin
      _ = a * ‖g‖ ^ 2 := by rw [integral_const_mul, integral_norm_sq_eq]
  have hG : Integrable (fun p : X × X => (1 / 2 : ℝ) *
      (‖k.fn p‖ * ‖f p.1‖ ^ 2 + ‖k.fn p‖ * ‖g p.2‖ ^ 2)) (μ.prod μ) :=
    (A1.add A2).const_mul _
  calc ‖k.form f g‖ ≤ ∫ p, (1 / 2 : ℝ) * (‖k.fn p‖ * ‖f p.1‖ ^ 2 + ‖k.fn p‖ * ‖g p.2‖ ^ 2)
        ∂(μ.prod μ) := by
        apply norm_integral_le_of_norm_le hG
        filter_upwards with p
        simp only [Kernel.integrand, norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖f p.1‖ - ‖g p.2‖), norm_nonneg (k.fn p), norm_nonneg (f p.1),
          norm_nonneg (g p.2), mul_nonneg (norm_nonneg (k.fn p)) (sq_nonneg (‖f p.1‖ - ‖g p.2‖))]
    _ = (1 / 2 : ℝ) * (∫ p, ‖k.fn p‖ * ‖f p.1‖ ^ 2 ∂(μ.prod μ) +
          ∫ p, ‖k.fn p‖ * ‖g p.2‖ ^ 2 ∂(μ.prod μ)) := by
        rw [integral_const_mul, integral_add A1 A2]
    _ ≤ (a / 2) * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by linarith

/-- **Schur test**: `‖T‖ ≤ a` when all row and column integrals of `|k|` are at most `a`. -/
theorem norm_operator_le_schur (k : Kernel μ) (a : ℝ) (ha : 0 ≤ a)
    (hrow : ∀ x, ∫ y, ‖k.fn (x, y)‖ ∂μ ≤ a)
    (hcol : ∀ y, ∫ x, ‖k.fn (x, y)‖ ∂μ ≤ a) : ‖k.operator‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro g
  by_cases hz : k.operator g = 0
  · rw [hz, norm_zero]; positivity
  · have hp : 0 < ‖k.operator g‖ := norm_pos_iff.mpr hz
    have hg : g ≠ 0 := fun h => hz (by rw [h, map_zero])
    have hgp : 0 < ‖g‖ := norm_pos_iff.mpr hg
    set T : ℝ := ‖k.operator g‖ with hT
    set G : ℝ := ‖g‖ with hG
    set s : ℝ := G / T with hs
    have hsT : s * T = G := by rw [hs]; field_simp
    have hb := schur_form_le k a hrow hcol ((s : ℂ) • k.operator g) g
    have hform : k.form ((s : ℂ) • k.operator g) g = ((s * T ^ 2 : ℝ) : ℂ) := by
      rw [← Kernel.inner_operator, inner_smul_left, Complex.conj_ofReal,
        inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    have hs0 : 0 ≤ s := div_nonneg hgp.le hp.le
    rw [hform, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_smul,
      Complex.norm_real, Real.norm_of_nonneg hs0] at hb
    have e1 : s * T ^ 2 = G * T := by rw [← hsT]; ring
    have e2 : (s * T) ^ 2 = G ^ 2 := by rw [hsT]
    nlinarith [e1, e2, hb]

end Schur

/-! ### One-dimensional exponential integrals -/

section OneD

/-- Right-anchored exponential weight `e^{-η(c-t)}`. -/
def wR (η c t : ℝ) : ℝ := Real.exp (-η * (c - t))

/-- Left-anchored exponential weight `e^{-η(t-c)}`. -/
def wL (η c t : ℝ) : ℝ := Real.exp (-η * (t - c))

theorem continuous_wR (η c : ℝ) : Continuous (wR η c) := by unfold wR; fun_prop
theorem continuous_wL (η c : ℝ) : Continuous (wL η c) := by unfold wL; fun_prop
theorem wR_nonneg (η c t : ℝ) : 0 ≤ wR η c t := (Real.exp_pos _).le
theorem wL_nonneg (η c t : ℝ) : 0 ≤ wL η c t := (Real.exp_pos _).le

theorem integral_indicator_wR (η a b : ℝ) (hη : 0 < η) :
    ∫ t, (Ioo a b).indicator (wR η b) t ≤ 1 / η := by
  by_cases hab : a < b
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le]
    have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Real.exp (-η * (b - t)) / η)
        (wR η b t) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => -η * (b - t)) η t := by
        have := ((hasDerivAt_id t).const_sub b).const_mul (-η)
        simpa using this
      have h2 := (h1.exp).div_const η
      convert h2 using 1
      unfold wR
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_wR η b).intervalIntegrable a b)]
    have : Real.exp (-η * (b - a)) / η > 0 := div_pos (Real.exp_pos _) hη
    simp only [sub_self, mul_zero, Real.exp_zero]
    linarith
  · rw [Ioo_eq_empty hab]
    simp only [indicator_empty, integral_zero]
    positivity

theorem integral_indicator_wL (η a b : ℝ) (hη : 0 < η) :
    ∫ t, (Ioo a b).indicator (wL η a) t ≤ 1 / η := by
  by_cases hab : a < b
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le]
    have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => -Real.exp (-η * (t - a)) / η)
        (wL η a t) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => -η * (t - a)) (-η) t := by
        have := ((hasDerivAt_id t).sub_const a).const_mul (-η)
        simpa using this
      have h2 := ((h1.exp).neg).div_const η
      convert h2 using 1
      unfold wL
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_wL η a).intervalIntegrable a b)]
    have : Real.exp (-η * (b - a)) / η > 0 := div_pos (Real.exp_pos _) hη
    simp only [sub_self, mul_zero, Real.exp_zero]
    have e : -Real.exp (-η * (b - a)) / η - -1 / η = 1 / η - Real.exp (-η * (b - a)) / η := by
      ring
    rw [e]
    linarith
  · rw [Ioo_eq_empty hab]
    simp only [indicator_empty, integral_zero]
    positivity

/-- Fubini on the product cube: the integral of a product of box-localized weights. -/
theorem integral_box_prod {m : ℕ} (η : ℝ) (hη : 0 < η) (a b : Fin m → ℝ) (w : Fin m → ℝ → ℝ)
    (hwc : ∀ i, Continuous (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (hw : ∀ i, ∫ t, (Ioo (a i) (b i)).indicator (w i) t ≤ 1 / η) :
    ∫ y : Fin m → ℝ, ∏ i, (Ioo (a i) (b i)).indicator (w i) (y i) ≤ (1 / η) ^ m := by
  rw [integral_fintype_prod_volume_eq_prod (fun i => (Ioo (a i) (b i)).indicator (w i))]
  calc ∏ i, ∫ t, (Ioo (a i) (b i)).indicator (w i) t ≤ ∏ _i : Fin m, (1 / η) :=
        Finset.prod_le_prod₀ (fun i _ => integral_nonneg (fun t => indicator_nonneg
          (fun s _ => hw0 i s) t)) (fun i _ => hw i)
    _ = (1 / η) ^ m := by simp

theorem integrable_box_prod {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℝ → ℝ)
    (hwc : ∀ i, Continuous (w i)) :
    Integrable (fun y : Fin m → ℝ => ∏ i, (Ioo (a i) (b i)).indicator (w i) (y i)) volume := by
  have hi : ∀ i, Integrable ((Ioo (a i) (b i)).indicator (w i)) volume := fun i =>
    ((hwc i).integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  have := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure ℝ)) hi
  simpa [volume_pi] using this

end OneD

/-! ### Row and column integrals of the alternating-simplex kernels -/

section Kernels

variable {m : ℕ}

theorem norm_exp_I_mul (z : ℂ) (t : ℝ) : ‖Complex.exp (Complex.I * z * t)‖ = Real.exp (-z.im * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem norm_rawPlus_eq {L : ℝ} (z : ℂ) {x y : Fin m → ℝ} (h : PlusOrder L x y) :
    ‖rawPlus L z x y‖ = ∏ i, Real.exp (-z.im * (x i - y i)) := by
  classical
  unfold rawPlus
  rw [if_pos h, norm_exp_I_mul, displacement, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

theorem norm_rawMinus_eq {L : ℝ} (z : ℂ) {x y : Fin m → ℝ} (h : MinusOrder L x y) :
    ‖rawMinus L z x y‖ = Real.exp (-z.im * (L - ∑ j, (y j - x j))) := by
  classical
  unfold rawMinus
  rw [if_pos h]
  have : Complex.I * z * (L : ℂ) - Complex.I * z * ((∑ j, (y j - x j) : ℝ) : ℂ) =
      Complex.I * z * ((L - ∑ j, (y j - x j) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_exp_I_mul]

/-- Row bound for `K̃⁺`: `‖K̃⁺(x,y)‖ ≤ ∏ 1_{(lower_i, x_i)}(y_i) e^{-η(x_i-y_i)}`. -/
theorem rawPlus_row_le (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) :
    ‖rawPlus L z x y‖ ≤ ∏ i, (Ioo (lower x i) (x i)).indicator (wR z.im (x i)) (y i) := by
  classical
  have hnn : 0 ≤ ∏ i, (Ioo (lower x i) (x i)).indicator (wR z.im (x i)) (y i) :=
    Finset.prod_nonneg (fun i _ => indicator_nonneg (fun s _ => wR_nonneg _ _ _) _)
  by_cases hx : x ∈ chamber m L
  · by_cases h : PlusOrder L x y
    · rw [norm_rawPlus_eq z h]
      refine le_of_eq (Finset.prod_congr rfl (fun i _ => ?_))
      rw [indicator_of_mem ((plusOrder_box hx y).mp h i)]
      rfl
    · simp only [rawPlus, if_neg h, norm_zero]; exact hnn
  · rw [rawPlus_zero_off_chamber hx y z, norm_zero]; exact hnn

/-- Column bound for `K̃⁺` (fixed `y`, variable `x`). -/
theorem rawPlus_col_le (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) :
    ‖rawPlus L z x y‖ ≤ ∏ i, (Ioo (y i) (upper L y i)).indicator (wL z.im (y i)) (x i) := by
  classical
  have hnn : 0 ≤ ∏ i, (Ioo (y i) (upper L y i)).indicator (wL z.im (y i)) (x i) :=
    Finset.prod_nonneg (fun i _ => indicator_nonneg (fun s _ => wL_nonneg _ _ _) _)
  by_cases h : PlusOrder L x y
  · have hy : y ∈ chamber m L := minusOrder_output_chamber (L := L) (x := y) (y := x) h
    rw [norm_rawPlus_eq z h]
    have hb := (minusOrder_box hy x).mp h
    refine le_of_eq (Finset.prod_congr rfl (fun i _ => ?_))
    rw [indicator_of_mem (hb i)]
    unfold wL
    congr 1
  · simp only [rawPlus, if_neg h, norm_zero]; exact hnn

theorem sum_upper {n : ℕ} (L : ℝ) (x : Fin (n + 1) → ℝ) :
    ∑ i, upper L x i = L + ∑ j : Fin n, x j.castSucc := by
  rw [Fin.sum_univ_succ]
  have h0 : upper L x 0 = L := by simp [upper]
  rw [h0]
  congr 1 <;> simp [upper]

theorem sum_lower {n : ℕ} (y : Fin (n + 1) → ℝ) :
    ∑ i, lower y i = ∑ j : Fin n, y j.succ := by
  rw [Fin.sum_univ_castSucc]
  have hl : lower y (Fin.last n) = 0 := by simp [lower]
  rw [hl, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold lower
  rw [dif_pos (by simp)]
  congr 1

/-- Row bound for `K̃⁻` (`m = n+1`). -/
theorem rawMinus_row_le {n : ℕ} (L : ℝ) (z : ℂ) (hη : 0 ≤ z.im) (x y : Fin (n + 1) → ℝ) :
    ‖rawMinus L z x y‖ ≤
      ∏ i, (Ioo (x i) (upper L x i)).indicator (wR z.im (upper L x i)) (y i) := by
  classical
  have hnn : 0 ≤ ∏ i, (Ioo (x i) (upper L x i)).indicator (wR z.im (upper L x i)) (y i) :=
    Finset.prod_nonneg (fun i _ => indicator_nonneg (fun s _ => wR_nonneg _ _ _) _)
  by_cases h : MinusOrder L x y
  · have hx : x ∈ chamber (n + 1) L := minusOrder_output_chamber h
    have hb := (minusOrder_box hx y).mp h
    rw [norm_rawMinus_eq z h]
    have hp : ∏ i, (Ioo (x i) (upper L x i)).indicator (wR z.im (upper L x i)) (y i) =
        Real.exp (-z.im * ∑ i, (upper L x i - y i)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [indicator_of_mem (hb i)]
      rfl
    rw [hp]
    apply Real.exp_le_exp.mpr
    have hs : ∑ i, (upper L x i - y i) + x (Fin.last n) = L - ∑ j, (y j - x j) := by
      simp only [Finset.sum_sub_distrib]
      rw [sum_upper, Fin.sum_univ_castSucc x]
      ring
    have hlast : 0 < x (Fin.last n) := (hx.2 _).1
    nlinarith [mul_nonneg hη hlast.le]
  · simp only [rawMinus, if_neg h, norm_zero]; exact hnn

/-- Column bound for `K̃⁻` (`m = n+1`). -/
theorem rawMinus_col_le {n : ℕ} (L : ℝ) (z : ℂ) (hη : 0 ≤ z.im) (x y : Fin (n + 1) → ℝ) :
    ‖rawMinus L z x y‖ ≤
      ∏ i, (Ioo (lower y i) (y i)).indicator (wL z.im (lower y i)) (x i) := by
  classical
  have hnn : 0 ≤ ∏ i, (Ioo (lower y i) (y i)).indicator (wL z.im (lower y i)) (x i) :=
    Finset.prod_nonneg (fun i _ => indicator_nonneg (fun s _ => wL_nonneg _ _ _) _)
  by_cases h : MinusOrder L x y
  · have hy : y ∈ chamber (n + 1) L := plusOrder_output_chamber (L := L) (x := y) (y := x) h
    have hb := (plusOrder_box hy x).mp h
    rw [norm_rawMinus_eq z h]
    have hp : ∏ i, (Ioo (lower y i) (y i)).indicator (wL z.im (lower y i)) (x i) =
        Real.exp (-z.im * ∑ i, (x i - lower y i)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [indicator_of_mem (hb i)]
      rfl
    rw [hp]
    apply Real.exp_le_exp.mpr
    have hs : L - ∑ j, (y j - x j) = ∑ i, (x i - lower y i) + (L - y 0) := by
      simp only [Finset.sum_sub_distrib]
      rw [sum_lower, Fin.sum_univ_succ y]
      ring
    have h0 : 0 < L - y 0 := sub_pos.mpr (hy.2 0).2
    nlinarith [mul_nonneg hη h0.le]
  · simp only [rawMinus, if_neg h, norm_zero]; exact hnn

end Kernels

/-! ### Integrals over the physical torus and operator norms -/

section Torus

variable (L : ℝ) [Fact (0 < L)]

theorem torus_real_integral {m : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f) :
    ∫ y, f (representatives L y) ∂PhysicalTensor.torusPiMeasure L m =
      ∫ y, f y ∂cubeMeasure m L := by
  have h := integral_representatives L (fun y => ((f y : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp hf)
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

theorem cube_integral_le {m : ℕ} {η : ℝ} (hη : 0 < η) (F : (Fin m → ℝ) → ℝ)
    (hF0 : ∀ y, 0 ≤ F y) (a b : Fin m → ℝ) (w : Fin m → ℝ → ℝ) (hwc : ∀ i, Continuous (w i))
    (hw0 : ∀ i t, 0 ≤ w i t)
    (hw : ∀ i, ∫ t, (Ioo (a i) (b i)).indicator (w i) t ≤ 1 / η)
    (hle : ∀ y, F y ≤ ∏ i, (Ioo (a i) (b i)).indicator (w i) (y i)) :
    ∫ y, F y ∂cubeMeasure m L ≤ (1 / η) ^ m := by
  have hGi := integrable_box_prod a b w hwc
  have hG0 : ∀ y : Fin m → ℝ, 0 ≤ ∏ i, (Ioo (a i) (b i)).indicator (w i) (y i) := fun y =>
    Finset.prod_nonneg (fun i _ => indicator_nonneg (fun s _ => hw0 i s) _)
  calc ∫ y, F y ∂cubeMeasure m L
      ≤ ∫ y : Fin m → ℝ, ∏ i, (Ioo (a i) (b i)).indicator (w i) (y i) ∂cubeMeasure m L :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hF0) hGi.restrict
          (Filter.Eventually.of_forall hle)
    _ ≤ ∫ y : Fin m → ℝ, ∏ i, (Ioo (a i) (b i)).indicator (w i) (y i) :=
        setIntegral_le_integral hGi (Filter.Eventually.of_forall hG0)
    _ ≤ (1 / η) ^ m := integral_box_prod η hη a b w hwc hw0 hw

variable {L}

theorem plus_row_integral {m : ℕ} (z : ℂ) (hη : 0 < z.im) (x : Fin m → AddCircle L) :
    ∫ y, ‖(plusKernel L m z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L m ≤ (1 / z.im) ^ m := by
  have hm : Measurable fun y : Fin m → ℝ => ‖rawPlus L z (representatives L x) y‖ :=
    ((measurable_rawPlus m L z).comp (measurable_const.prodMk measurable_id)).norm
  change ∫ y, (fun y' => ‖rawPlus L z (representatives L x) y'‖) (representatives L y) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  exact cube_integral_le L hη _ (fun _ => norm_nonneg _) _ _ (fun i => wR z.im (representatives L x i))
    (fun i => continuous_wR _ _) (fun i => wR_nonneg _ _)
    (fun i => integral_indicator_wR _ _ _ hη) (fun y => rawPlus_row_le L z _ y)

theorem plus_col_integral {m : ℕ} (z : ℂ) (hη : 0 < z.im) (y : Fin m → AddCircle L) :
    ∫ x, ‖(plusKernel L m z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L m ≤ (1 / z.im) ^ m := by
  have hm : Measurable fun x : Fin m → ℝ => ‖rawPlus L z x (representatives L y)‖ :=
    ((measurable_rawPlus m L z).comp (measurable_id.prodMk measurable_const)).norm
  change ∫ x, (fun x' => ‖rawPlus L z x' (representatives L y)‖) (representatives L x) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  exact cube_integral_le L hη _ (fun _ => norm_nonneg _) _ _ (fun i => wL z.im (representatives L y i))
    (fun i => continuous_wL _ _) (fun i => wL_nonneg _ _)
    (fun i => integral_indicator_wL _ _ _ hη) (fun x => rawPlus_col_le L z x _)

theorem minus_row_integral {n : ℕ} (z : ℂ) (hη : 0 < z.im) (x : Fin (n + 1) → AddCircle L) :
    ∫ y, ‖(minusKernel L (n + 1) z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L (n + 1) ≤
      (1 / z.im) ^ (n + 1) := by
  have hm : Measurable fun y : Fin (n + 1) → ℝ => ‖rawMinus L z (representatives L x) y‖ :=
    ((measurable_rawMinus (n + 1) L z).comp (measurable_const.prodMk measurable_id)).norm
  change ∫ y, (fun y' => ‖rawMinus L z (representatives L x) y'‖) (representatives L y) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  exact cube_integral_le L hη _ (fun _ => norm_nonneg _) _ _
    (fun i => wR z.im (upper L (representatives L x) i))
    (fun i => continuous_wR _ _) (fun i => wR_nonneg _ _)
    (fun i => integral_indicator_wR _ _ _ hη) (fun y => rawMinus_row_le L z hη.le _ y)

theorem minus_col_integral {n : ℕ} (z : ℂ) (hη : 0 < z.im) (y : Fin (n + 1) → AddCircle L) :
    ∫ x, ‖(minusKernel L (n + 1) z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L (n + 1) ≤
      (1 / z.im) ^ (n + 1) := by
  have hm : Measurable fun x : Fin (n + 1) → ℝ => ‖rawMinus L z x (representatives L y)‖ :=
    ((measurable_rawMinus (n + 1) L z).comp (measurable_id.prodMk measurable_const)).norm
  change ∫ x, (fun x' => ‖rawMinus L z x' (representatives L y)‖) (representatives L x) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  exact cube_integral_le L hη _ (fun _ => norm_nonneg _) _ _
    (fun i => wL z.im (lower (representatives L y) i))
    (fun i => continuous_wL _ _) (fun i => wL_nonneg _ _)
    (fun i => integral_indicator_wL _ _ _ hη) (fun x => rawMinus_col_le L z hη.le x _)

theorem norm_plusKernel_le {m : ℕ} (z : ℂ) (hη : 0 < z.im) :
    ‖(plusKernel L m z).operator‖ ≤ (1 / z.im) ^ m :=
  norm_operator_le_schur _ _ (by positivity) (plus_row_integral z hη) (plus_col_integral z hη)

theorem norm_minusKernel_le {n : ℕ} (z : ℂ) (hη : 0 < z.im) :
    ‖(minusKernel L (n + 1) z).operator‖ ≤ (1 / z.im) ^ (n + 1) :=
  norm_operator_le_schur _ _ (by positivity) (minus_row_integral z hη) (minus_col_integral z hη)

/-- Sharp bound for the raw operator `K̃⁺ + K̃⁻`. -/
theorem norm_rawOperator_le_sharp {n : ℕ} (z : ℂ) (hη : 0 < z.im) :
    ‖rawOperator L (n + 1) z‖ ≤ 2 * (1 / z.im) ^ (n + 1) := by
  unfold rawOperator
  calc _ ≤ ‖(plusKernel L (n + 1) z).operator‖ + ‖(minusKernel L (n + 1) z).operator‖ :=
        norm_add_le _ _
    _ ≤ (1 / z.im) ^ (n + 1) + (1 / z.im) ^ (n + 1) :=
        add_le_add (norm_plusKernel_le z hη) (norm_minusKernel_le z hη)
    _ = _ := by ring

theorem norm_positionInclusion_le (m : ℕ) : ‖QuantumNLS.BethePhysicalTransfer.positionInclusion L m‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => ?_)
  unfold QuantumNLS.BethePhysicalTransfer.positionInclusion
  simp only [ContinuousLinearMap.comp_apply, one_mul]
  rw [ContinuousLinearEquiv.coe_coe]
  have := (PhysicalTensor.physUnitary (L := L) (N := m)).norm_map (f : TensorCarrier.HilbertTensorPower ℂ (PhysicalTensor.L2T L) m)
  rw [← Submodule.norm_coe]
  exact this.le

/-- **`‖K_{r,z}‖ ≤ 2 (Im z)^{-r}`** (`lem:root-placement`, first clause), for the physical kernels
`K_{r,z} = P_r(K̃⁺+K̃⁻)P_r`, `r ≥ 1`, `Im z > 0`. -/
theorem norm_physicalKernel_le {r : ℕ} (hr : 1 ≤ r) (z : ℂ) (hη : 0 < z.im) :
    ‖QuantumNLS.BethePhysicalTransfer.physicalKernel L r z‖ ≤ 2 * (z.im)⁻¹ ^ r := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  unfold QuantumNLS.BethePhysicalTransfer.physicalKernel
  have hP := norm_positionInclusion_le (L := L) (n + 1)
  have hR := norm_rawOperator_le_sharp (L := L) (n := n) z hη
  have hPa : ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)).adjoint‖ ≤ 1 := by
    have : ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)).adjoint‖ =
        ‖QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)‖ :=
      LinearIsometryEquiv.norm_map _ _
    rw [this]; exact hP
  have h2 := ContinuousLinearMap.opNorm_comp_le
    (QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)).adjoint
    ((rawOperator L (n + 1) z).comp (QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)))
  have h3 := ContinuousLinearMap.opNorm_comp_le (rawOperator L (n + 1) z)
    (QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1))
  rw [one_div] at hR
  calc _ ≤ ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)).adjoint‖ *
        ‖(rawOperator L (n + 1) z).comp (QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1))‖ := h2
    _ ≤ 1 * (‖rawOperator L (n + 1) z‖ *
        ‖QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)‖) :=
        mul_le_mul hPa h3 (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ ≤ 1 * (2 * (z.im)⁻¹ ^ (n + 1) * 1) := by
        gcongr
    _ = _ := by ring

/-! ### The product-state clauses -/

section Product

open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.HighMomentsOps
  QuantumNLS.HighMomentsRank QuantumNLS.HighMomentsWord QuantumNLS.HighMomentsCount
  QuantumNLS.HighMomentsAssembly QuantumNLS.HighMomentsFinal QuantumNLS.PlacementGrouping
  QuantumNLS.RootOverlapCommutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The family of kernels that is `A` in rank `r` and `0` otherwise. -/
def oneRank (r : ℕ) (A : BoundedSymmetricKernel H r) : ∀ r' : ℕ, BoundedSymmetricKernel H r' :=
  fun r' => if h : r' = r then cast (congrArg (BoundedSymmetricKernel H) h.symm) A else 0

theorem oneRank_self (r : ℕ) (A : BoundedSymmetricKernel H r) : oneRank r A r = A := by
  simp [oneRank]

/-- Every placement has expectation `a` in the product state (`⟨u^N, P_S(A) u^N⟩ = ⟨u^r, A u^r⟩`). -/
theorem inner_Pl (u : H) (hu : ‖u‖ = 1) (B : ∀ r : ℕ, BoundedSymmetricKernel H r) {N : ℕ}
    (s : Finset (Fin N)) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N), Pl B N s (htpow N u)⟫_ℂ =
      kernelProductSymbol (B s.card) u := by
  have h1 := Pl_rk1_Pl u hu B s
  have hPi := Pl_rk1_htpow u hu s
  have hsa := Pl_rk1_isAdj u s
  calc ⟪(htpow N u : HilbertTensorPower ℂ H N), Pl B N s (htpow N u)⟫_ℂ
      = ⟪Pl (rkFam u) N s (htpow N u), Pl B N s (htpow N u)⟫_ℂ := by rw [hPi]
    _ = ⟪(htpow N u : HilbertTensorPower ℂ H N), Pl (rkFam u) N s (Pl B N s (htpow N u))⟫_ℂ :=
        hsa _ _
    _ = _ := by
        rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_htpow_one u hu N]
        simp

/-- **`⟨u^{⊗N}, U_{N,r}(A) u^{⊗N}⟩ = a`** (`lem:root-placement`, second clause), full-tensor form. -/
theorem inner_rawSubsetAverage (u : H) (hu : ‖u‖ = 1) {N r : ℕ} (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N), rawSubsetAverage N r hr A (htpow N u)⟫_ℂ =
      kernelProductSymbol A u := by
  have hB := oneRank_self r A
  have hav := rawAvg_eq_sum (oneRank r A) r hr
  rw [hB] at hav
  rw [hav, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, inner_smul_right,
    inner_sum]
  have hterm : ∀ s ∈ Finset.powersetCard r (Finset.univ : Finset (Fin N)),
      ⟪(htpow N u : HilbertTensorPower ℂ H N), Pl (oneRank r A) N s (htpow N u)⟫_ℂ =
        kernelProductSymbol A u := by
    intro s hs
    have hc : s.card = r := (Finset.mem_powersetCard.mp hs).2
    rw [inner_Pl u hu]
    have := congrArg (fun k => kernelProductSymbol (oneRank r A k) u) hc
    rw [this, hB]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hC : (N.choose r : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  field_simp

theorem inner_genericU (u : H) (hu : ‖u‖ = 1) {N r : ℕ} (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    ⟪wvec N u, genericU_N_r N r hr A (wvec N u)⟫_ℂ = kernelProductSymbol A u := by
  have h := inner_rawSubsetAverage u hu hr A
  show ⟪(wvec N u : HilbertTensorPower ℂ H N),
    ((genericU_N_r N r hr A (wvec N u) : SymSector ℂ H N) : HilbertTensorPower ℂ H N)⟫_ℂ = _
  rw [coe_genericU]
  exact h

/-- **Centered placement average**: `‖(U_{N,r}(A) − a) u^{⊗N}‖ ≤ 2 r ‖A‖ / √N` (`lem:root-placement`, third
clause), full-tensor form. -/
theorem centered_avg_norm_le (u : H) (hu : ‖u‖ = 1) {N r : ℕ} (hr : r ≤ N) (hN : 0 < N)
    (A : BoundedSymmetricKernel H r) :
    ‖(rawSubsetAverage N r hr A - kernelProductSymbol A u • (1 : Op H N)) (htpow N u)‖ ≤
      2 * r * ‖A‖ / Real.sqrt N := by
  classical
  set B := oneRank r A with hBdef
  have hB : B r = A := oneRank_self r A
  set P := Finset.powersetCard r (Finset.univ : Finset (Fin N)) with hP
  set a := kernelProductSymbol A u with ha
  have hA : 0 ≤ ‖A‖ := ContinuousLinearMap.opNorm_nonneg A
  have hCpos : (0 : ℝ) < N.choose r := by exact_mod_cast Nat.choose_pos hr
  have hC : (N.choose r : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcardP : P.card = N.choose r := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ s ∈ P, s.card = r := fun s hs => (Finset.mem_powersetCard.mp hs).2
  have haa : ∀ s ∈ P, aa u B s.card = a := by
    intro s hs
    have := congrArg (fun k => kernelProductSymbol (B k) u) (hmem s hs)
    show kernelProductSymbol (B s.card) u = a
    rw [this, hB]
  have hnormB : ∀ s ∈ P, ‖B s.card‖ = ‖A‖ := by
    intro s hs
    have := congrArg (fun k => ‖B k‖) (hmem s hs)
    rw [this, hB]
  set Y : HilbertTensorPower ℂ H N := ∑ s ∈ P, Tf u B N s (htpow N u) with hY
  have hX : (rawSubsetAverage N r hr A - a • (1 : Op H N)) (htpow N u) =
      ((N.choose r : ℂ)⁻¹) • Y := by
    have hav := rawAvg_eq_sum B r hr
    rw [hB] at hav
    rw [hav]
    have hsum : Y = ∑ s ∈ P, Pl B N s (htpow N u) - (N.choose r : ℂ) • (a • htpow N u) := by
      rw [hY]
      have : ∀ s ∈ P, Tf u B N s (htpow N u) = Pl B N s (htpow N u) - a • htpow N u := by
        intro s hs
        simp only [Tf, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, haa s hs]
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, hcardP,
        Nat.cast_smul_eq_nsmul ℂ]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.one_apply]
    rw [hsum, smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul]
  have hpair : ∀ s ∈ P, ∀ s' ∈ P,
      ‖⟪Tf u B N s (htpow N u), Tf u B N s' (htpow N u)⟫_ℂ‖ ≤
        if (s ∩ s').Nonempty then 4 * ‖A‖ ^ 2 else 0 := by
    intro s hs s' hs'
    have hadj := isAdj_Tf u B N s
    have e : ⟪Tf u B N s (htpow N u), Tf u B N s' (htpow N u)⟫_ℂ =
        ⟪(htpow N u : HilbertTensorPower ℂ H N),
          Tf u (adjFam B) N s (Tf u B N s' (htpow N u))⟫_ℂ := hadj _ _
    rw [e]
    split_ifs with hne
    · refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_htpow_one u hu N, one_mul]
      have h1 := norm_Tf_le u hu (adjFam B) N s
      have h2 := norm_Tf_le u hu B N s'
      rw [norm_adjFam, hnormB s hs] at h1
      rw [hnormB s' hs'] at h2
      have h3 := ContinuousLinearMap.le_opNorm (Tf u (adjFam B) N s) (Tf u B N s' (htpow N u))
      have h4 := ContinuousLinearMap.le_opNorm (Tf u B N s') (htpow N u)
      rw [norm_htpow_one u hu N, mul_one] at h4
      calc ‖Tf u (adjFam B) N s (Tf u B N s' (htpow N u))‖
          ≤ ‖Tf u (adjFam B) N s‖ * ‖Tf u B N s' (htpow N u)‖ := h3
        _ ≤ (2 * ‖A‖) * (2 * ‖A‖) := mul_le_mul h1 (h4.trans h2) (norm_nonneg _) (by positivity)
        _ = 4 * ‖A‖ ^ 2 := by ring
    · have hd : Disjoint s s' := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact Finset.not_nonempty_iff_eq_empty.mp hne
      have hz := word_iso (N := N) (m := 1) u hu ![adjFam B, B] ![s, s'] 0 (by
        intro i hi
        have : i = 1 := by fin_cases i <;> simp_all
        subst this
        simpa using hd)
      have hw : wprod 2 (fun i => Tf u ((![adjFam B, B] : Fin 2 → ∀ r : ℕ, BoundedSymmetricKernel H r) i)
          N ((![s, s'] : Fin 2 → Finset (Fin N)) i)) (htpow N u) =
          Tf u (adjFam B) N s (Tf u B N s' (htpow N u)) := by
        simp [wprod]
      rw [hw] at hz
      rw [hz]
      simp
  have hmeet : ∀ s' ∈ P, ((P.filter (fun s => (s ∩ s').Nonempty)).card : ℝ) ≤
      (r : ℝ) * r * N.choose r / N := by
    intro s' hs'
    have h := card_meeting_mul_le (N := N) r s'
    rw [hmem s' hs'] at h
    rw [le_div_iff₀ hNr]
    exact_mod_cast h
  have hYsq : ‖Y‖ ^ 2 ≤ 4 * ‖A‖ ^ 2 * ((N.choose r : ℝ) ^ 2 * (r : ℝ) ^ 2 / N) := by
    have h1 : ‖Y‖ ^ 2 = ‖⟪Y, Y⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K]; simp [norm_pow]
    have h2 : ⟪Y, Y⟫_ℂ = ∑ s ∈ P, ∑ s' ∈ P,
        ⟪Tf u B N s (htpow N u), Tf u B N s' (htpow N u)⟫_ℂ := by
      conv_lhs => rw [hY]
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [inner_sum]
    rw [h1, h2]
    calc ‖∑ s ∈ P, ∑ s' ∈ P, ⟪Tf u B N s (htpow N u), Tf u B N s' (htpow N u)⟫_ℂ‖
        ≤ ∑ s ∈ P, ‖∑ s' ∈ P, ⟪Tf u B N s (htpow N u), Tf u B N s' (htpow N u)⟫_ℂ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ s ∈ P, ∑ s' ∈ P, ‖⟪Tf u B N s (htpow N u), Tf u B N s' (htpow N u)⟫_ℂ‖ :=
          Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
      _ ≤ ∑ s ∈ P, ∑ s' ∈ P, (if (s ∩ s').Nonempty then 4 * ‖A‖ ^ 2 else 0) :=
          Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun s' hs' => hpair s hs s' hs'))
      _ = ∑ s' ∈ P, ∑ s ∈ P, (if (s ∩ s').Nonempty then 4 * ‖A‖ ^ 2 else 0) :=
          Finset.sum_comm
      _ ≤ ∑ s' ∈ P, (4 * ‖A‖ ^ 2) * ((r : ℝ) * r * N.choose r / N) := by
          refine Finset.sum_le_sum (fun s' hs' => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          calc ((P.filter (fun s => (s ∩ s').Nonempty)).card : ℝ) * (4 * ‖A‖ ^ 2)
              ≤ ((r : ℝ) * r * N.choose r / N) * (4 * ‖A‖ ^ 2) :=
                mul_le_mul_of_nonneg_right (hmeet s' hs') (by positivity)
            _ = _ := by ring
      _ = 4 * ‖A‖ ^ 2 * ((N.choose r : ℝ) ^ 2 * (r : ℝ) ^ 2 / N) := by
          rw [Finset.sum_const, hcardP, nsmul_eq_mul]
          ring
  rw [hX, norm_smul, norm_inv, Complex.norm_natCast]
  set M : ℝ := 2 * r * ‖A‖ / Real.sqrt N with hM
  have hM0 : 0 ≤ M := div_nonneg (mul_nonneg (by positivity) hA) (Real.sqrt_nonneg _)
  have hM2 : M ^ 2 = 4 * ‖A‖ ^ 2 * (r : ℝ) ^ 2 / N := by
    rw [hM, div_pow, mul_pow, mul_pow, Real.sq_sqrt hNr.le]; ring
  have hXsq : ((N.choose r : ℝ)⁻¹ * ‖Y‖) ^ 2 ≤ M ^ 2 := by
    rw [hM2, mul_pow, inv_pow]
    have : ((N.choose r : ℝ) ^ 2)⁻¹ * (4 * ‖A‖ ^ 2 * ((N.choose r : ℝ) ^ 2 * (r : ℝ) ^ 2 / N)) =
        4 * ‖A‖ ^ 2 * (r : ℝ) ^ 2 / N := by
      field_simp
    calc ((N.choose r : ℝ) ^ 2)⁻¹ * ‖Y‖ ^ 2
        ≤ ((N.choose r : ℝ) ^ 2)⁻¹ * (4 * ‖A‖ ^ 2 * ((N.choose r : ℝ) ^ 2 * (r : ℝ) ^ 2 / N)) :=
          mul_le_mul_of_nonneg_left hYsq (by positivity)
      _ = _ := this
  exact le_of_sq_le_sq hXsq hM0

/-- Symmetric-sector form of the third clause. -/
theorem centered_genericU_norm_le (u : H) (hu : ‖u‖ = 1) {N r : ℕ} (hr : r ≤ N) (hN : 0 < N)
    (A : BoundedSymmetricKernel H r) :
    ‖(genericU_N_r N r hr A - kernelProductSymbol A u • (1 : BoundedSymmetricKernel H N))
        (wvec N u)‖ ≤ 2 * r * ‖A‖ / Real.sqrt N := by
  have h := centered_avg_norm_le u hu hr hN A
  have e : (((genericU_N_r N r hr A - kernelProductSymbol A u • (1 : BoundedSymmetricKernel H N))
      (wvec N u) : SymSector ℂ H N) : HilbertTensorPower ℂ H N) =
      (rawSubsetAverage N r hr A - kernelProductSymbol A u • (1 : Op H N)) (htpow N u) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, Submodule.coe_sub, Submodule.coe_smul, coe_genericU]
    rfl
  rw [← Submodule.norm_coe, e]
  exact h

end Product

/-! ### `lem:root-placement` for the physical kernels -/

open QuantumNLS.KernelDefinition QuantumNLS.TensorCarrier

/-- **`lem:root-placement`** (R-FFA8D3F2), on `Sym^N L²(𝕋_L)`: for a unit profile `u`, `1 ≤ r ≤ N` and
`η = Im z > 0`:
* `‖K_{r,z}‖ ≤ 2 η^{-r}`;
* for every bounded kernel `A` on `Sym^r`, with `a = ⟨u^{⊗r}, A u^{⊗r}⟩`:
  `⟨u^{⊗N}, U_{N,r}(A) u^{⊗N}⟩ = a` and `‖(U_{N,r}(A) − a) u^{⊗N}‖ ≤ 2 r ‖A‖/√N`. -/
theorem lem_root_placement (u : PhysicalTensor.L2T L) (hu : ‖u‖ = 1) {N r : ℕ} (hr1 : 1 ≤ r)
    (hrN : r ≤ N) (z : ℂ) (hη : 0 < z.im) :
    ‖QuantumNLS.BethePhysicalTransfer.physicalKernel L r z‖ ≤ 2 * (z.im)⁻¹ ^ r ∧
    (∀ A : BoundedSymmetricKernel (PhysicalTensor.L2T L) r,
      ⟪(QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u),
        genericU_N_r N r hrN A
          (QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u)⟫_ℂ =
        kernelProductSymbol A u ∧
      ‖(genericU_N_r N r hrN A - kernelProductSymbol A u •
          (1 : BoundedSymmetricKernel (PhysicalTensor.L2T L) N))
          (QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u)‖ ≤
        2 * r * ‖A‖ / Real.sqrt N) :=
  ⟨norm_physicalKernel_le hr1 z hη, fun A =>
    ⟨inner_genericU u hu hrN A, centered_genericU_norm_le u hu hrN (by omega) A⟩⟩

end Torus

#print axioms norm_operator_le_schur
#print axioms norm_physicalKernel_le
#print axioms inner_genericU
#print axioms centered_avg_norm_le
#print axioms lem_root_placement

end QuantumNLS.RootPlacementBound
