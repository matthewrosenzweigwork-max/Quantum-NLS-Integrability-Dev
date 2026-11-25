import Mathlib
import QuantumNLS.RiccatiSobolevE1
import QuantumNLS.RiccatiSobolevE2
import QuantumNLS.RiccatiSobolevE2b

/-!
# R-3FEAD88B blocker 3, stage E3-pre: the periodic H^a space as a complete normed space

Source convention (DEF-002, stages E1, E2, E2b): a periodic field is a Fourier sequence `c : ℤ → ℂ`
with squared norm `hsq L a c = ∑_k wt_k |c_k|²`, `wt_k = pw_k²`, `pw_k = (1 + |2πk/L|)^a`.

Banach model (d-coordinates): `Ell2 := lp (fun _ : ℤ => ℂ) 2`, with the isometric identification
`x ↦ toField x`, `(toField x)_k = x_k / pw_k`. Then `hsq L a (toField x) = ofReal (‖x‖²)` exactly
(`hsq_toField`), so `Ell2` is the complete space of periodic H^a fields with the DEF-002 norm.

Operators on `Ell2` (all transferred from E1 and E2b, nothing else assumed):
* `ropCLM L z hz`: the resolvent `R_z = (∂x − i z)⁻¹`, `‖R_z x‖ ≤ (Im z)⁻¹ ‖x‖`.
* `mulBil hL ha`: the algebra product (convolution of Fourier coefficients), bounded bilinear with
  constant `Cmul L a = √(4 (2^a)² ∑ wt⁻¹)`, i.e. `‖x·y‖ ≤ Cmul ‖x‖ ‖y‖` (`a > 1/2`, `L > 0`).

Proof-level content: pointwise lemmas on `ℤ`-indexed sums, `lp` membership by `memℓp_gen`,
the norm identity `‖x‖² = ∑ ‖x_k‖²`, and `LinearMap.mkContinuous` / `mkContinuous₂`.
Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace QuantumNLS.RiccatiSobolevBanach

open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2 QuantumNLS.RiccatiSobolevE2b

/-- The Banach space of weighted-`ℓ²` sequences (d-coordinates of the periodic H^a fields). -/
abbrev Ell2 : Type := lp (fun _ : ℤ => ℂ) (2 : ENNReal)

theorem two_toReal : (2 : ENNReal).toReal = 2 := by norm_num

theorem pw_pos (L a : ℝ) (k : ℤ) : 0 < pw L a k := by
  unfold pw
  positivity

theorem pw_ne_zero (L a : ℝ) (k : ℤ) : ((pw L a k : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pw_pos L a k).ne'

/-- Squared `ℓ²` norms are summable on `Ell2`. -/
theorem summable_sq (x : Ell2) : Summable (fun k => ‖x k‖ ^ 2) := by
  have h := Memℓp.summable (by norm_num) (lp.memℓp x)
  rw [two_toReal] at h
  simpa only [Real.rpow_two] using h

/-- Norm identity `‖x‖² = ∑_k ‖x_k‖²` on `Ell2`. -/
theorem norm_sq_eq_tsum (x : Ell2) : ‖x‖ ^ 2 = ∑' k, ‖x k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) x
  rw [two_toReal] at h
  simpa only [Real.rpow_two] using h

/-- Pointwise comparison implies the norm comparison on `Ell2`. -/
theorem norm_le_of_pointwise {x y : Ell2} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k, ‖y k‖ ≤ C * ‖x k‖) : ‖y‖ ≤ C * ‖x‖ := by
  have hx : Summable (fun k => (C * ‖x k‖) ^ 2) :=
    ((summable_sq x).mul_left (C ^ 2)).congr fun k => by ring
  have key : ∑' k, ‖y k‖ ^ 2 ≤ ∑' k, (C * ‖x k‖) ^ 2 :=
    Summable.tsum_le_tsum (fun k => pow_le_pow_left₀ (norm_nonneg _) (h k) 2)
      (summable_sq y) hx
  have e : ∑' k, (C * ‖x k‖) ^ 2 = (C * ‖x‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_tsum x, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  have hsq' : ‖y‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [norm_sq_eq_tsum y, ← e]
    exact key
  exact (pow_le_pow_iff_left₀ (norm_nonneg y) (mul_nonneg hC (norm_nonneg x)) two_ne_zero).1 hsq'

/-- Fourier coefficients `c_k = x_k / pw_k` of a point `x` of the Banach space. -/
def toField (L a : ℝ) (x : Ell2) : ℤ → ℂ := fun k => x k / ((pw L a k : ℝ) : ℂ)

theorem wt_mul_norm_div_sq (L a : ℝ) (k : ℤ) (z : ℂ) :
    wt L a k * ‖z / ((pw L a k : ℝ) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 := by
  have hp : pw L a k ≠ 0 := (pw_pos L a k).ne'
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (pw_pos L a k).le, wt_eq_pw_sq, div_pow]
  field_simp

/-- Isometry: the H^a norm of `toField x` equals the Banach norm of `x`. -/
theorem hsq_toField (L a : ℝ) (x : Ell2) : hsq L a (toField L a x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hterm : ∀ k, wt L a k * ‖toField L a x k‖ ^ 2 = ‖x k‖ ^ 2 := fun k =>
    wt_mul_norm_div_sq L a k (x k)
  unfold hsq
  simp only [hterm]
  rw [norm_sq_eq_tsum x, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) (summable_sq x)]

theorem hsq_toField_ne_top (L a : ℝ) (x : Ell2) : hsq L a (toField L a x) ≠ ⊤ := by
  rw [hsq_toField]
  exact ENNReal.ofReal_ne_top

/-- Summability of `wt ‖c‖²` gives membership of the rescaled sequence in `lp 2`. -/
theorem memℓp_of_summable {L a : ℝ} {c : ℤ → ℂ}
    (hc : Summable (fun k => wt L a k * ‖c k‖ ^ 2)) :
    Memℓp (fun k => ((pw L a k : ℝ) : ℂ) * c k) 2 := by
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  refine hc.congr fun k => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pw_pos L a k).le, mul_pow, wt_eq_pw_sq]

/-- The H^a Riccati/algebra constant `K_a = 4 (2^a)² ∑ wt⁻¹` and its square root. -/
def Kconst (L a : ℝ) : ℝ := 4 * (2 ^ a) ^ 2 * ∑' k : ℤ, (wt L a k)⁻¹

theorem Kconst_nonneg (L a : ℝ) : 0 ≤ Kconst L a :=
  mul_nonneg (by positivity) (tsum_nonneg fun k => inv_nonneg.2 (wt_nonneg L a k))

/-- Operator constant of the algebra product on `Ell2`. -/
def Cmul (L a : ℝ) : ℝ := Real.sqrt (Kconst L a)

theorem summable_conv {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {c d : ℤ → ℂ}
    (hc : hsq L a c ≠ ⊤) (hd : hsq L a d ≠ ⊤) (k : ℤ) :
    Summable (fun j => c j * d (k - j)) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨hHc, _⟩ := hsq_summable_eq hc
  obtain ⟨hHd, _⟩ := hsq_summable_eq hd
  have hc1 : Summable (fun j => ‖c j‖) := l1_summable hL ha hHc
  have hbd : ∀ i, ‖d i‖ ≤ 1 + ∑' m, wt L a m * ‖d m‖ ^ 2 := fun i => by
    have h1 : wt L a i * ‖d i‖ ^ 2 ≤ ∑' m, wt L a m * ‖d m‖ ^ 2 :=
      hHd.le_tsum i (fun j _ => mul_nonneg (wt_nonneg L a j) (sq_nonneg _))
    have h2 : ‖d i‖ ^ 2 ≤ wt L a i * ‖d i‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_wt ha0 i)
    nlinarith [sq_nonneg (‖d i‖ - 1), sq_nonneg (‖d i‖)]
  refine Summable.of_norm_bounded (hc1.mul_right (1 + ∑' m, wt L a m * ‖d m‖ ^ 2)) (fun j => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbd (k - j)) (norm_nonneg _)

theorem convC_add_left {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {c c' d : ℤ → ℂ}
    (hc : hsq L a c ≠ ⊤) (hc' : hsq L a c' ≠ ⊤) (hd : hsq L a d ≠ ⊤) (k : ℤ) :
    convC (fun j => c j + c' j) d k = convC c d k + convC c' d k := by
  unfold convC
  rw [← Summable.tsum_add (summable_conv hL ha hc hd k) (summable_conv hL ha hc' hd k)]
  exact tsum_congr fun j => by beta_reduce; ring

theorem convC_add_right {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {c d d' : ℤ → ℂ}
    (hc : hsq L a c ≠ ⊤) (hd : hsq L a d ≠ ⊤) (hd' : hsq L a d' ≠ ⊤) (k : ℤ) :
    convC c (fun i => d i + d' i) k = convC c d k + convC c d' k := by
  unfold convC
  rw [← Summable.tsum_add (summable_conv hL ha hc hd k) (summable_conv hL ha hc hd' k)]
  exact tsum_congr fun j => by beta_reduce; ring

theorem convC_smul_left (r : ℂ) (c d : ℤ → ℂ) (k : ℤ) :
    convC (fun j => r * c j) d k = r * convC c d k := by
  unfold convC
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by beta_reduce; ring

theorem convC_smul_right (r : ℂ) (c d : ℤ → ℂ) (k : ℤ) :
    convC c (fun i => r * d i) k = r * convC c d k := by
  unfold convC
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by beta_reduce; ring

theorem toField_add (L a : ℝ) (x y : Ell2) :
    toField L a (x + y) = fun k => toField L a x k + toField L a y k := by
  funext k
  simp only [toField, lp.coeFn_add, Pi.add_apply, add_div]

theorem toField_smul (L a : ℝ) (r : ℂ) (x : Ell2) :
    toField L a (r • x) = fun k => r * toField L a x k := by
  funext k
  simp only [toField, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- Coordinates of the algebra product: `(x·y)_k = pw_k (conv(toField x, toField y))_k`. -/
def mulFun (L a : ℝ) (x y : Ell2) : ℤ → ℂ :=
  fun k => ((pw L a k : ℝ) : ℂ) * convC (toField L a x) (toField L a y) k

theorem hsq_conv_ne_top {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    hsq L a (convC (toField L a x) (toField L a y)) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hsq_toField_ne_top L a x))
      (hsq_toField_ne_top L a y))
    (hsq_convC_le hL ha _ _ (hsq_toField_ne_top L a x) (hsq_toField_ne_top L a y))

theorem mem_mulFun {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    Memℓp (mulFun L a x y) 2 :=
  memℓp_of_summable (hsq_summable_eq (hsq_conv_ne_top hL ha x y)).1

/-- The algebra product of two points of the Banach space. -/
def mulEll {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) : Ell2 :=
  ⟨mulFun L a x y, mem_mulFun hL ha x y⟩

theorem mulEll_apply {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) (k : ℤ) :
    mulEll hL ha x y k = ((pw L a k : ℝ) : ℂ) * convC (toField L a x) (toField L a y) k := rfl

theorem toField_mulEll {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    toField L a (mulEll hL ha x y) = convC (toField L a x) (toField L a y) := by
  funext k
  have hp := pw_ne_zero L a k
  show ((pw L a k : ℝ) : ℂ) * convC (toField L a x) (toField L a y) k / ((pw L a k : ℝ) : ℂ)
    = convC (toField L a x) (toField L a y) k
  exact mul_div_cancel_left₀ _ hp

theorem mulEll_add_left {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x x' y : Ell2) :
    mulEll hL ha (x + x') y = mulEll hL ha x y + mulEll hL ha x' y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  rw [mulEll_apply, mulEll_apply, mulEll_apply, toField_add,
    convC_add_left hL ha (hsq_toField_ne_top L a x) (hsq_toField_ne_top L a x')
      (hsq_toField_ne_top L a y) k, mul_add]

theorem mulEll_add_right {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y y' : Ell2) :
    mulEll hL ha x (y + y') = mulEll hL ha x y + mulEll hL ha x y' := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  rw [mulEll_apply, mulEll_apply, mulEll_apply, toField_add,
    convC_add_right hL ha (hsq_toField_ne_top L a x) (hsq_toField_ne_top L a y)
      (hsq_toField_ne_top L a y') k, mul_add]

theorem mulEll_smul_left {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r : ℂ) (x y : Ell2) :
    mulEll hL ha (r • x) y = r • mulEll hL ha x y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [mulEll_apply, mulEll_apply, toField_smul, convC_smul_left]
  ring

theorem mulEll_smul_right {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r : ℂ) (x y : Ell2) :
    mulEll hL ha x (r • y) = r • mulEll hL ha x y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [mulEll_apply, mulEll_apply, toField_smul, convC_smul_right]
  ring

/-- Operator bound for the algebra product: `‖x·y‖ ≤ Cmul ‖x‖ ‖y‖` (`L > 0`, `a > 1/2`). -/
theorem norm_mulEll_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    ‖mulEll hL ha x y‖ ≤ Cmul L a * ‖x‖ * ‖y‖ := by
  have hK0 : 0 ≤ Kconst L a := Kconst_nonneg L a
  have hle : hsq L a (convC (toField L a x) (toField L a y))
      ≤ ENNReal.ofReal (Kconst L a) * hsq L a (toField L a x) * hsq L a (toField L a y) :=
    hsq_convC_le hL ha (toField L a x) (toField L a y)
      (hsq_toField_ne_top L a x) (hsq_toField_ne_top L a y)
  rw [← toField_mulEll hL ha x y, hsq_toField, hsq_toField, hsq_toField] at hle
  rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (mul_nonneg hK0 (sq_nonneg ‖x‖))] at hle
  have h2 : ‖mulEll hL ha x y‖ ^ 2 ≤ Kconst L a * ‖x‖ ^ 2 * ‖y‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hK0 (sq_nonneg ‖x‖)) (sq_nonneg ‖y‖))).1 hle
  have hC : (Cmul L a * ‖x‖ * ‖y‖) ^ 2 = Kconst L a * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    unfold Cmul
    rw [mul_pow, mul_pow, Real.sq_sqrt hK0]
  have hb0 : 0 ≤ Cmul L a * ‖x‖ * ‖y‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hsq_le : ‖mulEll hL ha x y‖ ^ 2 ≤ (Cmul L a * ‖x‖ * ‖y‖) ^ 2 := by
    rw [hC]
    exact h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 two_ne_zero).1 hsq_le

/-- The algebra product as a bilinear map on `lp 2` (linear in each slot). -/
def mulLin {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) : Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] Ell2 :=
  LinearMap.mk₂ ℂ (mulEll hL ha) (fun x x' y => mulEll_add_left hL ha x x' y)
    (fun r x y => mulEll_smul_left hL ha r x y)
    (fun x y y' => mulEll_add_right hL ha x y y')
    (fun r x y => mulEll_smul_right hL ha r x y)

/-- The algebra product as a continuous bilinear map on the periodic H^a space. -/
def mulBil {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) : Ell2 →L[ℂ] Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous₂ (mulLin hL ha) (Cmul L a) (fun x y => norm_mulEll_le hL ha x y)

theorem mulBil_apply {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    mulBil hL ha x y = mulEll hL ha x y := rfl

theorem norm_mulBil_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    ‖mulBil hL ha x y‖ ≤ Cmul L a * ‖x‖ * ‖y‖ :=
  norm_mulEll_le hL ha x y

/-- Coordinates of the resolvent `(∂x − i z)⁻¹`: mode `k` is multiplied by `1/(i(2πk/L − z))`. -/
def ropFun (L : ℝ) (z : ℂ) (x : Ell2) : ℤ → ℂ :=
  fun k => x k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))

theorem mem_ropFun (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) : Memℓp (ropFun L z x) 2 := by
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((summable_sq x).mul_left (z.im⁻¹ ^ 2))
  have h := norm_div_I_mul_le (x k) (freq L k) z hz
  show ‖x k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))‖ ^ 2 ≤ z.im⁻¹ ^ 2 * ‖x k‖ ^ 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  exact h2

/-- The resolvent on `Ell2`. -/
def ropEll (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) : Ell2 :=
  ⟨ropFun L z x, mem_ropFun L z hz x⟩

theorem ropEll_add (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x y : Ell2) :
    ropEll L z hz (x + y) = ropEll L z hz x + ropEll L z hz y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  show (x k + y k) / (Complex.I * (((freq L k : ℝ) : ℂ) - z))
    = x k / (Complex.I * (((freq L k : ℝ) : ℂ) - z)) + y k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))
  exact add_div _ _ _

theorem ropEll_smul (L : ℝ) (z : ℂ) (hz : 0 < z.im) (r : ℂ) (x : Ell2) :
    ropEll L z hz (r • x) = r • ropEll L z hz x := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show r * x k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))
    = r * (x k / (Complex.I * (((freq L k : ℝ) : ℂ) - z)))
  ring

/-- The resolvent as a continuous linear map with norm at most `(Im z)⁻¹`. -/
def ropCLM (L : ℝ) (z : ℂ) (hz : 0 < z.im) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ropEll L z hz x
      map_add' := fun x y => ropEll_add L z hz x y
      map_smul' := fun r x => ropEll_smul L z hz r x }
    (z.im⁻¹)
    (fun x => norm_le_of_pointwise (inv_nonneg.2 hz.le)
      (fun k => norm_div_I_mul_le (x k) (freq L k) z hz))

theorem norm_ropCLM_le (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) :
    ‖ropCLM L z hz x‖ ≤ z.im⁻¹ * ‖x‖ :=
  norm_le_of_pointwise (y := ropCLM L z hz x) (inv_nonneg.2 hz.le)
    (fun k => norm_div_I_mul_le (x k) (freq L k) z hz)

end QuantumNLS.RiccatiSobolevBanach

#print axioms QuantumNLS.RiccatiSobolevBanach.norm_mulBil_le
#print axioms QuantumNLS.RiccatiSobolevBanach.norm_ropCLM_le
#print axioms QuantumNLS.RiccatiSobolevBanach.hsq_toField
