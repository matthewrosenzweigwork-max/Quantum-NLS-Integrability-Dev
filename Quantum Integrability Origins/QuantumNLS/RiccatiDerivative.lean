import Mathlib
import QuantumNLS.RiccatiSobolevBanach

/-!
# R-3FEAD88B stage E4-1: the derivative `∂x` between periodic Sobolev spaces

Convention (DEF-001, DEF-002): `∂x e_k = i (2πk/L) e_k`, so on Fourier coefficients `(∂c)_k = i f_k c_k`,
`f_k = 2πk/L = freq L k`. The DEF-002 squared norm is `hsq L s c = ∑_k wt_s(k) |c_k|²`, `wt_s = (1+|f|)^{2s}`.

Proved here (no assumption on `L` beyond the ones stated):
* `hsq_dField_le`: `hsq L a (∂c) ≤ hsq L (a+1) c` for every `a`, `L`, i.e. `‖∂r‖_{H^a} ≤ ‖r‖_{H^{a+1}}` with
  constant `1`. The reason: `|f| ≤ 1 + |f|`, so `|f|² (1+|f|)^{2a} ≤ (1+|f|)^{2a+2}`.
* `derCLM L : Ell2 →L Ell2` (d-coordinates): `toField L a (derCLM x) = dField L (toField L (a+1) x)` and
  `‖derCLM x‖ ≤ ‖x‖`, i.e. the Banach-level derivative `H^{a+1} → H^a` with norm at most `1`.
* `hsq_dField_le_scaled`: the requested form with the factor `2π/L`, proved under the extra hypothesis `L ≤ 2π`
  (then `1 ≤ 2π/L`). The factor `2π/L` is NOT valid for `L > 2π`: see the note at `hsq_dField_le_scaled`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace QuantumNLS.RiccatiDerivative

open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiSobolevBanach

/-- Fourier symbol of `∂x` on mode `k`: `i · 2πk/L`. -/
def dSymb (L : ℝ) (k : ℤ) : ℂ := Complex.I * ((freq L k : ℝ) : ℂ)

/-- The derivative on Fourier coefficient sequences: `(∂c)_k = i (2πk/L) c_k`. -/
def dField (L : ℝ) (c : ℤ → ℂ) : ℤ → ℂ := fun k => dSymb L k * c k

theorem norm_dSymb (L : ℝ) (k : ℤ) : ‖dSymb L k‖ = |freq L k| := by
  unfold dSymb
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Weight shift: `wt_{a+1}(k) = wt_a(k) (1 + |2πk/L|)²`. -/
theorem wt_succ (L a : ℝ) (k : ℤ) : wt L (a + 1) k = wt L a k * (1 + |freq L k|) ^ 2 := by
  unfold wt
  have hb : (0 : ℝ) < 1 + |freq L k| := by positivity
  rw [show 2 * (a + 1) = 2 * a + 2 by ring, Real.rpow_add hb, Real.rpow_two]

theorem hterm_dField (L a : ℝ) (c : ℤ → ℂ) (k : ℤ) :
    wt L a k * ‖dField L c k‖ ^ 2 ≤ wt L (a + 1) k * ‖c k‖ ^ 2 := by
  have hn : ‖dField L c k‖ = |freq L k| * ‖c k‖ := by
    unfold dField
    rw [norm_mul, norm_dSymb]
  have h1 : |freq L k| ^ 2 ≤ (1 + |freq L k|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
  rw [hn, wt_succ, mul_pow]
  have hw := wt_nonneg L a k
  calc wt L a k * (|freq L k| ^ 2 * ‖c k‖ ^ 2)
      ≤ wt L a k * ((1 + |freq L k|) ^ 2 * ‖c k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) hw
    _ = wt L a k * (1 + |freq L k|) ^ 2 * ‖c k‖ ^ 2 := by ring

/-- Sharp DEF-002 derivative bound: `‖∂c‖_{H^a} ≤ ‖c‖_{H^{a+1}}` (constant `1`), in `ENNReal`. -/
theorem hsq_dField_le (L a : ℝ) (c : ℤ → ℂ) :
    hsq L a (dField L c) ≤ hsq L (a + 1) c := by
  unfold hsq
  exact ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hterm_dField L a c k)

/-- Scaled form. Requires `0 < L ≤ 2π`, where `1 ≤ 2π/L` and the constant `(2π/L)²` is at least `1`.
Note (not a Lean claim): for `L > 2π` no constant `2π/L` works, since for `k` with `2π|k|/L` large the ratio
`|f|/(1+|f|)` tends to `1 > 2π/L`. The constant `1` of `hsq_dField_le` is always valid. -/
theorem hsq_dField_le_scaled {L a : ℝ} (hL0 : 0 < L) (hL : L ≤ 2 * Real.pi) (c : ℤ → ℂ) :
    hsq L a (dField L c) ≤ ENNReal.ofReal ((2 * Real.pi / L) ^ 2) * hsq L (a + 1) c := by
  have h1 : (1 : ℝ) ≤ 2 * Real.pi / L := (one_le_div hL0).2 hL
  have h2 : (1 : ℝ) ≤ (2 * Real.pi / L) ^ 2 := one_le_pow₀ h1
  have h3 : (1 : ENNReal) ≤ ENNReal.ofReal ((2 * Real.pi / L) ^ 2) := ENNReal.one_le_ofReal.2 h2
  exact (hsq_dField_le L a c).trans (le_mul_of_one_le_left zero_le h3)

/-! ### Banach-level derivative in d-coordinates -/

/-- Multiplier from the d-coordinates of `H^{a+1}` to those of `H^a`:
`pw_a/pw_{a+1} · i f = i f/(1+|f|)`. Independent of `a` (it is the same formula for every `a`). -/
def derSymb (L : ℝ) (k : ℤ) : ℂ := dSymb L k / ((1 + |freq L k| : ℝ) : ℂ)

theorem norm_derSymb_le (L : ℝ) (k : ℤ) : ‖derSymb L k‖ ≤ 1 := by
  unfold derSymb
  rw [norm_div, norm_dSymb, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity), one_mul]
  linarith [abs_nonneg (freq L k)]

def derFun (L : ℝ) (x : Ell2) : ℤ → ℂ := fun k => derSymb L k * x k

theorem mem_derFun (L : ℝ) (x : Ell2) : Memℓp (derFun L x) 2 := by
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (summable_sq x)
  show ‖derSymb L k * x k‖ ^ 2 ≤ ‖x k‖ ^ 2
  have h : ‖derSymb L k * x k‖ ≤ ‖x k‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_derSymb_le L k)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The derivative on the d-coordinate Banach space. -/
def derEll (L : ℝ) (x : Ell2) : Ell2 := ⟨derFun L x, mem_derFun L x⟩

theorem derEll_add (L : ℝ) (x y : Ell2) : derEll L (x + y) = derEll L x + derEll L y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  show derSymb L k * (x k + y k) = derSymb L k * x k + derSymb L k * y k
  ring

theorem derEll_smul (L : ℝ) (r : ℂ) (x : Ell2) : derEll L (r • x) = r • derEll L x := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show derSymb L k * (r * x k) = r * (derSymb L k * x k)
  ring

theorem norm_derEll_le (L : ℝ) (x : Ell2) : ‖derEll L x‖ ≤ ‖x‖ := by
  have h := norm_le_of_pointwise (x := x) (y := derEll L x) (C := 1) zero_le_one
    (fun k => by
      rw [one_mul]
      show ‖derSymb L k * x k‖ ≤ ‖x k‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_derSymb_le L k))
  rwa [one_mul] at h

/-- The derivative as a continuous linear map of the d-coordinate Banach space, norm at most `1`. -/
def derCLM (L : ℝ) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := fun x => derEll L x
      map_add' := fun x y => derEll_add L x y
      map_smul' := fun r x => derEll_smul L r x }
    1
    (fun x => by
      rw [one_mul]
      exact norm_derEll_le L x)

theorem pw_succ (L a : ℝ) (k : ℤ) : pw L (a + 1) k = pw L a k * (1 + |freq L k|) := by
  unfold pw
  have hb : (1 + |freq L k|) ≠ 0 := by positivity
  exact Real.rpow_add_one hb a

/-- Physical identity: the H^a field of `∂x x` is `∂` of the H^{a+1} field of `x`. -/
theorem toField_derEll (L a : ℝ) (x : Ell2) :
    toField L a (derEll L x) = dField L (toField L (a + 1) x) := by
  funext k
  show derSymb L k * x k / ((pw L a k : ℝ) : ℂ)
    = dSymb L k * (x k / ((pw L (a + 1) k : ℝ) : ℂ))
  unfold derSymb
  rw [pw_succ, Complex.ofReal_mul]
  ring

/-- The H^a norm of `∂x` (d-coordinates of `H^a`) is bounded by the H^{a+1} norm of `x`. -/
theorem hsq_derEll_le (L a : ℝ) (x : Ell2) :
    hsq L a (toField L a (derEll L x)) ≤ hsq L (a + 1) (toField L (a + 1) x) := by
  rw [toField_derEll]
  exact hsq_dField_le L a _

/-- Banach-level form: `‖derCLM x‖ ≤ ‖x‖`, the d-coordinate statement of the same bound. -/
theorem norm_derCLM_le (L : ℝ) (x : Ell2) : ‖derCLM L x‖ ≤ ‖x‖ :=
  norm_derEll_le L x

end QuantumNLS.RiccatiDerivative

#print axioms QuantumNLS.RiccatiDerivative.hsq_dField_le
#print axioms QuantumNLS.RiccatiDerivative.hsq_dField_le_scaled
#print axioms QuantumNLS.RiccatiDerivative.norm_derCLM_le
#print axioms QuantumNLS.RiccatiDerivative.toField_derEll
#print axioms QuantumNLS.RiccatiDerivative.hsq_derEll_le
