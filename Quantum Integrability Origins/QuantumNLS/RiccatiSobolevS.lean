import Mathlib
import QuantumNLS.RiccatiSobolevBanach

/-!
# R-3FEAD88B stage E4-0: the H^S model and the continuous inclusion H^S → H^a

Source (`source/chapters/foundations/riccati_expansion.tex`, Prop `values:prop:riccati`): the parameters
range over an `H^S × H^S` neighbourhood with `S > a + M + 2`. Convention (DEF-002, `definitions.tex:15`):
`H^s` has squared norm `hsq L s c = ∑_k wt_s(k) |c_k|²`, `wt_s(k) = pw_s(k)²`, `pw_s(k) = (1+|2πk/L|)^s`.

Model. The H^S space is the same Banach space `Ell2` (weighted `ℓ²` in d-coordinates, from E3-pre) read with
the weight `pw_S`: the identification is `toField L S`, `x ↦ (x_k / pw_S(k))_k`. Every E3-pre statement holds with
`a := S` (`hsq_toField`, `mulBil`, `ropCLM`). The name `Ell2S` below is an abbreviation for that same normed space;
it is not a second type, and the H^S norm of a point `x` is `hsq L S (toField L S x)` = `ofReal ‖x‖²`.

Proved here, for `a ≤ S`:
* `iotaEll` / `iotaCLM`: the diagonal map with multiplier `pw_a / pw_S ∈ (0, 1]` (d-coordinates).
* `toField_iota`: `toField L a (iota x) = toField L S x` (same Fourier coefficients: the inclusion is the identity
  on the physical field).
* `norm_iotaEll_le`: `‖iota x‖ ≤ ‖x‖`, i.e. `‖·‖_{H^a} ≤ ‖·‖_{H^S}` on the common field.
* `hsq_mono`, `hsq_iota_le`: DEF-002 comparison `hsq L a c ≤ hsq L S c`.
* `iotaCLM_analyticAt`, `comp_iota_analyticAt`: composition with the continuous inclusion preserves analyticity
  (this is the holomorphy transfer used for the `H^S` parameter neighbourhood).
* `norm_mulBilS_le`, `norm_ropCLM_S_le`: the E3-pre product and resolvent bounds with `a := S` (reuse).

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace QuantumNLS.RiccatiSobolevS

open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiSobolevBanach

/-- The H^S model: the Banach space `Ell2` read with the weight `pw_S` (identification `toField L S`). -/
abbrev Ell2S : Type := Ell2

/-- Fourier coefficients of a point of the H^S model. -/
def toFieldS (L S : ℝ) (x : Ell2S) : ℤ → ℂ := toField L S x

theorem hsq_toFieldS (L S : ℝ) (x : Ell2S) :
    hsq L S (toFieldS L S x) = ENNReal.ofReal (‖x‖ ^ 2) :=
  hsq_toField L S x

theorem pw_le_pw {L a S : ℝ} (haS : a ≤ S) (k : ℤ) : pw L a k ≤ pw L S k := by
  unfold pw
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (freq L k)]) haS

/-- Diagonal multiplier of the inclusion `H^S ⊂ H^a`: `pw_a / pw_S`. -/
def incMult (L a S : ℝ) (k : ℤ) : ℝ := pw L a k / pw L S k

theorem incMult_nonneg (L a S : ℝ) (k : ℤ) : 0 ≤ incMult L a S k :=
  div_nonneg (pw_pos L a k).le (pw_pos L S k).le

theorem incMult_le_one {L a S : ℝ} (haS : a ≤ S) (k : ℤ) : incMult L a S k ≤ 1 := by
  unfold incMult
  rw [div_le_iff₀ (pw_pos L S k), one_mul]
  exact pw_le_pw haS k

/-- Coordinates of the inclusion: `(ι x)_k = (pw_a/pw_S)(k) · x_k`. -/
def iotaFun (L a S : ℝ) (x : Ell2) : ℤ → ℂ :=
  fun k => ((incMult L a S k : ℝ) : ℂ) * x k

theorem norm_iotaFun_le {L a S : ℝ} (haS : a ≤ S) (x : Ell2) (k : ℤ) :
    ‖iotaFun L a S x k‖ ≤ ‖x k‖ := by
  show ‖((incMult L a S k : ℝ) : ℂ) * x k‖ ≤ ‖x k‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (incMult_nonneg L a S k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (incMult_le_one haS k)

theorem mem_iotaFun {L a S : ℝ} (haS : a ≤ S) (x : Ell2) : Memℓp (iotaFun L a S x) 2 := by
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_iotaFun_le haS x k) 2) (summable_sq x)

/-- The inclusion on the point level. -/
def iotaEll {L a S : ℝ} (haS : a ≤ S) (x : Ell2) : Ell2 := ⟨iotaFun L a S x, mem_iotaFun haS x⟩

theorem iotaEll_add {L a S : ℝ} (haS : a ≤ S) (x y : Ell2) :
    iotaEll (L := L) haS (x + y) = iotaEll (L := L) haS x + iotaEll (L := L) haS y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  show ((incMult L a S k : ℝ) : ℂ) * (x k + y k)
    = ((incMult L a S k : ℝ) : ℂ) * x k + ((incMult L a S k : ℝ) : ℂ) * y k
  ring

theorem iotaEll_smul {L a S : ℝ} (haS : a ≤ S) (r : ℂ) (x : Ell2) :
    iotaEll (L := L) haS (r • x) = r • iotaEll (L := L) haS x := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show ((incMult L a S k : ℝ) : ℂ) * (r * x k) = r * (((incMult L a S k : ℝ) : ℂ) * x k)
  ring

theorem norm_iotaEll_le {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    ‖iotaEll (L := L) haS x‖ ≤ ‖x‖ := by
  have h := norm_le_of_pointwise (x := x) (y := iotaEll (L := L) haS x) (C := 1) zero_le_one
    (fun k => by
      rw [one_mul]
      exact norm_iotaFun_le haS x k)
  rwa [one_mul] at h

/-- The inclusion `H^S → H^a` as a continuous linear map of the d-coordinate Banach space, norm at most `1`. -/
def iotaCLM (L a S : ℝ) (haS : a ≤ S) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := fun x => iotaEll (L := L) haS x
      map_add' := fun x y => iotaEll_add (L := L) haS x y
      map_smul' := fun r x => iotaEll_smul (L := L) haS r x }
    1
    (fun x => by
      rw [one_mul]
      exact norm_iotaEll_le (L := L) haS x)

theorem iotaCLM_apply {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    iotaCLM L a S haS x = iotaEll (L := L) haS x := rfl

theorem norm_iotaCLM_le {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    ‖iotaCLM L a S haS x‖ ≤ ‖x‖ :=
  norm_iotaEll_le (L := L) haS x

/-- The inclusion does not change the physical field: `toField_a (ι x) = toField_S x`. -/
theorem toField_iota {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    toField L a (iotaEll (L := L) haS x) = toField L S x := by
  funext k
  show ((incMult L a S k : ℝ) : ℂ) * x k / ((pw L a k : ℝ) : ℂ) = x k / ((pw L S k : ℝ) : ℂ)
  unfold incMult
  rw [Complex.ofReal_div]
  have h1 := pw_ne_zero L a k
  have h2 := pw_ne_zero L S k
  field_simp

theorem wt_le_wt {L a S : ℝ} (haS : a ≤ S) (k : ℤ) : wt L a k ≤ wt L S k := by
  unfold wt
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (freq L k)]) (by linarith)

/-- DEF-002 comparison: `‖c‖_{H^a} ≤ ‖c‖_{H^S}` for `a ≤ S`, on coefficient sequences (valued in `[0,∞]`). -/
theorem hsq_mono {L a S : ℝ} (haS : a ≤ S) (c : ℤ → ℂ) : hsq L a c ≤ hsq L S c := by
  unfold hsq
  exact ENNReal.tsum_le_tsum fun k =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (wt_le_wt haS k) (sq_nonneg _))

/-- The H^a norm of the inclusion of `x` is bounded by its H^S norm (the same physical field). -/
theorem hsq_iota_le {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    hsq L a (toField L a (iotaEll (L := L) haS x)) ≤ hsq L S (toField L S x) := by
  rw [hsq_toField, hsq_toField]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_iotaEll_le (L := L) haS x) 2)

/-- The inclusion is analytic (continuous linear). -/
theorem iotaCLM_analyticAt {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    AnalyticAt ℂ (iotaCLM L a S haS) x :=
  (iotaCLM L a S haS).analyticAt x

/-- Holomorphy transfer: a map analytic at the image of `x` under the inclusion stays analytic after composition. -/
theorem comp_iota_analyticAt {L a S : ℝ} (haS : a ≤ S) {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {g : Ell2 → X} {x : Ell2} (hg : AnalyticAt ℂ g (iotaCLM L a S haS x)) :
    AnalyticAt ℂ (fun y => g (iotaCLM L a S haS y)) x :=
  hg.comp (iotaCLM_analyticAt haS x)

/-- Reuse of E3-pre with `a := S`: the product on the H^S model is bounded by `Cmul L S`. -/
theorem norm_mulBilS_le {L S : ℝ} (hL : 0 < L) (hS : 1 / 2 < S) (x y : Ell2) :
    ‖mulBil hL hS x y‖ ≤ Cmul L S * ‖x‖ * ‖y‖ :=
  norm_mulBil_le hL hS x y

/-- Reuse of E3-pre with `a := S`: the resolvent on the H^S model has norm at most `(Im z)⁻¹`. -/
theorem norm_ropCLM_S_le (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) :
    ‖ropCLM L z hz x‖ ≤ z.im⁻¹ * ‖x‖ :=
  norm_ropCLM_le L z hz x

end QuantumNLS.RiccatiSobolevS

#print axioms QuantumNLS.RiccatiSobolevS.iotaCLM_apply
#print axioms QuantumNLS.RiccatiSobolevS.toField_iota
#print axioms QuantumNLS.RiccatiSobolevS.hsq_iota_le
#print axioms QuantumNLS.RiccatiSobolevS.comp_iota_analyticAt
#print axioms QuantumNLS.RiccatiSobolevS.norm_mulBilS_le
#print axioms QuantumNLS.RiccatiSobolevS.norm_ropCLM_S_le
