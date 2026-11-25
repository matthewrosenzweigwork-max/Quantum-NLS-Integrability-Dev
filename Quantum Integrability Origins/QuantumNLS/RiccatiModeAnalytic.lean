import Mathlib
import QuantumNLS.RiccatiCoeffAnalytic
import QuantumNLS.RiccatiValueBounds
import QuantumNLS.RiccatiPointwiseDisc

/-!
# R-3FEAD88B blocker (2): analyticity of the mode coefficients and of the trace logarithm

* `modeCoefCLM`: the Floquet mode integral `(f, w) ↦ ∫₀ᴸ physRep f · physRep w` as a continuous
  bilinear map `Ell2 →L Ell2 →L ℂ` (bound from the frozen `norm_modeCoef_le`).
* `modeCoef_analyticAt`: `p ↦ modeCoef (g p) (h p)` is analytic wherever `g` and `h` are.
* `logTrace_analyticAt`: on the sector `‖p.i‖ < B`, the principal logarithm of the discriminant equals
  `logS κ z (modeCoef (lowT p.2) (rfG p))` (frozen `logTrace_eq_logS`), which is analytic in `p`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex

namespace QuantumNLS.RiccatiModeAnalytic

open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiGlobal QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiCoeffAnalytic
open QuantumNLS.SmoothScalarMomentsPrerequisite

/-! ### 1. The mode integral as a continuous bilinear map -/

theorem modeCoef_add_left {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (x x' y : Ell2) :
    modeCoef L a (x + x') y = modeCoef L a x y + modeCoef L a x' y := by
  unfold modeCoef
  rw [physRep_add hL ha]
  have hc1 : Continuous (fun s => physRep L a x s * physRep L a y s) :=
    (physRep_continuous L ha x).mul (physRep_continuous L ha y)
  have hc2 : Continuous (fun s => physRep L a x' s * physRep L a y s) :=
    (physRep_continuous L ha x').mul (physRep_continuous L ha y)
  simp only [Pi.add_apply, add_mul]
  exact intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)

theorem modeCoef_add_right {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (x y y' : Ell2) :
    modeCoef L a x (y + y') = modeCoef L a x y + modeCoef L a x y' := by
  unfold modeCoef
  rw [physRep_add hL ha]
  have hc1 : Continuous (fun s => physRep L a x s * physRep L a y s) :=
    (physRep_continuous L ha x).mul (physRep_continuous L ha y)
  have hc2 : Continuous (fun s => physRep L a x s * physRep L a y' s) :=
    (physRep_continuous L ha x).mul (physRep_continuous L ha y')
  simp only [Pi.add_apply, mul_add]
  exact intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)

theorem modeCoef_smul_left {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (c : ℂ) (x y : Ell2) :
    modeCoef L a (c • x) y = c • modeCoef L a x y := by
  unfold modeCoef
  rw [physRep_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul c _

theorem modeCoef_smul_right {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (c : ℂ) (x y : Ell2) :
    modeCoef L a x (c • y) = c • modeCoef L a x y := by
  unfold modeCoef
  rw [physRep_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hfun : ∀ s, physRep L a x s * (c * physRep L a y s)
      = c * (physRep L a x s * physRep L a y s) := fun s => by ring
  simp only [hfun]
  exact intervalIntegral.integral_const_mul c _

/-- The mode integral as a bilinear map. -/
def modeCoefLin {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a) :
    Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (modeCoef L a)
    (fun x x' y => modeCoef_add_left hL ha x x' y)
    (fun r x y => modeCoef_smul_left hL ha r x y)
    (fun x y y' => modeCoef_add_right hL ha x y y')
    (fun r x y => modeCoef_smul_right hL ha r x y)

/-- The mode integral as a continuous bilinear map, with the frozen bound. -/
def modeCoefCLM {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a) :
    Ell2 →L[ℂ] Ell2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ (modeCoefLin hL ha) (L * physK L a * physK L a) (fun f w => by
    have h := QuantumNLS.RiccatiValueBounds.norm_modeCoef_le hL ha f w
    have e : L * ((physK L a * ‖f‖) * (physK L a * ‖w‖))
        = L * physK L a * physK L a * ‖f‖ * ‖w‖ := by ring
    rw [e] at h
    exact h)

theorem modeCoefCLM_apply {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (f w : Ell2) : modeCoefCLM hL ha f w = modeCoef L a f w := rfl

/-- Analyticity of `p ↦ modeCoef (g p) (h p)` from analyticity of the two arguments. -/
theorem modeCoef_analyticAt {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    {g h : Ell2 × Ell2 → Ell2} {p0 : Ell2 × Ell2} (hg : AnalyticAt ℂ g p0)
    (hh : AnalyticAt ℂ h p0) :
    AnalyticAt ℂ (fun q => modeCoef L a (g q) (h q)) p0 := by
  have h2 : AnalyticAt ℂ (fun q => (modeCoefCLM hL ha) (g q) (h q)) p0 :=
    ((ContinuousLinearMap.analyticAt_bilinear (modeCoefCLM hL ha) (g p0, h p0)).comp₂ hg hh)
  have hfun : (fun q => modeCoef L a (g q) (h q))
      = fun q => (modeCoefCLM hL ha) (g q) (h q) := funext fun q => rfl
  rw [hfun]
  exact h2

/-! ### 2. The logarithm `logS` and the sector bound -/

/-- If `|κ w| ≤ 1/8` and `L Im z ≥ 8 + 1/4`, then `1 + exp(izL − 2κw)` lies in the slit plane. -/
theorem one_add_exp_mem_slit (L κ : ℝ) (z w : ℂ) (hLIm : 8 + 1 / 4 ≤ L * z.im)
    (hw : ‖(κ : ℂ) * w‖ ≤ 1 / 8) :
    (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * w)) ∈ Complex.slitPlane := by
  have hcn : ‖2 * (κ : ℂ) * w‖ ≤ 1 / 4 := by
    rw [show (2 : ℂ) * (κ : ℂ) * w = 2 * ((κ : ℂ) * w) by ring, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  have hA : (Complex.I * z * (L : ℂ)).re = -(z.im * L) := by
    simp [Complex.mul_re]
  have hre : (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * w).re ≤ -8 := by
    rw [Complex.sub_re, hA]
    have h := Complex.abs_re_le_norm (2 * (κ : ℂ) * w)
    have h' := (abs_le.mp h).1
    nlinarith
  have hexp8 : Real.exp (-8) ≤ 1 / 2 := by
    have h1 : (8 : ℝ) + 1 ≤ Real.exp 8 := by
      have := Real.add_one_le_exp (8 : ℝ)
      linarith
    have h2 : Real.exp (-8) * Real.exp 8 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 := Real.exp_pos (-8)
    nlinarith
  have hnorm : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * w)‖ ≤ 1 / 2 := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hre).trans hexp8
  rw [Complex.mem_slitPlane_iff]
  left
  rw [Complex.add_re, Complex.one_re]
  have h := Complex.abs_re_le_norm (Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * w))
  have h' := (abs_le.mp h).1
  linarith

/-- `logS` is analytic where its argument stays in the slit region. -/
theorem logS_analyticAt (L κ : ℝ) (z : ℂ) {J : Ell2 × Ell2 → ℂ} {p0 : Ell2 × Ell2}
    (hJ : AnalyticAt ℂ J p0)
    (hs : 1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J p0) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun q => logS L κ z (J q)) p0 := by
  have hc1 : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => Complex.I * z * (L : ℂ)) p0 := analyticAt_const
  have hc2 : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => 2 * (κ : ℂ)) p0 := analyticAt_const
  have hk : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => (κ : ℂ)) p0 := analyticAt_const
  have hEarg : AnalyticAt ℂ (fun q => Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J q) p0 :=
    hc1.sub (hc2.mul hJ)
  have hE : AnalyticAt ℂ (fun q => 1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J q)) p0 :=
    analyticAt_const.add hEarg.cexp
  have hlog := hE.clog hs
  have hk' : AnalyticAt ℂ (fun q => (κ : ℂ) * J q) p0 := hk.mul hJ
  unfold logS
  exact hk'.add hlog

/-! ### 3. The mode bound on the sector and the analytic trace -/

theorem modeCoef_bound {L a S : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (haS : a ≤ S) {κ βu B : ℝ}
    (hB : 0 < B) (hBu : B < βu) (hβu : 0 < βu) {z : ℂ} (hz : 0 < z.im)
    (hκ : 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2) {p : Ell2 × Ell2}
    (h1 : ‖p.1‖ ≤ B) (h2 : ‖p.2‖ ≤ B) :
    ‖modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p)‖
      ≤ L * ((physK L a * B) * (physK L a * (2 * B / z.im))) := by
  have hpK : 0 ≤ physK L a := physK_nonneg (by linarith)
  have hL0 : 0 ≤ L := hL.le
  have hlow : ‖lowT L a S p.2‖ ≤ B := (norm_lowT_le L a S p.2).trans h2
  have hr := (rfG_small_radius (S := S) hL ha hβu hz hκ hB hBu h1 h2).2
  refine (QuantumNLS.RiccatiValueBounds.norm_modeCoef_le hL ha _ _).trans ?_
  gcongr

theorem logTrace_analyticAt (L : ℝ) [Fact (0 < L)] {a S : ℝ} {M : ℕ} (hL : 0 < L)
    (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) {κ : ℝ} (hκ0 : 0 < κ)
    {B βu : ℝ} (hB : 0 < B) (hBu : B < βu) (hβu : 0 < βu)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ B δ ≤ ‖z‖)
    (hκ : 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    (hJ : κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im)))) ≤ 1 / 8)
    (hLIm : 8 + 1 / 4 ≤ L * z.im) {p0 : Ell2 × Ell2} (h1 : ‖p0.1‖ < B) (h2 : ‖p0.2‖ < B) :
    AnalyticAt ℂ (fun p : Ell2 × Ell2 => logTrace L a S κ ha z p) p0 := by
  have haS' : a ≤ S := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hUo : IsOpen {p : Ell2 × Ell2 | ‖p.1‖ < B ∧ ‖p.2‖ < B} :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have hmem : p0 ∈ {p : Ell2 × Ell2 | ‖p.1‖ < B ∧ ‖p.2‖ < B} := ⟨h1, h2⟩
  -- the value identity on the sector
  have hEq : ∀ p ∈ {p : Ell2 × Ell2 | ‖p.1‖ < B ∧ ‖p.2‖ < B},
      logS L κ z (modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p))
        = logTrace L a S κ ha z p := by
    intro p hp
    have hp1 : ‖p.1‖ ≤ B := hp.1.le
    have hp2 : ‖p.2‖ ≤ B := hp.2.le
    have hr := rfG_small_radius (S := S) hL ha hβu hz hκ hB hBu hp1 hp2
    have hJκ : κ * ‖modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p)‖ ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (modeCoef_bound hL ha haS' hB hBu hβu hz hκ hp1 hp2)
        hκ0.le) (hJ.trans (by norm_num))
    exact (QuantumNLS.RiccatiValueBounds.logTrace_eq_logS (a := a) (S := S) (M := M) (L := L)
      hL ha haS hM κ hκ0 p.1 p.2 B hB hp1 hp2 D hD δ hδ z hz hsec hR
      (rfG hL ha S (κ / L) βu hβu z p) hr.1 hr.2 hJκ).symm
  -- analyticity of the mode coefficient along the sector
  have hlowan : AnalyticAt ℂ (fun p : Ell2 × Ell2 => lowT L a S p.2) p0 :=
    analyticAt_lowT_comp (L := L) (p := a) (q := S) haS'
      (g := ⇑(ContinuousLinearMap.snd ℂ Ell2 Ell2))
      ((ContinuousLinearMap.snd ℂ Ell2 Ell2).analyticAt p0)
  have hrfan : AnalyticAt ℂ (fun p : Ell2 × Ell2 => rfG hL ha S (κ / L) βu hβu z p) p0 :=
    rfG_analyticOnNhd hL ha haS' hβu hz hκ p0 ⟨lt_trans h1 hBu, lt_trans h2 hBu⟩
  have hJan : AnalyticAt ℂ (fun p : Ell2 × Ell2 =>
      modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p)) p0 :=
    modeCoef_analyticAt hL ha hlowan hrfan
  -- the slit condition at p0
  have hs : 1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ)
      * modeCoef L a (lowT L a S p0.2) (rfG hL ha S (κ / L) βu hβu z p0)) ∈ Complex.slitPlane := by
    apply one_add_exp_mem_slit L κ z _ hLIm
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0.le]
    have hp1 : ‖p0.1‖ ≤ B := h1.le
    have hp2 : ‖p0.2‖ ≤ B := h2.le
    exact le_trans (mul_le_mul_of_nonneg_left
      (modeCoef_bound hL ha haS' hB hBu hβu hz hκ hp1 hp2) hκ0.le) hJ
  have hLS := logS_analyticAt L κ z hJan hs
  exact hLS.congr (Filter.eventually_of_mem (hUo.mem_nhds hmem) (fun p hp => hEq p hp))

end QuantumNLS.RiccatiModeAnalytic
