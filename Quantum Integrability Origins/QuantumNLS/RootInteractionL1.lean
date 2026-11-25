import Mathlib
import QuantumNLS.L1Stability
import QuantumNLS.RootDiscriminantL1
import QuantumNLS.RootDiscriminantContinuity

/-!
# R-7E0532E7: interaction picture for `L¹` profiles and complex spectral parameter

For `κ > 0`, `z ∈ ℂ` and a profile `v` that is interval integrable on `[0,L]` (every `L²(𝕋_L)` class), with
`M = TT κ v z = L1SpatialTransfer.transfer (balCoef κ v z)`:

* `Dc z x = diag(e^{izx/2}, e^{-izx/2})`, `Bc κ v z x = [[0, √κ v̄ e^{izx}],[√κ v e^{-izx}, 0]]`.
* `Nc_eq_transfer_cont`: for CONTINUOUS `v`, `Dc z x · M(x) = transfer(Bc κ v z)(x)` on `[0,L]` (classical product rule,
  `hasDerivAt_Nc`, and uniqueness `L2SpatialTransfer.transfer_eq_classical`).
* `exists_continuous_approx`: a continuous `w` with `∫₀ᴸ‖v - w‖ ≤ ε` (mathlib's `Integrable.exists_hasCompactSupport_integral_sub_le`).
* `norm_TT_sub_le`, `norm_transfer_Bc_sub_le`: `L¹`-Lipschitz estimates from `L1Stability.norm_transfer_sub_le`.
* **`Nc_eq_transfer`**: the identity extends to all interval-integrable `v` by approximation (both sides are continuous in the
  `L¹` norm); no absolute-continuity product rule is used.
* `trace_TT_eq`: `tr M(L) = e^{-izL/2} (N₀₀ + e^{izL} N₁₁)` with `N = transfer(Bc κ v z)(L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.LinearFundamental
open QuantumNLS.RootDiscriminantBound (P1 P2 norm_le_of_row_sums row_sum_le_norm norm_one_mat2_le)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance instPseudoMetrizableMat2RIL1 : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENormedAddMonoidMat2RIL1 : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RootInteractionL1

open QuantumNLS.RootDiscriminantL1 (TT intervalIntegrable_balCoef)

/-! ### The interaction-picture objects, complex `z` -/

def a1c (z : ℂ) : ℂ := Complex.I * z / 2
def E1c (z : ℂ) (x : ℝ) : ℂ := Complex.exp (a1c z * x)
def E2c (z : ℂ) (x : ℝ) : ℂ := Complex.exp (-(a1c z * x))

theorem E1c_mul_E2c (z : ℂ) (x : ℝ) : E1c z x * E2c z x = 1 := by
  unfold E1c E2c; rw [← Complex.exp_add]; simp

theorem norm_E1c (z : ℂ) (x : ℝ) : ‖E1c z x‖ = Real.exp (-(z.im * x / 2)) := by
  unfold E1c a1c; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]; ring

theorem norm_E2c (z : ℂ) (x : ℝ) : ‖E2c z x‖ = Real.exp (z.im * x / 2) := by
  unfold E2c a1c; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]; ring

def Dc (z : ℂ) (x : ℝ) : Mat2 := E1c z x • P1 + E2c z x • P2

def Bc (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (x : ℝ) : Mat2 :=
  !![0, (Real.sqrt κ : ℂ) * conj (v x) * (E1c z x * E1c z x);
     (Real.sqrt κ : ℂ) * v x * (E2c z x * E2c z x), 0]

theorem norm_E1c_sq_le (z : ℂ) {L x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖E1c z x * E1c z x‖ ≤ Real.exp (|z.im| * L) := by
  rw [norm_mul, norm_E1c, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : -(z.im * x) ≤ |z.im| * L := by
    calc -(z.im * x) = (-z.im) * x := by ring
      _ ≤ |z.im| * x := mul_le_mul_of_nonneg_right (neg_le_abs _) hx.1
      _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
  linarith

theorem norm_E2c_sq_le (z : ℂ) {L x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖E2c z x * E2c z x‖ ≤ Real.exp (|z.im| * L) := by
  rw [norm_mul, norm_E2c, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : z.im * x ≤ |z.im| * L := by
    calc z.im * x ≤ |z.im| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx.1
      _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
  linarith

theorem norm_offdiag_le (a b : ℂ) {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hC : 0 ≤ C) :
    ‖(!![0, a; b, 0] : Mat2)‖ ≤ C := by
  refine norm_le_of_row_sums _ hC (fun i => ?_)
  fin_cases i <;> simp [ha, hb]

theorem norm_Bc_le (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) {L x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖Bc κ v z x‖ ≤ Real.sqrt κ * ‖v x‖ * Real.exp (|z.im| * L) := by
  have hs : ‖((Real.sqrt κ : ℝ) : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := norm_E1c_sq_le z hx
  have h2 := norm_E2c_sq_le z hx
  have hp : 0 ≤ Real.sqrt κ * ‖v x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hC : 0 ≤ Real.sqrt κ * ‖v x‖ * Real.exp (|z.im| * L) := by positivity
  refine norm_offdiag_le _ _ ?_ ?_ hC
  · rw [norm_mul, norm_mul, hs, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left h1 hp
  · rw [norm_mul, norm_mul, hs]
    exact mul_le_mul_of_nonneg_left h2 hp

theorem Bc_sub (κ : ℝ) (v w : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    Bc κ v z x - Bc κ w z x = Bc κ (fun s => v s - w s) z x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Bc] <;> ring

theorem norm_balCoef_sub_le (κ : ℝ) (v w : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ‖balCoef κ v z x - balCoef κ w z x‖ ≤ Real.sqrt κ * ‖v x - w x‖ := by
  have hs : ‖((Real.sqrt κ : ℝ) : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have e : balCoef κ v z x - balCoef κ w z x =
      !![0, (Real.sqrt κ : ℂ) * conj (v x - w x); (Real.sqrt κ : ℂ) * (v x - w x), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [balCoef, coef] <;> ring
  rw [e]
  have hp : 0 ≤ Real.sqrt κ * ‖v x - w x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  refine norm_offdiag_le _ _ ?_ ?_ hp
  · rw [norm_mul, hs, Complex.norm_conj]
  · rw [norm_mul, hs]

theorem norm_balCoef_le' (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ‖balCoef κ v z x‖ ≤ ‖z‖ / 2 + Real.sqrt κ * ‖v x‖ :=
  QuantumNLS.RootDiscriminantContinuity.norm_balCoef_le κ v z x

/-! ### Derivatives (classical product rule) -/

theorem hasDerivAt_E1c (z : ℂ) (x : ℝ) : HasDerivAt (E1c z) (a1c z * E1c z x) x := by
  have h : HasDerivAt (E1c z) _ x := ((hasDerivAt_id x).ofReal_comp.const_mul (a1c z)).cexp
  refine h.congr_deriv ?_
  simp [E1c]; ring

theorem hasDerivAt_E2c (z : ℂ) (x : ℝ) : HasDerivAt (E2c z) (-(a1c z) * E2c z x) x := by
  have h : HasDerivAt (E2c z) _ x := ((hasDerivAt_id x).ofReal_comp.const_mul (a1c z)).neg.cexp
  refine h.congr_deriv ?_
  simp [E2c]; ring

theorem hasDerivAt_Dc (z : ℂ) (x : ℝ) :
    HasDerivAt (Dc z) ((a1c z * E1c z x) • P1 + (-(a1c z) * E2c z x) • P2) x :=
  ((hasDerivAt_E1c z x).smul_const P1).add ((hasDerivAt_E2c z x).smul_const P2)

theorem hasDerivAt_Nc (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) {M : ℝ → Mat2}
    (hM : IsFundamental (balCoef κ v z) M) (x : ℝ) :
    HasDerivAt (fun y => Dc z y * M y) (Bc κ v z x * (Dc z x * M x)) x := by
  have h := (hasDerivAt_Dc z x).mul (hM.2 x)
  refine h.congr_deriv ?_
  have hE : E1c z x * E2c z x = 1 := E1c_mul_E2c z x
  have hE2 : E2c z x = (E1c z x)⁻¹ := eq_inv_of_mul_eq_one_right hE
  have hne : E1c z x ≠ 0 := Complex.exp_ne_zero _
  have hdiff : ((a1c z * E1c z x) • P1 + (-(a1c z) * E2c z x) • P2) * M x +
      Dc z x * (balCoef κ v z x * M x) = Bc κ v z x * (Dc z x * M x) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dc, P1, P2, Bc, balCoef, coef, a1c, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.vecMul, dotProduct] <;>
      (rw [hE2]; field_simp; try ring)
  exact hdiff

theorem continuous_Bc (κ : ℝ) {v : ℝ → ℂ} (hv : Continuous v) (z : ℂ) : Continuous (Bc κ v z) := by
  unfold Bc
  refine continuous_matrix fun i j => ?_
  have h1 : Continuous (E1c z) := by unfold E1c; fun_prop
  have h2 : Continuous (E2c z) := by unfold E2c; fun_prop
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- Integrability of the interaction-picture coefficient for interval-integrable `v`. -/
theorem intervalIntegrable_Bc {L : ℝ} {v : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L) (κ : ℝ) (z : ℂ) :
    IntervalIntegrable (Bc κ v z) volume 0 L := by
  have hconj : IntervalIntegrable (fun x => conj (v x)) volume 0 L :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hv.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hv.2⟩
  have h1 : Continuous (E1c z) := by unfold E1c; fun_prop
  have h2 : Continuous (E2c z) := by unfold E2c; fun_prop
  let E : Mat2 := !![0, 1; 0, 0]
  let F : Mat2 := !![0, 0; 1, 0]
  have hh := (((hconj.mul_continuousOn (g := fun x => E1c z x * E1c z x) (h1.mul h1).continuousOn).const_mul
      ((Real.sqrt κ : ℝ) : ℂ)).smul_continuousOn (g := fun _ => E) continuousOn_const).add
    (((hv.mul_continuousOn (g := fun x => E2c z x * E2c z x) (h2.mul h2).continuousOn).const_mul
      ((Real.sqrt κ : ℝ) : ℂ)).smul_continuousOn (g := fun _ => F) continuousOn_const)
  have he : Bc κ v z = fun x =>
      (((Real.sqrt κ : ℝ) : ℂ) * (conj (v x) * (E1c z x * E1c z x))) • E +
        (((Real.sqrt κ : ℝ) : ℂ) * (v x * (E2c z x * E2c z x))) • F := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Bc, E, F] <;> ring
  rw [he]
  exact hh

/-! ### Continuous profiles -/

theorem Nc_eq_transfer_cont {L : ℝ} (hL : 0 < L) {v : ℝ → ℂ} (hv : Continuous v) (κ : ℝ) (z : ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) :
    Dc z x * TT κ v z x = transfer (Bc κ v z) x := by
  have : Fact (0 < L) := ⟨hL⟩
  have hM := spatialTransfer_spec' κ hv z
  have hfro : TT κ v z x = SpatialTransfer.spatialTransfer κ v z x :=
    QuantumNLS.L2SpatialTransfer.transfer_eq_frozen κ hv z hx
  have hN0 : Dc z 0 * SpatialTransfer.spatialTransfer κ v z 0 = 1 := by
    rw [hM.1, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dc, E1c, E2c, P1, P2]
  have hNd : ∀ y, HasDerivAt (fun y => Dc z y * SpatialTransfer.spatialTransfer κ v z y)
      (Bc κ v z y * (Dc z y * SpatialTransfer.spatialTransfer κ v z y)) y := fun y => hasDerivAt_Nc κ v z hM y
  have hNf : IsFundamental (Bc κ v z) (fun y => Dc z y * SpatialTransfer.spatialTransfer κ v z y) := ⟨hN0, hNd⟩
  have := QuantumNLS.L2SpatialTransfer.transfer_eq_classical (continuous_Bc κ hv z) hNf hx
  rw [hfro]
  exact this.symm

/-! ### Approximation by continuous profiles -/

theorem exists_continuous_approx {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℝ → ℂ, Continuous w ∧ ∫ s in (0 : ℝ)..L, ‖v s - w s‖ ≤ ε := by
  have hint : Integrable ((Ioc (0 : ℝ) L).indicator v) volume :=
    (integrable_indicator_iff measurableSet_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).1 hv)
  obtain ⟨g, -, hg, hgc, hgi⟩ := hint.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨g, hgc, ?_⟩
  rw [intervalIntegral.integral_of_le hL]
  refine le_trans ?_ hg
  have hnn : 0 ≤ᵐ[volume] fun x => ‖(Ioc (0 : ℝ) L).indicator v x - g x‖ := ae_of_all _ fun x => norm_nonneg _
  have hfull : Integrable (fun x => ‖(Ioc (0 : ℝ) L).indicator v x - g x‖) volume := (hint.sub hgi).norm
  calc ∫ x in Ioc (0 : ℝ) L, ‖v x - g x‖ = ∫ x in Ioc (0 : ℝ) L, ‖(Ioc (0 : ℝ) L).indicator v x - g x‖ := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
        simp [Set.indicator_of_mem hx]
    _ ≤ ∫ x, ‖(Ioc (0 : ℝ) L).indicator v x - g x‖ :=
        setIntegral_le_integral hfull hnn

/-! ### `L¹`-Lipschitz estimates -/

/-- Stability in the form needed below: the three `L¹` quantities are bounded by `P, P', δ`. -/
theorem norm_transfer_sub_le_of {A A' : ℝ → Mat2} {L : ℝ} (hL : 0 ≤ L)
    (hA : IntervalIntegrable A volume 0 L) (hA' : IntervalIntegrable A' volume 0 L) {P P' δ : ℝ}
    (h1 : ∫ s in (0 : ℝ)..L, ‖A s‖ ≤ P) (h2 : ∫ s in (0 : ℝ)..L, ‖A' s‖ ≤ P')
    (h3 : ∫ s in (0 : ℝ)..L, ‖A s - A' s‖ ≤ δ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖transfer A x - transfer A' x‖ ≤ δ * (Real.exp P * Real.exp P') := by
  have h := QuantumNLS.L1Stability.norm_transfer_sub_le hL hA hA' hx
  have hδ0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖A s - A' s‖ := intervalIntegral.integral_nonneg hL (fun s _ => norm_nonneg _)
  have e1 : Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖) ≤ Real.exp P := Real.exp_le_exp.2 h1
  have e2 : Real.exp (∫ s in (0 : ℝ)..L, ‖A' s‖) ≤ Real.exp P' := Real.exp_le_exp.2 h2
  refine h.trans ?_
  have hone := norm_one_mat2_le
  have hδ : 0 ≤ δ := hδ0.trans h3
  have hA1 : ‖(1 : Mat2)‖ * Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖) ≤ 1 * Real.exp P :=
    mul_le_mul hone e1 (Real.exp_pos _).le zero_le_one
  have hB : (∫ s in (0 : ℝ)..L, ‖A s - A' s‖) * (‖(1 : Mat2)‖ * Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖)) ≤
      δ * (1 * Real.exp P) := mul_le_mul h3 hA1 (by positivity) hδ
  calc (∫ s in (0 : ℝ)..L, ‖A s - A' s‖) * (‖(1 : Mat2)‖ * Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖)) *
        Real.exp (∫ s in (0 : ℝ)..L, ‖A' s‖)
      ≤ δ * (1 * Real.exp P) * Real.exp P' :=
        mul_le_mul hB e2 (Real.exp_pos _).le (mul_nonneg hδ (by positivity))
    _ = δ * (Real.exp P * Real.exp P') := by ring

theorem integral_norm_balCoef_le {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    (κ : ℝ) (z : ℂ) :
    ∫ s in (0 : ℝ)..L, ‖balCoef κ v z s‖ ≤ L * (‖z‖ / 2) + Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s‖ := by
  have hA := (intervalIntegrable_balCoef hv κ z).norm
  have hR : IntervalIntegrable (fun s => ‖z‖ / 2 + Real.sqrt κ * ‖v s‖) volume 0 L :=
    intervalIntegrable_const.add (hv.norm.const_mul _)
  calc ∫ s in (0 : ℝ)..L, ‖balCoef κ v z s‖ ≤ ∫ s in (0 : ℝ)..L, (‖z‖ / 2 + Real.sqrt κ * ‖v s‖) :=
        intervalIntegral.integral_mono_on hL hA hR (fun s _ => norm_balCoef_le' κ v z s)
    _ = L * (‖z‖ / 2) + Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s‖ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hv.norm.const_mul _),
          intervalIntegral.integral_const_mul]
        simp
        ring

theorem integral_norm_balCoef_sub_le {L : ℝ} (hL : 0 ≤ L) {v w : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    (hw : IntervalIntegrable w volume 0 L) (κ : ℝ) (z : ℂ) :
    ∫ s in (0 : ℝ)..L, ‖balCoef κ v z s - balCoef κ w z s‖ ≤ Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s - w s‖ := by
  have hA := ((intervalIntegrable_balCoef hv κ z).sub (intervalIntegrable_balCoef hw κ z)).norm
  calc ∫ s in (0 : ℝ)..L, ‖balCoef κ v z s - balCoef κ w z s‖ ≤ ∫ s in (0 : ℝ)..L, Real.sqrt κ * ‖v s - w s‖ :=
        intervalIntegral.integral_mono_on hL hA ((hv.sub hw).norm.const_mul _) (fun s _ => norm_balCoef_sub_le κ v w z s)
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem integral_norm_Bc_le {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    (κ : ℝ) (z : ℂ) :
    ∫ s in (0 : ℝ)..L, ‖Bc κ v z s‖ ≤ Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖v s‖ := by
  have hA := (intervalIntegrable_Bc hv κ z).norm
  have hR : IntervalIntegrable (fun s => Real.sqrt κ * Real.exp (|z.im| * L) * ‖v s‖) volume 0 L :=
    hv.norm.const_mul _
  calc ∫ s in (0 : ℝ)..L, ‖Bc κ v z s‖ ≤ ∫ s in (0 : ℝ)..L, Real.sqrt κ * Real.exp (|z.im| * L) * ‖v s‖ := by
        refine intervalIntegral.integral_mono_on hL hA hR (fun s hs => ?_)
        have := norm_Bc_le κ v z (L := L) hs
        linarith [this, show Real.sqrt κ * ‖v s‖ * Real.exp (|z.im| * L) =
          Real.sqrt κ * Real.exp (|z.im| * L) * ‖v s‖ by ring]
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem integral_norm_Bc_sub_le {L : ℝ} (hL : 0 ≤ L) {v w : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    (hw : IntervalIntegrable w volume 0 L) (κ : ℝ) (z : ℂ) :
    ∫ s in (0 : ℝ)..L, ‖Bc κ v z s - Bc κ w z s‖ ≤
      Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖v s - w s‖ := by
  have hA := ((intervalIntegrable_Bc hv κ z).sub (intervalIntegrable_Bc hw κ z)).norm
  have hR : IntervalIntegrable (fun s => Real.sqrt κ * Real.exp (|z.im| * L) * ‖v s - w s‖) volume 0 L :=
    (hv.sub hw).norm.const_mul _
  calc ∫ s in (0 : ℝ)..L, ‖Bc κ v z s - Bc κ w z s‖ ≤
        ∫ s in (0 : ℝ)..L, Real.sqrt κ * Real.exp (|z.im| * L) * ‖v s - w s‖ := by
        refine intervalIntegral.integral_mono_on hL hA hR (fun s hs => ?_)
        rw [Bc_sub]
        have := norm_Bc_le κ (fun s => v s - w s) z (L := L) hs
        linarith [this, show Real.sqrt κ * ‖v s - w s‖ * Real.exp (|z.im| * L) =
          Real.sqrt κ * Real.exp (|z.im| * L) * ‖v s - w s‖ by ring]
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- **`L¹`-Lipschitz bound for the Carathéodory fundamental matrix.** -/
theorem norm_TT_sub_le {L : ℝ} (hL : 0 ≤ L) {v w : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    (hw : IntervalIntegrable w volume 0 L) (κ : ℝ) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖TT κ v z x - TT κ w z x‖ ≤
      (Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s - w s‖) *
        (Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s‖) *
          Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖w s‖)) :=
  norm_transfer_sub_le_of hL (intervalIntegrable_balCoef hv κ z) (intervalIntegrable_balCoef hw κ z)
    (integral_norm_balCoef_le hL hv κ z) (integral_norm_balCoef_le hL hw κ z)
    (integral_norm_balCoef_sub_le hL hv hw κ z) hx

/-- **`L¹`-Lipschitz bound for the interaction-picture transfer** (uniform for real `z`). -/
theorem norm_transfer_Bc_sub_le {L : ℝ} (hL : 0 ≤ L) {v w : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L)
    (hw : IntervalIntegrable w volume 0 L) (κ : ℝ) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖transfer (Bc κ v z) x - transfer (Bc κ w z) x‖ ≤
      (Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖v s - w s‖) *
        (Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖v s‖) *
          Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖w s‖)) :=
  norm_transfer_sub_le_of hL (intervalIntegrable_Bc hv κ z) (intervalIntegrable_Bc hw κ z)
    (integral_norm_Bc_le hL hv κ z) (integral_norm_Bc_le hL hw κ z)
    (integral_norm_Bc_sub_le hL hv hw κ z) hx

theorem norm_Dc_le (z : ℂ) {L x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) : ‖Dc z x‖ ≤ Real.exp (|z.im| * L / 2) := by
  have h1 : ‖E1c z x‖ ≤ Real.exp (|z.im| * L / 2) := by
    rw [norm_E1c]; apply Real.exp_le_exp.2
    have : -(z.im * x) ≤ |z.im| * L := by
      calc -(z.im * x) = (-z.im) * x := by ring
        _ ≤ |z.im| * x := mul_le_mul_of_nonneg_right (neg_le_abs _) hx.1
        _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
    linarith
  have h2 : ‖E2c z x‖ ≤ Real.exp (|z.im| * L / 2) := by
    rw [norm_E2c]; apply Real.exp_le_exp.2
    have : z.im * x ≤ |z.im| * L := by
      calc z.im * x ≤ |z.im| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx.1
        _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
    linarith
  have hC : 0 ≤ Real.exp (|z.im| * L / 2) := (Real.exp_pos _).le
  refine norm_le_of_row_sums _ hC (fun i => ?_)
  fin_cases i <;> simp [Dc, P1, P2, h1, h2]

/-! ### The identity for all interval-integrable profiles -/

theorem Nc_eq_transfer {L : ℝ} (hL : 0 < L) {v : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 L) (κ : ℝ) (z : ℂ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    Dc z x * TT κ v z x = transfer (Bc κ v z) x := by
  set V : ℝ := ∫ s in (0 : ℝ)..L, ‖v s‖ with hV
  have hV0 : 0 ≤ V := intervalIntegral.integral_nonneg hL.le (fun s _ => norm_nonneg _)
  -- constant independent of the approximant
  set K1 : ℝ := Real.sqrt κ * (Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * V) *
      Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * (V + 1))) with hK1
  set K2 : ℝ := Real.sqrt κ * Real.exp (|z.im| * L) * (Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * V) *
      Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * (V + 1))) with hK2
  set D : ℝ := Real.exp (|z.im| * L / 2) with hD
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖Dc z x * TT κ v z x - transfer (Bc κ v z) x‖ ≤ (D * K1 + K2) * ε := by
    intro ε hε hε1
    obtain ⟨w, hwc, hw⟩ := exists_continuous_approx hL.le hv hε
    have hwI : IntervalIntegrable w volume 0 L := hwc.intervalIntegrable 0 L
    have hδ0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖v s - w s‖ := intervalIntegral.integral_nonneg hL.le (fun s _ => norm_nonneg _)
    have hW : ∫ s in (0 : ℝ)..L, ‖w s‖ ≤ V + 1 := by
      have hle : ∫ s in (0 : ℝ)..L, ‖w s‖ ≤ ∫ s in (0 : ℝ)..L, (‖v s‖ + ‖v s - w s‖) :=
        intervalIntegral.integral_mono_on hL.le hwI.norm (hv.norm.add (hv.sub hwI).norm) (fun s _ => by
          have := norm_sub_norm_le (w s) (v s)
          have h' : ‖w s - v s‖ = ‖v s - w s‖ := norm_sub_rev _ _
          linarith)
      rw [intervalIntegral.integral_add hv.norm (hv.sub hwI).norm] at hle
      linarith
    have e1 := norm_TT_sub_le hL.le hv hwI κ z hx
    have e2 := norm_transfer_Bc_sub_le hL.le hv hwI κ z hx
    have hcont := Nc_eq_transfer_cont hL hwc κ z hx
    have hs0 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
    have e1' : ‖TT κ v z x - TT κ w z x‖ ≤ K1 * ε := by
      refine e1.trans ?_
      have hexp : Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖w s‖) ≤
          Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * (V + 1)) :=
        Real.exp_le_exp.2 (by nlinarith)
      have hpos : 0 ≤ Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * V) := (Real.exp_pos _).le
      calc (Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s - w s‖) *
            (Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * V) *
              Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖w s‖))
          ≤ (Real.sqrt κ * ε) * (Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * V) *
              Real.exp (L * (‖z‖ / 2) + Real.sqrt κ * (V + 1))) := by
            gcongr
        _ = K1 * ε := by rw [hK1]; ring
    have e2' : ‖transfer (Bc κ v z) x - transfer (Bc κ w z) x‖ ≤ K2 * ε := by
      refine e2.trans ?_
      have hc0 : 0 ≤ Real.sqrt κ * Real.exp (|z.im| * L) := by positivity
      have hexp : Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖w s‖) ≤
          Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * (V + 1)) :=
        Real.exp_le_exp.2 (by gcongr)
      calc (Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖v s - w s‖) *
            (Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * V) *
              Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * ∫ s in (0 : ℝ)..L, ‖w s‖))
          ≤ (Real.sqrt κ * Real.exp (|z.im| * L) * ε) * (Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * V) *
              Real.exp (Real.sqrt κ * Real.exp (|z.im| * L) * (V + 1))) := by
            gcongr
        _ = K2 * ε := by rw [hK2]; ring
    have hDn := norm_Dc_le z hx
    have hdiff : Dc z x * TT κ v z x - transfer (Bc κ v z) x =
        Dc z x * (TT κ v z x - TT κ w z x) - (transfer (Bc κ v z) x - transfer (Bc κ w z) x) := by
      rw [mul_sub, ← hcont]; abel
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    have h3 : ‖Dc z x * (TT κ v z x - TT κ w z x)‖ ≤ D * (K1 * ε) :=
      (norm_mul_le _ _).trans (mul_le_mul hDn e1' (norm_nonneg _) (Real.exp_pos _).le)
    linarith
  -- conclude
  have hz : ‖Dc z x * TT κ v z x - transfer (Bc κ v z) x‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hKpos : 0 ≤ D * K1 + K2 := by
      have : 0 ≤ K1 := by rw [hK1]; positivity
      have : 0 ≤ K2 := by rw [hK2]; positivity
      positivity
    set e : ℝ := min 1 (ε / (D * K1 + K2 + 1)) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have hb := hbound e he0 he1
    refine hb.trans ?_
    have : (D * K1 + K2) * e ≤ ε := by
      have h2 : e ≤ ε / (D * K1 + K2 + 1) := min_le_right _ _
      calc (D * K1 + K2) * e ≤ (D * K1 + K2 + 1) * e := by nlinarith
        _ ≤ (D * K1 + K2 + 1) * (ε / (D * K1 + K2 + 1)) := by gcongr
        _ = ε := by field_simp
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

end QuantumNLS.RootInteractionL1

#print axioms QuantumNLS.RootInteractionL1.hasDerivAt_Nc
#print axioms QuantumNLS.RootInteractionL1.intervalIntegrable_Bc
#print axioms QuantumNLS.RootInteractionL1.Nc_eq_transfer_cont
#print axioms QuantumNLS.RootInteractionL1.exists_continuous_approx
#print axioms QuantumNLS.RootInteractionL1.norm_TT_sub_le
#print axioms QuantumNLS.RootInteractionL1.norm_transfer_Bc_sub_le
#print axioms QuantumNLS.RootInteractionL1.Nc_eq_transfer
