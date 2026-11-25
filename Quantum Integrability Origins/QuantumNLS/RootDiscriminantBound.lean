import Mathlib
import QuantumNLS.RootDiscriminant
import QuantumNLS.L1SpatialTransfer

/-!
# R-7E0532E7: the real trace bound `|Δ_u(t)| ≤ 2 cosh(√κ ‖u‖_{L¹(0,L)})`

(`ROOT_spectral_density.tex`, "This also gives, for real `t`, `|Δ_u(t)| ≤ 2cosh(√κ‖u‖₁)`".)  Interaction picture:
for real `t`, `N(x) = diag(e^{itx/2}, e^{-itx/2}) M(x,t)` solves `N' = B N`, `B = [[0, √κ ū e^{itx}],[√κ u e^{-itx}, 0]]`,
`‖B(x)‖_∞ = √κ|u(x)|`; the L¹ Volterra series (`L1SpatialTransfer.transfer`, uniqueness `fundamental_spec`) gives
`‖N(L)‖ ≤ exp(√κ ∫₀ᴸ|u|)`, while `‖N(L)‖_∞ = |M₀₀| + |M₀₁|` and `|M₀₀|² - |M₀₁|² = 1` (RootDiscriminant), so
`|M₀₀| ≤ cosh(√κ ∫₀ᴸ|u|)` and `|Δ| = 2|Re M₀₀| ≤ 2cosh`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix NNReal
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental QuantumNLS.RootDiscriminant

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootDiscriminantBound

theorem row_sum_le_norm (m : Mat2) (i : Fin 2) : ‖m i 0‖ + ‖m i 1‖ ≤ ‖m‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i : Fin 2 => ∑ j : Fin 2, ‖m i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j : Fin 2, ‖m i j‖₊ : ℝ≥0) : ℝ) ≤
      ((Finset.univ.sup fun i : Fin 2 => ∑ j : Fin 2, ‖m i j‖₊ : ℝ≥0) : ℝ) := by exact_mod_cast h
  simpa [Fin.sum_univ_two] using h2

theorem norm_le_of_row_sums (m : Mat2) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖m i 0‖ + ‖m i 1‖ ≤ C) : ‖m‖ ≤ C := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : Fin 2 => ∑ j : Fin 2, ‖m i j‖₊) ≤ C.toNNReal := by
    refine Finset.sup_le fun i _ => ?_
    rw [← NNReal.coe_le_coe]
    simpa [Fin.sum_univ_two, Real.coe_toNNReal C hC] using h i
  have h2 := (NNReal.coe_le_coe.2 this)
  simpa [Real.coe_toNNReal C hC] using h2

section Interaction

variable (κ : ℝ) (u : ℝ → ℂ) (t : ℝ)

/-- `a₁ = i t/2`. -/
def a1 : ℂ := Complex.I * t / 2

def E1 (x : ℝ) : ℂ := Complex.exp (a1 t * x)
def E2 (x : ℝ) : ℂ := Complex.exp (-(a1 t * x))

theorem E1_mul_E2 (x : ℝ) : E1 t x * E2 t x = 1 := by
  unfold E1 E2; rw [← Complex.exp_add]; simp

theorem norm_E1 (x : ℝ) : ‖E1 t x‖ = 1 := by
  unfold E1 a1; rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im]

theorem norm_E2 (x : ℝ) : ‖E2 t x‖ = 1 := by
  unfold E2 a1; rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im]

def P1 : Mat2 := !![1, 0; 0, 0]
def P2 : Mat2 := !![0, 0; 0, 1]

/-- `D(x) = diag(e^{itx/2}, e^{-itx/2})`. -/
def Dm (x : ℝ) : Mat2 := E1 t x • P1 + E2 t x • P2

/-- `B(x) = [[0, √κ ū E1²],[√κ u E2², 0]]`. -/
def Bm (x : ℝ) : Mat2 :=
  !![0, (Real.sqrt κ : ℂ) * conj (u x) * (E1 t x * E1 t x); (Real.sqrt κ : ℂ) * u x * (E2 t x * E2 t x), 0]

theorem hasDerivAt_E1 (x : ℝ) : HasDerivAt (E1 t) (a1 t * E1 t x) x := by
  have h : HasDerivAt (E1 t) _ x := ((hasDerivAt_id x).ofReal_comp.const_mul (a1 t)).cexp
  refine h.congr_deriv ?_
  simp [E1]; ring

theorem hasDerivAt_E2 (x : ℝ) : HasDerivAt (E2 t) (-(a1 t) * E2 t x) x := by
  have h : HasDerivAt (E2 t) _ x := ((hasDerivAt_id x).ofReal_comp.const_mul (a1 t)).neg.cexp
  refine h.congr_deriv ?_
  simp [E2]; ring

theorem hasDerivAt_Dm (x : ℝ) :
    HasDerivAt (Dm t) ((a1 t * E1 t x) • P1 + (-(a1 t) * E2 t x) • P2) x :=
  ((hasDerivAt_E1 t x).smul_const P1).add ((hasDerivAt_E2 t x).smul_const P2)

/-- **`N = D M` solves `N' = B N`** for real `t`. -/
theorem hasDerivAt_N (hκ : 0 < κ) {M : ℝ → Mat2} (hM : IsFundamental (balCoef κ u (t : ℂ)) M) (x : ℝ) :
    HasDerivAt (fun y => Dm t y * M y) (Bm κ u t x * (Dm t x * M x)) x := by
  have h := (hasDerivAt_Dm t x).mul (hM.2 x)
  refine h.congr_deriv ?_
  have hE : E1 t x * E2 t x = 1 := E1_mul_E2 t x
  have hE2 : E2 t x = (E1 t x)⁻¹ := eq_inv_of_mul_eq_one_right hE
  have hne : E1 t x ≠ 0 := Complex.exp_ne_zero _
  have hdiff : ((a1 t * E1 t x) • P1 + (-(a1 t) * E2 t x) • P2) * M x + Dm t x * (balCoef κ u (t : ℂ) x * M x) =
      Bm κ u t x * (Dm t x * M x) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dm, P1, P2, Bm, balCoef, coef, a1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.vecMul, dotProduct] <;>
      (rw [hE2]; field_simp; try ring)
  exact hdiff

end Interaction

section Bound

variable (κ : ℝ) (u : ℝ → ℂ) (t : ℝ)

theorem norm_one_mat2_le : ‖(1 : Mat2)‖ ≤ 1 := by
  refine norm_le_of_row_sums _ zero_le_one (fun i => ?_)
  fin_cases i <;> simp [Matrix.one_apply]

theorem norm_Bm_le (x : ℝ) : ‖Bm κ u t x‖ ≤ Real.sqrt κ * ‖u x‖ := by
  have hs : ‖((Real.sqrt κ : ℝ) : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine norm_le_of_row_sums _ (by positivity) (fun i => ?_)
  have hs' : |Real.sqrt κ| = Real.sqrt κ := abs_of_nonneg (Real.sqrt_nonneg κ)
  fin_cases i <;> simp [Bm, norm_mul, norm_E1, norm_E2, hs, hs']

theorem continuous_Bm {u : ℝ → ℂ} (hu : Continuous u) : Continuous (Bm κ u t) := by
  unfold Bm
  refine continuous_matrix fun i j => ?_
  have h1 : Continuous (E1 t) := by unfold E1; fun_prop
  have h2 : Continuous (E2 t) := by unfold E2; fun_prop
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- **`|M₀₀(L,t)| + |M₀₁(L,t)| ≤ exp(√κ ∫₀ᴸ |u|)`** (interaction picture, Volterra series). -/
theorem norm_row_le (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) :
    ‖spatialTransfer κ u (t : ℂ) L 0 0‖ + ‖spatialTransfer κ u (t : ℂ) L 0 1‖ ≤
      Real.exp (Real.sqrt κ * ∫ x in (0 : ℝ)..L, ‖u x‖) := by
  have hM := spatialTransfer_spec' κ hu (t : ℂ)
  set M := spatialTransfer κ u (t : ℂ) with hMdef
  set N : ℝ → Mat2 := fun y => Dm t y * M y with hN
  have hBc := continuous_Bm κ t hu
  have hNd : ∀ y, HasDerivAt N (Bm κ u t y * N y) y := fun y => hasDerivAt_N κ u t hκ hM y
  have hNc : Continuous N := continuous_iff_continuousAt.2 fun y => (hNd y).continuousAt
  have hA := hBc.intervalIntegrable (μ := MeasureTheory.volume) 0 L
  have hN0 : N 0 = 1 := by
    simp only [hN, hM.1, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dm, E1, E2, P1, P2]
  have hint : ∀ x ∈ Set.Icc 0 L, N x = 1 + ∫ s in (0 : ℝ)..x, Bm κ u t s * N s := by
    intro x _
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hNd y)
      ((hBc.mul hNc).intervalIntegrable 0 x)
    rw [this, hN0]; abel
  have hEq := (QuantumNLS.L1SpatialTransfer.fundamental_spec hL hA).2.2.2 N hNc.continuousOn hint
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hNL : N L = QuantumNLS.L1SpatialTransfer.transfer (Bm κ u t) L := hEq hLmem
  obtain ⟨hsum, hb⟩ := QuantumNLS.L1SpatialTransfer.uniform_dyson_bound hL hA
  set I : ℝ := ∫ s in (0 : ℝ)..L, ‖Bm κ u t s‖ with hI
  have hnorm : ‖N L‖ ≤ Real.exp I := by
    rw [hNL]
    unfold QuantumNLS.L1SpatialTransfer.transfer
    have hs2 : Summable fun n : ℕ => ‖QuantumNLS.LinearFundamental.dyson (Bm κ u t) n L‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hb n L hLmem) hsum
    refine (norm_tsum_le_tsum_norm hs2).trans ?_
    have hexp : HasSum (fun n : ℕ => I ^ n / (n.factorial : ℝ)) (Real.exp I) := by
      have := NormedSpace.expSeries_div_hasSum_exp I
      rwa [← Real.exp_eq_exp_ℝ] at this
    calc ∑' n : ℕ, ‖QuantumNLS.LinearFundamental.dyson (Bm κ u t) n L‖
        ≤ ∑' n : ℕ, ‖(1 : Mat2)‖ * I ^ n / (n.factorial : ℝ) :=
          hs2.tsum_le_tsum (fun n => hb n L hLmem) hsum
      _ ≤ ∑' n : ℕ, I ^ n / (n.factorial : ℝ) := by
          refine hsum.tsum_le_tsum (fun n => ?_) hexp.summable
          have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hL (fun s _ => norm_nonneg _)
          have : 0 ≤ I ^ n / (n.factorial : ℝ) := by positivity
          calc ‖(1 : Mat2)‖ * I ^ n / (n.factorial : ℝ) = ‖(1 : Mat2)‖ * (I ^ n / (n.factorial : ℝ)) := by ring
            _ ≤ 1 * (I ^ n / (n.factorial : ℝ)) := mul_le_mul_of_nonneg_right norm_one_mat2_le this
            _ = _ := one_mul _
      _ = Real.exp I := hexp.tsum_eq
  have hI_le : I ≤ Real.sqrt κ * ∫ x in (0 : ℝ)..L, ‖u x‖ := by
    rw [hI, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hL (hBc.norm.intervalIntegrable _ _)
      ((hu.norm.const_mul _).intervalIntegrable _ _) (fun s _ => norm_Bm_le κ u t s)
  have hrow := row_sum_le_norm (N L) 0
  have hE : ‖E1 t L‖ = 1 := norm_E1 t L
  have hr : ‖N L 0 0‖ + ‖N L 0 1‖ = ‖M L 0 0‖ + ‖M L 0 1‖ := by
    simp [hN, Dm, P1, P2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, norm_mul, hE]
  rw [← hr]
  exact (hrow.trans hnorm).trans (Real.exp_le_exp.2 hI_le)

theorem cosh_bound_of {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 - b ^ 2 = 1) (h : a + b ≤ Real.exp c) :
    a ≤ Real.cosh c := by
  have ha1 : 1 ≤ a := by nlinarith
  set W := a + b with hW
  have hW1 : 1 ≤ W := by linarith
  have hWpos : 0 < W := by linarith
  have hEpos : 0 < Real.exp c := Real.exp_pos c
  have hdiff : a - b = W⁻¹ := by
    have h1 : (a - b) * W = 1 := by nlinarith
    exact eq_inv_of_mul_eq_one_left h1
  have ha2 : a = (W + W⁻¹) / 2 := by
    have : 2 * a = W + W⁻¹ := by rw [← hdiff, hW]; ring
    linarith
  have hEW : 1 ≤ Real.exp c * W := by nlinarith
  have hkey : W + W⁻¹ ≤ Real.exp c + (Real.exp c)⁻¹ := by
    rw [← sub_nonneg]
    have : Real.exp c + (Real.exp c)⁻¹ - (W + W⁻¹) = (Real.exp c - W) * (Real.exp c * W - 1) / (Real.exp c * W) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  rw [Real.cosh_eq, ha2]
  have : Real.exp (-c) = (Real.exp c)⁻¹ := Real.exp_neg c
  rw [this]
  linarith

variable {κ}

/-- **The real trace bound**: `|Δ_u(t)| ≤ 2cosh(√κ ∫₀ᴸ|u|)` for real `t`, `κ > 0`, continuous `u`. -/
theorem abs_discReal_le (L : ℝ) (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u) (hL : 0 ≤ L) (t : ℝ) :
    |discReal L κ u t| ≤ 2 * Real.cosh (Real.sqrt κ * ∫ x in (0 : ℝ)..L, ‖u x‖) := by
  have hrow := norm_row_le κ t hκ hu hL
  have hd := norm_sq_sub_eq_one κ hu t L
  have hp := cosh_bound_of (norm_nonneg _) (norm_nonneg _) hd hrow
  have hdisc : discReal L κ u t = 2 * (spatialTransfer κ u (t : ℂ) L 0 0).re := by
    have := discriminant_eq_two_re L κ hu t
    unfold discReal
    rw [this]; simp
  rw [hdisc, abs_mul, abs_two]
  have := Complex.abs_re_le_norm (spatialTransfer κ u (t : ℂ) L 0 0)
  linarith

end Bound

#print axioms abs_discReal_le
#print axioms norm_row_le

end QuantumNLS.RootDiscriminantBound
