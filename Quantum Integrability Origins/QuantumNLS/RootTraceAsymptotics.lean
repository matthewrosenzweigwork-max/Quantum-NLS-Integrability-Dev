import Mathlib
import QuantumNLS.RootDiscriminantContinuity

/-!
# R-7E0532E7: `Δ_u(t) - 2cos(tL/2) → 0` as `|t| → ∞` (eq:root-trace-asymptotic), continuous `u`

Route (interaction picture, no multidimensional Fourier analysis): with `N_t = diag(e^{itx/2},e^{-itx/2}) M_t`,
`N_t(L) = ∑_n dyson(B_t, n)(L)` (`B_t = [[0, √κ ū e^{itx}],[√κ u e^{-itx}, 0]]`) and `Δ_u(t) - 2cos(tL/2) =
E₂(L)(N₀₀-1) + E₁(L)(N₁₁-1)`.  Each Dyson term `n ≥ 1` tends to `0` pointwise in `x ∈ [0,L]`: `n = 1` is the scalar
Riemann-Lebesgue lemma `∫₀ˣ g e^{±its} ds → 0` (Mathlib `Real.tendsto_integral_exp_smul_cocompact`), and the step `n → n+1` is
dominated convergence in the outer integral (the outer factor is bounded by `√κ|u|`).  The uniform majorant `c^n/n!`
(`c = √κ∫₀ᴸ|u|`) and `tendsto_tsum_of_dominated_convergence` sum the series.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix NNReal FourierTransform Interval
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental QuantumNLS.RootDiscriminant
  QuantumNLS.RootDiscriminantBound

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootTraceAsymptotics

/-- Scalar Riemann-Lebesgue: `∫₀ˣ g(s) e^{i c t s} ds → 0` along `cocompact ℝ` (`c ≠ 0`, `x ≥ 0`). -/
theorem tendsto_osc (g : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..x, g s * Complex.exp (Complex.I * ((c * t : ℝ) : ℂ) * s))
      (cocompact ℝ) (𝓝 0) := by
  set f : ℝ → ℂ := (Ioc (0 : ℝ) x).indicator g with hf
  have hw : Tendsto (fun t : ℝ => -(c * t) / (2 * Real.pi)) (cocompact ℝ) (cocompact ℝ) := by
    have hc' : (-c / (2 * Real.pi)) ≠ 0 := by
      have := Real.pi_pos
      exact div_ne_zero (neg_ne_zero.2 hc) (by positivity)
    have := (Homeomorph.mulLeft₀ (-c / (2 * Real.pi)) hc').isClosedEmbedding.tendsto_cocompact
    refine this.congr (fun t => ?_)
    show (-c / (2 * Real.pi)) * t = -(c * t) / (2 * Real.pi)
    ring
  have key := (Real.tendsto_integral_exp_smul_cocompact f).comp hw
  refine key.congr (fun t => ?_)
  simp only [Function.comp]
  rw [intervalIntegral.integral_of_le hx, ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [hf, Set.indicator]
  split_ifs with hv
  · rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp
  · simp


section Dyson

variable (κ : ℝ) (u : ℝ → ℂ)

theorem E1_sq (t x : ℝ) : E1 t x * E1 t x = Complex.exp (Complex.I * ((1 * t : ℝ) : ℂ) * x) := by
  unfold E1 a1; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem E2_sq (t x : ℝ) : E2 t x * E2 t x = Complex.exp (Complex.I * ((-1 * t : ℝ) : ℂ) * x) := by
  unfold E2 a1; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem integral_entry {A : ℝ → Mat2} (hA : Continuous A) (x : ℝ) (i j : Fin 2) :
    (∫ s in (0 : ℝ)..x, A s) i j = ∫ s in (0 : ℝ)..x, A s i j := by
  have := ((entryCLM i j).restrictScalars ℝ).intervalIntegral_comp_comm (μ := volume) (a := 0) (b := x)
    (f := A) (hA.intervalIntegrable _ _)
  exact this.symm

variable {κ u}

/-- First Dyson term: `∫₀ˣ B_t → 0`. -/
theorem dyson_one_tendsto (hu : Continuous u) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun t : ℝ => dyson (Bm κ u t) 1 x) (cocompact ℝ) (𝓝 0) := by
  have hd : ∀ t, dyson (Bm κ u t) 1 x = ∫ s in (0 : ℝ)..x, Bm κ u t s := by
    intro t; simp [dyson]
  simp_rw [hd]
  have h01 : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..x, Bm κ u t s 0 1) (cocompact ℝ) (𝓝 0) := by
    have := tendsto_osc (fun s => (Real.sqrt κ : ℂ) * conj (u s)) hx (c := 1) one_ne_zero
    refine this.congr (fun t => ?_)
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [Bm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, E1_sq]
  have h10 : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..x, Bm κ u t s 1 0) (cocompact ℝ) (𝓝 0) := by
    have := tendsto_osc (fun s => (Real.sqrt κ : ℂ) * u s) hx (c := -1) (by norm_num)
    refine this.congr (fun t => ?_)
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [Bm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, E2_sq]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hn01 := (tendsto_zero_iff_norm_tendsto_zero.1 h01)
  have hn10 := (tendsto_zero_iff_norm_tendsto_zero.1 h10)
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using hn01.add hn10)
  have hBc := continuous_Bm κ t hu
  rw [sub_zero]
  refine norm_le_of_row_sums _ (by positivity) (fun i => ?_)
  rw [integral_entry hBc x i 0, integral_entry hBc x i 1]
  fin_cases i <;> simp [Bm]


/-- The uniform majorant `c = √κ ∫₀ᴸ |u|`. -/
def cC (κ : ℝ) (u : ℝ → ℂ) (L : ℝ) : ℝ := Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖u s‖

theorem cC_nonneg (κ : ℝ) (u : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ cC κ u L :=
  mul_nonneg (Real.sqrt_nonneg _) (intervalIntegral.integral_nonneg hL (fun s _ => norm_nonneg _))

theorem dyson_bound (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) (t : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖dyson (Bm κ u t) n x‖ ≤ cC κ u L ^ n / (n.factorial : ℝ) := by
  have hBc := continuous_Bm κ t hu
  have hA := hBc.intervalIntegrable (μ := volume) 0 L
  have h1 := QuantumNLS.L1SpatialTransfer.norm_dyson_le_control hL hA n x hx
  have hI : (∫ s in (0 : ℝ)..x, ‖Bm κ u t s‖) ≤ cC κ u L := by
    calc (∫ s in (0 : ℝ)..x, ‖Bm κ u t s‖) ≤ ∫ s in (0 : ℝ)..x, Real.sqrt κ * ‖u s‖ :=
          intervalIntegral.integral_mono_on hx.1 (hBc.norm.intervalIntegrable _ _)
            ((hu.norm.const_mul _).intervalIntegrable _ _) (fun s _ => norm_Bm_le κ u t s)
      _ = Real.sqrt κ * ∫ s in (0 : ℝ)..x, ‖u s‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ cC κ u L := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2 (ae_of_all _ fun s => norm_nonneg _)
            (hu.norm.intervalIntegrable _ _)
  have hI0 : 0 ≤ ∫ s in (0 : ℝ)..x, ‖Bm κ u t s‖ := intervalIntegral.integral_nonneg hx.1 (fun s _ => norm_nonneg _)
  refine h1.trans ?_
  have : (∫ s in (0 : ℝ)..x, ‖Bm κ u t s‖) ^ n ≤ cC κ u L ^ n := pow_le_pow_left₀ hI0 hI n
  calc ‖(1 : Mat2)‖ * (∫ s in (0 : ℝ)..x, ‖Bm κ u t s‖) ^ n / (n.factorial : ℝ)
      ≤ 1 * cC κ u L ^ n / (n.factorial : ℝ) := by
        gcongr
        exact norm_one_mat2_le
    _ = _ := by ring

/-- All Dyson terms of order `≥ 1` tend to `0` pointwise on `[0,L]`. -/
theorem dyson_tendsto (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) :
    ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) L, Tendsto (fun t : ℝ => dyson (Bm κ u t) (n + 1) x) (cocompact ℝ) (𝓝 0)
  | 0 => fun x hx => dyson_one_tendsto hu hx.1
  | n + 1 => fun x hx => by
    haveI : (cocompact ℝ).IsCountablyGenerated := by
      rw [cocompact_eq_atBot_atTop]; infer_instance
    have hdys : ∀ t : ℝ, dyson (Bm κ u t) (n + 1 + 1) x =
        ∫ s in (0 : ℝ)..x, Bm κ u t s * dyson (Bm κ u t) (n + 1) s := fun t => rfl
    simp_rw [hdys]
    have hIoc : Ι (0 : ℝ) x = Ioc 0 x := by rw [uIoc_of_le hx.1]
    have hsub : ∀ s ∈ Ι (0 : ℝ) x, s ∈ Icc (0 : ℝ) L := fun s hs => by
      rw [hIoc] at hs; exact ⟨hs.1.le, hs.2.trans hx.2⟩
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := 0) (b := x)
      (l := cocompact ℝ)
      (F := fun t s => Bm κ u t s * dyson (Bm κ u t) (n + 1) s) (f := fun _ => (0 : Mat2))
      (fun s => Real.sqrt κ * ‖u s‖ * (cC κ u L ^ (n + 1) / ((n + 1).factorial : ℝ)))
      (Eventually.of_forall fun t => by
        rw [hIoc]
        exact (((continuous_Bm κ t hu).mul
          (continuous_dyson (continuous_Bm κ t hu) (n + 1))).intervalIntegrable (μ := volume) 0 x).1.aestronglyMeasurable)
      (Eventually.of_forall fun t => ae_of_all _ fun s hs => by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul (norm_Bm_le κ u t s) (dyson_bound hu hL t (n + 1) (hsub s hs)) (norm_nonneg _)
          (by positivity))
      ((hu.norm.const_mul _).mul_const _ |>.intervalIntegrable _ _)
      (ae_of_all _ fun s hs => by
        have hih := dyson_tendsto hu hL n s (hsub s hs)
        refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
        refine squeeze_zero (fun t => norm_nonneg _) (fun t => (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_Bm_le κ u t s) (norm_nonneg _))) ?_
        simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hih).const_mul (Real.sqrt κ * ‖u s‖))
    have h0 : ∫ s in (0 : ℝ)..x, (fun _ => (0 : Mat2)) s = 0 := intervalIntegral.integral_zero
    rw [h0] at this
    exact this


/-- The Volterra series `transfer B_t (L) → 1`. -/
theorem transfer_tendsto (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun t : ℝ => QuantumNLS.L1SpatialTransfer.transfer (Bm κ u t) L) (cocompact ℝ) (𝓝 1) := by
  have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hsumm : ∀ t : ℝ, Summable (fun n : ℕ => dyson (Bm κ u t) n L) := fun t =>
    Summable.of_norm_bounded (Real.summable_pow_div_factorial (cC κ u L))
      (fun n => dyson_bound hu hL t n hLmem)
  have hsplit : ∀ t : ℝ, QuantumNLS.L1SpatialTransfer.transfer (Bm κ u t) L =
      1 + ∑' n : ℕ, dyson (Bm κ u t) (n + 1) L := by
    intro t
    unfold QuantumNLS.L1SpatialTransfer.transfer
    refine ((hsumm t).tsum_eq_zero_add).trans ?_
    rfl
  simp_rw [hsplit]
  have hbs : Summable (fun n : ℕ => cC κ u L ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (cC κ u L))
  have h : Tendsto (fun t : ℝ => ∑' n : ℕ, dyson (Bm κ u t) (n + 1) L) (cocompact ℝ)
      (𝓝 (∑' _n : ℕ, (0 : Mat2))) :=
    tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => cC κ u L ^ (n + 1) / ((n + 1).factorial : ℝ))
      hbs (fun n => dyson_tendsto hu hL n L hLmem)
      (Eventually.of_forall fun t n => dyson_bound hu hL t (n + 1) hLmem)
  simp only [tsum_zero] at h
  simpa using h.const_add (1 : Mat2)

end Dyson

section Final

variable {κ : ℝ} {u : ℝ → ℂ}

/-- `N_t(L) = D(L) M(L,t) = transfer B_t (L)`. -/
theorem N_eq_transfer (hκ : 0 < κ) (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    RootDiscriminantBound.Dm t L * spatialTransfer κ u (t : ℂ) L = QuantumNLS.L1SpatialTransfer.transfer (Bm κ u t) L := by
  have hM := spatialTransfer_spec' κ hu (t : ℂ)
  set M := spatialTransfer κ u (t : ℂ) with hMdef
  set N : ℝ → Mat2 := fun y => RootDiscriminantBound.Dm t y * M y with hN
  have hBc := continuous_Bm κ t hu
  have hNd : ∀ y, HasDerivAt N (Bm κ u t y * N y) y := fun y => hasDerivAt_N κ u t hκ hM y
  have hNc : Continuous N := continuous_iff_continuousAt.2 fun y => (hNd y).continuousAt
  have hA := hBc.intervalIntegrable (μ := MeasureTheory.volume) 0 L
  have hN0 : N 0 = 1 := by
    simp only [hN, hM.1, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RootDiscriminantBound.Dm, E1, E2, P1, P2]
  have hint : ∀ x ∈ Set.Icc 0 L, N x = 1 + ∫ s in (0 : ℝ)..x, Bm κ u t s * N s := by
    intro x _
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hNd y)
      ((hBc.mul hNc).intervalIntegrable 0 x)
    rw [this, hN0]; abel
  have hEq := (QuantumNLS.L1SpatialTransfer.fundamental_spec hL hA).2.2.2 N hNc.continuousOn hint
  exact hEq ⟨hL, le_rfl⟩

theorem two_cos_eq (t L : ℝ) : ((2 * Real.cos (t * L / 2) : ℝ) : ℂ) = E1 t L + E2 t L := by
  have h : ((t * L / 2 : ℝ) : ℂ) = (t * L / 2 : ℂ) := by push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_cos, h, Complex.cos]
  unfold E1 E2 a1
  push_cast
  ring_nf

/-- **`eq:root-trace-asymptotic`**: `Δ_u(t) - 2cos(tL/2) → 0` as `|t| → ∞` (continuous `u`, `κ > 0`, `L ≥ 0`). -/
theorem trace_asymptotic (hκ : 0 < κ) (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun t : ℝ => discReal L κ u t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0) := by
  have hT := transfer_tendsto (κ := κ) hu hL
  have hN : Tendsto (fun t : ℝ => ‖RootDiscriminantBound.Dm t L * spatialTransfer κ u (t : ℂ) L - 1‖) (cocompact ℝ) (𝓝 0) := by
    simp_rw [N_eq_transfer hκ hu hL]
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hT)
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  have h2 := hN.const_mul 2
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using h2)
  set M := spatialTransfer κ u (t : ℂ) L with hMdef
  set Nm := RootDiscriminantBound.Dm t L * M with hNm
  have hE : E1 t L * E2 t L = 1 := E1_mul_E2 t L
  have h00 : Nm 0 0 = E1 t L * M 0 0 := by
    simp [hNm, RootDiscriminantBound.Dm, P1, P2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h11 : Nm 1 1 = E2 t L * M 1 1 := by
    simp [hNm, RootDiscriminantBound.Dm, P1, P2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hM00 : M 0 0 = E2 t L * Nm 0 0 := by rw [h00, ← mul_assoc, mul_comm (E2 t L), hE, one_mul]
  have hM11 : M 1 1 = E1 t L * Nm 1 1 := by rw [h11, ← mul_assoc, hE, one_mul]
  have hdisc : ((discReal L κ u t - 2 * Real.cos (t * L / 2) : ℝ) : ℂ) =
      E2 t L * (Nm 0 0 - 1) + E1 t L * (Nm 1 1 - 1) := by
    have h1 := discriminant_eq_discReal L κ hu t
    have h2 : discriminant L κ u (t : ℂ) = M 0 0 + M 1 1 := by
      unfold discriminant; rw [Matrix.trace_fin_two]
    rw [Complex.ofReal_sub, ← h1, h2, two_cos_eq, hM00, hM11]
    ring
  have hn00 : ‖Nm 0 0 - 1‖ ≤ ‖Nm - 1‖ := by
    have := row_sum_le_norm (Nm - 1) 0
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at this
    refine le_trans ?_ this
    simp
  have hn11 : ‖Nm 1 1 - 1‖ ≤ ‖Nm - 1‖ := by
    have := row_sum_le_norm (Nm - 1) 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at this
    refine le_trans ?_ this
    simp
  have hrn : ‖((discReal L κ u t - 2 * Real.cos (t * L / 2) : ℝ) : ℂ)‖ ≤ 2 * ‖Nm - 1‖ := by
    rw [hdisc]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_E1, norm_E2, one_mul, one_mul]
    linarith
  rw [Complex.norm_real] at hrn
  exact hrn

#print axioms trace_asymptotic

end Final

end QuantumNLS.RootTraceAsymptotics
