import QuantumNLS.RootDiscriminantL1
import QuantumNLS.RootTraceAsymptotics

/-! Real-axis interaction picture for the actual L1 Volterra transfer.
All profile hypotheses are interval integrability; L2 instances use the
canonical pullback. This does not identify the quantum and spatial symbols. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental
  QuantumNLS.RootDiscriminantBound QuantumNLS.L1SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.L1TraceGeometry
variable {L κ : ℝ} {v : ℝ → ℂ}

/-- The interaction coefficient is L1 on the same period as the profile. -/
theorem intervalIntegrable_Bm (hv : IntervalIntegrable v volume 0 L) (κ t : ℝ) :
    IntervalIntegrable (Bm κ v t) volume 0 L := by
  have hvc : IntervalIntegrable (fun x => conj (v x)) volume 0 L :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hv.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hv.2⟩
  let E : Mat2 := !![0, 1; 0, 0]
  let F : Mat2 := !![0, 0; 1, 0]
  have hc1 : Continuous (fun x => E1 t x * E1 t x) := by unfold E1; fun_prop
  have hc2 : Continuous (fun x => E2 t x * E2 t x) := by unfold E2; fun_prop
  have h1 := ((hvc.const_mul (Real.sqrt κ : ℂ)).mul_continuousOn hc1.continuousOn).smul_continuousOn
    (g := fun _ => E) continuousOn_const
  have h2 := ((hv.const_mul (Real.sqrt κ : ℂ)).mul_continuousOn hc2.continuousOn).smul_continuousOn
    (g := fun _ => F) continuousOn_const
  have he : Bm κ v t = fun x =>
      ((Real.sqrt κ : ℂ) * conj (v x) * (E1 t x * E1 t x)) • E +
      ((Real.sqrt κ : ℂ) * v x * (E2 t x * E2 t x)) • F := by
    funext x; ext i j
    fin_cases i <;> fin_cases j <;> simp [Bm, E, F]
  rw [he]
  exact h1.add h2

/-- Smooth scalar gauges times fixed rows preserve absolute continuity. -/
theorem ac_interaction {M : ℝ → Mat2}
    (hM : AbsolutelyContinuousOnInterval M 0 L) (t : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => RootDiscriminantBound.Dm t x * M x) 0 L := by
  have hr : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hE1 : ContDiff ℝ 1 (E1 t) := by unfold E1; fun_prop
  have hE2 : ContDiff ℝ 1 (E2 t) := by unfold E2; fun_prop
  let A : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 P1 1
  let B : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 P2 1
  have hA := A.lipschitzWith.comp_absolutelyContinuousOnInterval hM
  have hB := B.lipschitzWith.comp_absolutelyContinuousOnInterval hM
  have hh := (hE1.contDiffOn.absolutelyContinuousOnInterval.smul hA).add
    (hE2.contDiffOn.absolutelyContinuousOnInterval.smul hB)
  have he : (fun x => RootDiscriminantBound.Dm t x * M x) =
      fun x => E1 t x • A (M x) + E2 t x • B (M x) := by
    funext x
    change (E1 t x • P1 + E2 t x • P2) * M x =
      E1 t x • (P1 * M x * 1) + E2 t x • (P2 * M x * 1)
    simp [add_mul]
  rw [he]
  exact hh

/-- The interaction-picture identity for the actual L1 fundamental matrix. -/
theorem interaction_eq (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L)
    (_hκ : 0 < κ) (t : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    RootDiscriminantBound.Dm t x * RootDiscriminantL1.TT κ v (t : ℂ) x =
      transfer (Bm κ v t) x := by
  let M := RootDiscriminantL1.TT κ v (t : ℂ)
  let N : ℝ → Mat2 := fun y => RootDiscriminantBound.Dm t y * M y
  have hA := RootDiscriminantL1.intervalIntegrable_balCoef hv κ (t : ℂ)
  have hM := fundamental_spec hL hA
  have hNac : AbsolutelyContinuousOnInterval N 0 L := ac_interaction hM.2.1 t
  have hNd : ∀ᵐ y ∂volume.restrict (Icc (0 : ℝ) L),
      HasDerivAt N (Bm κ v t y * N y) y := by
    filter_upwards [hM.2.2.1] with y hy
    have hd := (hasDerivAt_Dm t y).mul hy
    refine hd.congr_deriv ?_
    have hE : E1 t y * E2 t y = 1 := E1_mul_E2 t y
    have hE2 : E2 t y = (E1 t y)⁻¹ := eq_inv_of_mul_eq_one_right hE
    have hne : E1 t y ≠ 0 := Complex.exp_ne_zero _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [N, M, RootDiscriminantL1.TT, RootDiscriminantBound.Dm, P1, P2, Bm, balCoef, coef, a1,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
      (rw [hE2]; field_simp; ring)
  have hN0 : N 0 = 1 := by
    have hM0 : M 0 = 1 := hM.1
    simp only [N, hM0, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RootDiscriminantBound.Dm, E1, E2, P1, P2]
  have heq : ∀ y ∈ Icc (0 : ℝ) L, N y = 1 + ∫ s in (0 : ℝ)..y, Bm κ v t s * N s := by
    intro y hy
    have hsub : uIcc (0 : ℝ) y ⊆ uIcc 0 L := by
      rw [uIcc_of_le hy.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hy.2
    have hBN := (intervalIntegrable_Bm hv κ t).mul_continuousOn hNac.continuousOn
    have hBNy := hBN.mono_set hsub
    let F : ℝ → Mat2 := fun s => N s - ∫ w in (0 : ℝ)..s, Bm κ v t w * N w
    have hFac : AbsolutelyContinuousOnInterval F 0 y :=
      (hNac.mono hsub).sub (ac_integral hBNy)
    have hz : ∀ᵐ s, s ∈ uIcc (0 : ℝ) y → HasDerivAt F 0 s := by
      have hh := (ae_restrict_iff' measurableSet_Icc).1 hNd
      filter_upwards [hh, hBNy.ae_hasDerivAt_integral] with s hs hi hsy
      have hsL := hsub hsy
      have hd := hs (by simpa [uIcc_of_le hL] using hsL)
      simpa only [F, sub_self] using! hd.sub (hi hsy 0 (by simp))
    obtain ⟨C, hC⟩ := hFac.const_of_ae_hasDerivAt_zero hz
    have h0 := hC 0 (by simp)
    have hyC := hC y (by simp)
    dsimp [F] at h0 hyC
    simp only [intervalIntegral.integral_same, sub_zero, hN0] at h0
    rw [← h0] at hyC
    exact sub_eq_iff_eq_add.mp hyC

  exact (fundamental_spec hL (intervalIntegrable_Bm hv κ t)).2.2.2 N
    (by simpa [uIcc_of_le hL] using hNac.continuousOn) heq hx

/-- Factorial majorant uniform in the real spectral parameter, for L1 profiles. -/
theorem dyson_bound (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L)
    (κ t : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖dyson (Bm κ v t) n x‖ ≤
      RootTraceAsymptotics.cC κ v L ^ n / (n.factorial : ℝ) := by
  have hB := intervalIntegrable_Bm hv κ t
  have hsub : uIcc (0 : ℝ) x ⊆ uIcc 0 L := by
    rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
  have hI : (∫ s in (0 : ℝ)..x, ‖Bm κ v t s‖) ≤ RootTraceAsymptotics.cC κ v L := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..x, Real.sqrt κ * ‖v s‖ :=
        intervalIntegral.integral_mono_on hx.1 (hB.mono_set hsub).norm
          ((hv.mono_set hsub).norm.const_mul _) (fun s _ => norm_Bm_le κ v t s)
      _ = Real.sqrt κ * ∫ s in (0 : ℝ)..x, ‖v s‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ RootTraceAsymptotics.cC κ v L :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
            (ae_of_all _ fun s => norm_nonneg (v s)) hv.norm) (Real.sqrt_nonneg _)
  have hI0 : 0 ≤ ∫ s in (0 : ℝ)..x, ‖Bm κ v t s‖ :=
    intervalIntegral.integral_nonneg hx.1 (fun s _ => norm_nonneg _)
  refine (norm_dyson_le_control hL hB n x hx).trans ?_
  calc
    _ ≤ 1 * RootTraceAsymptotics.cC κ v L ^ n / (n.factorial : ℝ) := by
      gcongr
      exact norm_one_mat2_le
    _ = _ := by ring

/-- Entrywise integration for interval-integrable matrix functions. -/
theorem integral_entry {A : ℝ → Mat2} (hA : IntervalIntegrable A volume 0 L)
    (i j : Fin 2) : (∫ s in (0 : ℝ)..L, A s) i j = ∫ s in (0 : ℝ)..L, A s i j :=
  (((RootDiscriminant.entryCLM i j).restrictScalars ℝ).intervalIntegral_comp_comm hA).symm

/-- Riemann-Lebesgue for the first interaction iterate; no continuous representative. -/
theorem dyson_one_tendsto (hv : IntervalIntegrable v volume 0 L) (hL : 0 ≤ L)
    (κ : ℝ) :
    Tendsto (fun t : ℝ => dyson (Bm κ v t) 1 L) (cocompact ℝ) (𝓝 0) := by
  have hd : ∀ t, dyson (Bm κ v t) 1 L = ∫ s in (0 : ℝ)..L, Bm κ v t s := by
    intro t; simp [dyson]
  simp_rw [hd]
  have h01 : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..L, Bm κ v t s 0 1) (cocompact ℝ) (𝓝 0) := by
    have := RootTraceAsymptotics.tendsto_osc (fun s => (Real.sqrt κ : ℂ) * conj (v s)) hL
      (c := 1) one_ne_zero
    refine this.congr (fun t => ?_)
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [Bm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, RootTraceAsymptotics.E1_sq]
  have h10 : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..L, Bm κ v t s 1 0) (cocompact ℝ) (𝓝 0) := by
    have := RootTraceAsymptotics.tendsto_osc (fun s => (Real.sqrt κ : ℂ) * v s) hL
      (c := -1) (by norm_num)
    refine this.congr (fun t => ?_)
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [Bm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, RootTraceAsymptotics.E2_sq]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hn01 := tendsto_zero_iff_norm_tendsto_zero.1 h01
  have hn10 := tendsto_zero_iff_norm_tendsto_zero.1 h10
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using hn01.add hn10)
  rw [sub_zero]
  refine norm_le_of_row_sums _ (by positivity) (fun i => ?_)
  rw [integral_entry (intervalIntegrable_Bm hv κ t) i 0,
    integral_entry (intervalIntegrable_Bm hv κ t) i 1]
  fin_cases i <;> simp [Bm]

/-- All Dyson terms of order `≥ 1` tend to `0` pointwise on `[0,L]`. -/
theorem dyson_tendsto (hv : IntervalIntegrable v volume 0 L) (hL : 0 ≤ L) :
    ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) L, Tendsto (fun t : ℝ => dyson (Bm κ v t) (n + 1) x) (cocompact ℝ) (𝓝 0)
  | 0 => fun x hx => dyson_one_tendsto (hv.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]
      exact Icc_subset_Icc_right hx.2)) hx.1 κ
  | n + 1 => fun x hx => by
    have : (cocompact ℝ).IsCountablyGenerated := by
      rw [cocompact_eq_atBot_atTop]; infer_instance
    have hdys : ∀ t : ℝ, dyson (Bm κ v t) (n + 1 + 1) x =
        ∫ s in (0 : ℝ)..x, Bm κ v t s * dyson (Bm κ v t) (n + 1) s := fun t => rfl
    simp_rw [hdys]
    have hIoc : Ι (0 : ℝ) x = Ioc 0 x := by rw [uIoc_of_le hx.1]
    have hsub : ∀ s ∈ Ι (0 : ℝ) x, s ∈ Icc (0 : ℝ) L := fun s hs => by
      rw [hIoc] at hs; exact ⟨hs.1.le, hs.2.trans hx.2⟩
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := 0) (b := x)
      (l := cocompact ℝ)
      (F := fun t s => Bm κ v t s * dyson (Bm κ v t) (n + 1) s) (f := fun _ => (0 : Mat2))
      (fun s => Real.sqrt κ * ‖v s‖ * (RootTraceAsymptotics.cC κ v L ^ (n + 1) / ((n + 1).factorial : ℝ)))
      (Eventually.of_forall fun t => by
        rw [hIoc]
        exact ((integrable_dyson_product (intervalIntegrable_Bm hv κ t) (n + 1)).mono_set
          (by rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2)).1.aestronglyMeasurable)
      (Eventually.of_forall fun t => ae_of_all _ fun s hs => by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul (norm_Bm_le κ v t s) (dyson_bound hL hv κ t (n + 1) (hsub s hs)) (norm_nonneg _)
          (by positivity))
      (((hv.mono_set (by
        rw [uIcc_of_le hx.1, uIcc_of_le hL]
        exact Icc_subset_Icc_right hx.2)).norm.const_mul _).mul_const _)
      (ae_of_all _ fun s hs => by
        have hih := dyson_tendsto hv hL n s (hsub s hs)
        refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
        refine squeeze_zero (fun t => norm_nonneg _) (fun t => (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_Bm_le κ v t s) (norm_nonneg _))) ?_
        simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hih).const_mul (Real.sqrt κ * ‖v s‖))
    have h0 : ∫ s in (0 : ℝ)..x, (fun _ => (0 : Mat2)) s = 0 := intervalIntegral.integral_zero
    rw [h0] at this
    exact this


/-- The Volterra series `transfer B_t (L) → 1`. -/
theorem transfer_tendsto (hv : IntervalIntegrable v volume 0 L) (hL : 0 ≤ L) :
    Tendsto (fun t : ℝ => QuantumNLS.L1SpatialTransfer.transfer (Bm κ v t) L) (cocompact ℝ) (𝓝 1) := by
  have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hsumm : ∀ t : ℝ, Summable (fun n : ℕ => dyson (Bm κ v t) n L) := fun t =>
    Summable.of_norm_bounded (Real.summable_pow_div_factorial (RootTraceAsymptotics.cC κ v L))
      (fun n => dyson_bound hL hv κ t n hLmem)
  have hsplit : ∀ t : ℝ, QuantumNLS.L1SpatialTransfer.transfer (Bm κ v t) L =
      1 + ∑' n : ℕ, dyson (Bm κ v t) (n + 1) L := by
    intro t
    unfold QuantumNLS.L1SpatialTransfer.transfer
    refine ((hsumm t).tsum_eq_zero_add).trans ?_
    rfl
  simp_rw [hsplit]
  have hbs : Summable (fun n : ℕ => RootTraceAsymptotics.cC κ v L ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (RootTraceAsymptotics.cC κ v L))
  have h : Tendsto (fun t : ℝ => ∑' n : ℕ, dyson (Bm κ v t) (n + 1) L) (cocompact ℝ)
      (𝓝 (∑' _n : ℕ, (0 : Mat2))) :=
    tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => RootTraceAsymptotics.cC κ v L ^ (n + 1) / ((n + 1).factorial : ℝ))
      hbs (fun n => dyson_tendsto hv hL n L hLmem)
      (Eventually.of_forall fun t n => dyson_bound hL hv κ t (n + 1) hLmem)
  simp only [tsum_zero] at h
  simpa using h.const_add (1 : Mat2)

/-- **`eq:root-trace-asymptotic`**: `Δ_u(t) - 2cos(tL/2) → 0` as `|t| → ∞` (L1 `v`, `κ > 0`, `L ≥ 0`). -/
theorem trace_asymptotic (hκ : 0 < κ) (hv : IntervalIntegrable v volume 0 L) (hL : 0 ≤ L) :
    Tendsto (fun t : ℝ => (RootDiscriminantL1.discL1 L κ v (t : ℂ)).re - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0) := by
  have hT := transfer_tendsto (κ := κ) hv hL
  have hN : Tendsto (fun t : ℝ => ‖RootDiscriminantBound.Dm t L * RootDiscriminantL1.TT κ v (t : ℂ) L - 1‖) (cocompact ℝ) (𝓝 0) := by
    simp_rw [interaction_eq hL hv hκ _ ⟨hL, le_rfl⟩]
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hT)
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  have h2 := hN.const_mul 2
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using h2)
  set M := RootDiscriminantL1.TT κ v (t : ℂ) L with hMdef
  set Nm := RootDiscriminantBound.Dm t L * M with hNm
  have hE : E1 t L * E2 t L = 1 := E1_mul_E2 t L
  have h00 : Nm 0 0 = E1 t L * M 0 0 := by
    simp [hNm, RootDiscriminantBound.Dm, P1, P2, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h11 : Nm 1 1 = E2 t L * M 1 1 := by
    simp [hNm, RootDiscriminantBound.Dm, P1, P2, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hM00 : M 0 0 = E2 t L * Nm 0 0 := by rw [h00, ← mul_assoc, mul_comm (E2 t L), hE, one_mul]
  have hM11 : M 1 1 = E1 t L * Nm 1 1 := by rw [h11, ← mul_assoc, hE, one_mul]
  have hdisc : (((RootDiscriminantL1.discL1 L κ v (t : ℂ)).re - 2 * Real.cos (t * L / 2) : ℝ) : ℂ) =
      E2 t L * (Nm 0 0 - 1) + E1 t L * (Nm 1 1 - 1) := by
    have h1 : RootDiscriminantL1.discL1 L κ v (t : ℂ) =
        ((RootDiscriminantL1.discL1 L κ v (t : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [RootDiscriminantL1.discriminant_im_eq_zero_L1 hL hv κ t]
    have h2 : RootDiscriminantL1.discL1 L κ v (t : ℂ) = M 0 0 + M 1 1 := by
      unfold RootDiscriminantL1.discL1; rw [Matrix.trace_fin_two]
    rw [Complex.ofReal_sub, ← h1, h2, RootTraceAsymptotics.two_cos_eq, hM00, hM11]
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
  have hrn : ‖(((RootDiscriminantL1.discL1 L κ v (t : ℂ)).re - 2 * Real.cos (t * L / 2) : ℝ) : ℂ)‖ ≤ 2 * ‖Nm - 1‖ := by
    rw [hdisc]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_E1, norm_E2, one_mul, one_mul]
    linarith
  rw [Complex.norm_real] at hrn
  exact hrn


/-- The real-parameter interaction matrix has a uniform exponential bound. -/
theorem interaction_norm_le (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L)
    (κ t : ℝ) :
    ‖transfer (Bm κ v t) L‖ ≤ Real.exp (RootTraceAsymptotics.cC κ v L) := by
  have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hs := Real.summable_pow_div_factorial (RootTraceAsymptotics.cC κ v L)
  have hn : Summable (fun n : ℕ => ‖dyson (Bm κ v t) n L‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => dyson_bound hL hv κ t n hLmem) hs
  have he : HasSum (fun n : ℕ => RootTraceAsymptotics.cC κ v L ^ n / (n.factorial : ℝ))
      (Real.exp (RootTraceAsymptotics.cC κ v L)) := by
    have := NormedSpace.expSeries_div_hasSum_exp (RootTraceAsymptotics.cC κ v L)
    rwa [← Real.exp_eq_exp_ℝ] at this
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum (fun n => dyson_bound hL hv κ t n hLmem) hs).trans_eq he.tsum_eq)

/-- The sharp cosh trace bound for merely interval-integrable profiles. -/
theorem abs_trace_le (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L)
    (hκ : 0 < κ) (t : ℝ) :
    |(RootDiscriminantL1.discL1 L κ v (t : ℂ)).re| ≤
      2 * Real.cosh (Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖v s‖) := by
  let M := RootDiscriminantL1.TT κ v (t : ℂ) L
  have hrow : ‖M 0 0‖ + ‖M 0 1‖ ≤ Real.exp (RootTraceAsymptotics.cC κ v L) := by
    have hr := row_sum_le_norm (RootDiscriminantBound.Dm t L * M) 0
    have he : ‖(RootDiscriminantBound.Dm t L * M) 0 0‖ +
        ‖(RootDiscriminantBound.Dm t L * M) 0 1‖ = ‖M 0 0‖ + ‖M 0 1‖ := by
      simp [RootDiscriminantBound.Dm, P1, P2, Matrix.mul_apply, Fin.sum_univ_two,
        norm_E1]
    rw [he] at hr
    exact hr.trans (by
      change ‖RootDiscriminantBound.Dm t L * RootDiscriminantL1.TT κ v (t : ℂ) L‖ ≤ _
      rw [interaction_eq hL hv hκ t ⟨hL, le_rfl⟩]
      exact interaction_norm_le hL hv κ t)
  have hd := RootDiscriminantL1.norm_sq_sub_eq_one_L1 hL hv κ t (x := L) ⟨hL, le_rfl⟩
  have hp := cosh_bound_of (norm_nonneg (M 0 0)) (norm_nonneg (M 0 1)) hd hrow
  have he11 := RootDiscriminantL1.transfer_symm_apply hL hv κ t (x := L) ⟨hL, le_rfl⟩ 1 1
  have hr1 : (1 : Fin 2).rev = 0 := rfl
  simp only [hr1] at he11
  have htrace : (RootDiscriminantL1.discL1 L κ v (t : ℂ)).re = 2 * (M 0 0).re := by
    unfold RootDiscriminantL1.discL1
    rw [Matrix.trace_fin_two, he11]
    simp [M]; ring
  rw [htrace, abs_mul, abs_two]
  have hh := Complex.abs_re_le_norm (M 0 0)
  exact mul_le_mul_of_nonneg_left (hh.trans hp) (by norm_num)

/-- All these statements apply to every physical L2 class through its canonical pullback. -/
theorem L2_trace_asymptotic [Fact (0 < L)] (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    Tendsto (fun t : ℝ => (L2SpatialTransfer.discriminant κ u (t : ℂ)).re -
      2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0) :=
  trace_asymptotic hκ (L2SpatialTransfer.intervalIntegrable_profile u) (Fact.out : 0 < L).le

theorem L2_abs_trace_le [Fact (0 < L)] (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (t : ℝ) :
    |(L2SpatialTransfer.discriminant κ u (t : ℂ)).re| ≤
      2 * Real.cosh (Real.sqrt κ * ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile u s‖) :=
  abs_trace_le (Fact.out : 0 < L).le (L2SpatialTransfer.intervalIntegrable_profile u) hκ t

end QuantumNLS.L1TraceGeometry

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.L1TraceGeometry.intervalIntegrable_Bm
#print axioms QuantumNLS.L1TraceGeometry.ac_interaction
#print axioms QuantumNLS.L1TraceGeometry.interaction_eq
#print axioms QuantumNLS.L1TraceGeometry.dyson_bound
#print axioms QuantumNLS.L1TraceGeometry.integral_entry
#print axioms QuantumNLS.L1TraceGeometry.dyson_one_tendsto
#print axioms QuantumNLS.L1TraceGeometry.dyson_tendsto
#print axioms QuantumNLS.L1TraceGeometry.transfer_tendsto
#print axioms QuantumNLS.L1TraceGeometry.trace_asymptotic
#print axioms QuantumNLS.L1TraceGeometry.interaction_norm_le
#print axioms QuantumNLS.L1TraceGeometry.abs_trace_le
#print axioms QuantumNLS.L1TraceGeometry.L2_trace_asymptotic
#print axioms QuantumNLS.L1TraceGeometry.L2_abs_trace_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.L1TraceGeometry." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
