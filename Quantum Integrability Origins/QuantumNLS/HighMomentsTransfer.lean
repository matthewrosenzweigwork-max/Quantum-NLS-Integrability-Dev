import QuantumNLS.HighMomentsFinal
import QuantumNLS.NormalizedTransfer
import QuantumNLS.RootPlacementBound
import QuantumNLS.RootSymbolConvergence

/-!
# PROP-008 `lem:B4-high-moments`: the actual-transfer application
(`spectral_calculus.tex:24–60`, last sentences: "In particular it applies to the actual transfers ... on each
fixed compact set"; `transfer_moments.tex` `lem:QR-finite-kernel`, `lem:QR-transfer-moments`)

Part 1 (this module): the abstract estimate `HighMomentsFinal.high_moments_of_normal` applied to the actual
physical transfer `S_N(z)` of DEF-048.

* **Strip kernel bound** (the source's `eq:QR-kernel-bound`, `lem:QR-finite-kernel`, R-9E0CB8BA): for `b ≥ 0`,
  `r ≥ 1`, `Im z ≥ −b`: `‖K_{r,z}‖ ≤ 2 e^{bL} (L/r)^r`.  Proof as printed: the length multiplying `iz` lies in
  `[0,L]`; for fixed `x` the admissible `y` fill disjoint intervals of total length `≤ L`, whose product is
  `≤ (L/r)^r` by AM–GM; same for columns and for `K̃⁻`; Schur test (`RootPlacementBound.norm_operator_le_schur`) and
  `‖P_r‖ ≤ 1`.  This replaces the factorial form `2e^{L|Im z|}(κL)^m/√((2m)!)` of `Q7A:eq:kernels`; both are
  superexponentially small, which is all the lemma's hypothesis `Σ r^m‖A_r‖ < ∞` uses (the `√((2m)!)` form, a
  Hilbert–Schmidt bound, is not formalized).
* **Rank sums**: for `A_r = κ^r K_{r,z}` and every `q`, `Σ_r r^q ‖A_r‖ ≤ M_q(b) := 2e^{bL} Σ_r r^q (κL/r)^r < ∞`
  uniformly on the strip `Im z ≥ −b` (`rankSum_le`, `summable_rankSum`), hence on every compact set.
* **Normality**: the source applies the lemma to the actual transfer `S_N(z)` itself (normal in the complete Bethe
  basis).  By `BasisAdjoint`, `S_N(z)^* = e^{−iL\bar z} S_N(\bar z)`; hence `S_N(z)` is normal iff `S_N(z)` and
  `S_N(\bar z)` commute (`normal_iff_commute`), and for **real** `z` it is normal unconditionally
  (`normal_real`: `S_N(x)^* = e^{−iLx} S_N(x)`, equivalently `e^{−iLx/2}S_N(x)` self-adjoint); off the real axis
  normality (joint diagonalization in the Bethe basis, R-8E4D05E7) is a hypothesis of `transfer_moments`.
* **`transfer_moments`**: for `p ≥ 1`, `N ≥ 1`, unit `u`, `Im z ≥ −b`, `S_N(z)` normal:
  `⟨u^N, |S_N(z) − s(z)|^{2p} u^N⟩ = ‖(S_N(z) − s(z))^p u^N‖² ≤ C_p(b)/N^p`, with `s(z) = productSymbol` and
  `C_p(b)` depending only on `p, b, L, κ` (uniform in `z` on the strip, `u`, `N`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators

noncomputable section

namespace QuantumNLS.HighMomentsTransfer

open QuantumNLS.BetheIntegralOperator QuantumNLS.BetheTransferKernelAdjoint
  QuantumNLS.BetheTransferOperators QuantumNLS.BetheWeakGradient QuantumNLS.BetheWavefunctions
  QuantumNLS.BetheFiniteNAction QuantumNLS.RootPlacementBound

/-! ### AM–GM and unit box integrals -/

theorem prod_le_pow_of_sum_le {m : ℕ} (hm : 1 ≤ m) (ℓ : Fin m → ℝ) (h0 : ∀ i, 0 ≤ ℓ i) {L : ℝ}
    (hs : ∑ i, ℓ i ≤ L) : ∏ i, ℓ i ≤ (L / m) ^ m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hg := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ℓ (fun _ _ => zero_le_one)
    (by simpa using hmpos) (fun i _ => h0 i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hg
  have hP : 0 ≤ ∏ i, ℓ i := Finset.prod_nonneg (fun i _ => h0 i)
  have h1 : ∏ i, ℓ i = ((∏ i, ℓ i) ^ ((m : ℝ)⁻¹)) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hmpos.ne', Real.rpow_one]
  have h2 : (∑ i, ℓ i) / m ≤ L / m := div_le_div_of_nonneg_right hs hmpos.le
  calc ∏ i, ℓ i = ((∏ i, ℓ i) ^ ((m : ℝ)⁻¹)) ^ m := h1
    _ ≤ (L / m) ^ m := pow_le_pow_left₀ (Real.rpow_nonneg hP _) (hg.trans h2) m

theorem integral_indicator_one (a b : ℝ) :
    ∫ t, (Ioo a b).indicator (fun _ => (1 : ℝ)) t = max (b - a) 0 := by
  rw [integral_indicator_const _ measurableSet_Ioo]
  simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal']

theorem cube_integral_le_one {m : ℕ} (L : ℝ) [Fact (0 < L)] (K : ℝ) (hK : 0 ≤ K)
    (F : (Fin m → ℝ) → ℝ) (hF0 : ∀ y, 0 ≤ F y) (a b : Fin m → ℝ)
    (hle : ∀ y, F y ≤ K * ∏ i, (Ioo (a i) (b i)).indicator (fun _ => (1 : ℝ)) (y i)) :
    ∫ y, F y ∂cubeMeasure m L ≤ K * ∏ i, max (b i - a i) 0 := by
  have hGi := integrable_box_prod a b (fun _ _ => (1 : ℝ)) (fun _ => continuous_const)
  have hG0 : ∀ y : Fin m → ℝ,
      0 ≤ ∏ i, (Ioo (a i) (b i)).indicator (fun _ => (1 : ℝ)) (y i) := fun y =>
    Finset.prod_nonneg (fun i _ => indicator_nonneg (fun s _ => zero_le_one) _)
  have hKG : Integrable (fun y : Fin m → ℝ =>
      K * ∏ i, (Ioo (a i) (b i)).indicator (fun _ => (1 : ℝ)) (y i)) volume := hGi.const_mul K
  calc ∫ y, F y ∂cubeMeasure m L
      ≤ ∫ y : Fin m → ℝ, K * ∏ i, (Ioo (a i) (b i)).indicator (fun _ => (1 : ℝ)) (y i)
          ∂cubeMeasure m L :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hF0) hKG.restrict
          (Filter.Eventually.of_forall hle)
    _ ≤ ∫ y : Fin m → ℝ, K * ∏ i, (Ioo (a i) (b i)).indicator (fun _ => (1 : ℝ)) (y i) :=
        setIntegral_le_integral hKG (Filter.Eventually.of_forall
          (fun y => mul_nonneg hK (hG0 y)))
    _ = K * ∏ i, max (b i - a i) 0 := by
        rw [integral_const_mul,
          integral_fintype_prod_volume_eq_prod
            (fun i => (Ioo (a i) (b i)).indicator (fun _ => (1 : ℝ)))]
        congr 1
        exact Finset.prod_congr rfl (fun i _ => integral_indicator_one _ _)

/-! ### Strip bounds for the ordered kernels -/

section Pointwise

variable {m : ℕ}

theorem norm_rawPlus_eq' (L : ℝ) (z : ℂ) {x y : Fin m → ℝ} (h : PlusOrder L x y) :
    ‖rawPlus L z x y‖ = Real.exp (-z.im * displacement x y) := by
  classical
  unfold rawPlus
  rw [if_pos h, norm_exp_I_mul]

theorem norm_rawPlus_le_strip {L : ℝ} (hL : 0 ≤ L) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im)
    {x y : Fin m → ℝ} (h : PlusOrder L x y) : ‖rawPlus L z x y‖ ≤ Real.exp (b * L) := by
  rw [norm_rawPlus_eq' L z h]
  obtain ⟨d0, dL⟩ := displacement_range hL h
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right (by linarith : -z.im ≤ b) d0
  have h2 := mul_le_mul_of_nonneg_left dL hb
  linarith

theorem norm_rawMinus_le_strip {L : ℝ} (hL : 0 ≤ L) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im)
    {x y : Fin m → ℝ} (h : MinusOrder L x y) : ‖rawMinus L z x y‖ ≤ Real.exp (b * L) := by
  rw [norm_rawMinus_eq z h]
  have hh : PlusOrder L y x := h
  obtain ⟨d0, dL⟩ := displacement_range hL hh
  have e : ∑ j, (y j - x j) = displacement y x := rfl
  rw [e]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right (by linarith : -z.im ≤ b) (sub_nonneg.mpr dL)
  have h2 := mul_le_mul_of_nonneg_left (by linarith : L - displacement y x ≤ L) hb
  linarith

theorem rawPlus_row_one (L : ℝ) (hL : 0 ≤ L) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im)
    (x y : Fin m → ℝ) :
    ‖rawPlus L z x y‖ ≤ Real.exp (b * L) *
      ∏ i, (Ioo (lower x i) (x i)).indicator (fun _ => (1 : ℝ)) (y i) := by
  classical
  by_cases h : PlusOrder L x y
  · have hx : x ∈ chamber m L := plusOrder_output_chamber h
    have hbx := (plusOrder_box hx y).mp h
    rw [Finset.prod_eq_one (fun i _ => indicator_of_mem (hbx i) _), mul_one]
    exact norm_rawPlus_le_strip hL hb z hz h
  · simp only [rawPlus, if_neg h, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ =>
      indicator_nonneg (fun s _ => zero_le_one) _))

theorem rawPlus_col_one (L : ℝ) (hL : 0 ≤ L) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im)
    (x y : Fin m → ℝ) :
    ‖rawPlus L z x y‖ ≤ Real.exp (b * L) *
      ∏ i, (Ioo (y i) (upper L y i)).indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  by_cases h : PlusOrder L x y
  · have hy : y ∈ chamber m L := minusOrder_output_chamber (L := L) (x := y) (y := x) h
    have hbx := (minusOrder_box hy x).mp h
    rw [Finset.prod_eq_one (fun i _ => indicator_of_mem (hbx i) _), mul_one]
    exact norm_rawPlus_le_strip hL hb z hz h
  · simp only [rawPlus, if_neg h, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ =>
      indicator_nonneg (fun s _ => zero_le_one) _))

theorem rawMinus_row_one (L : ℝ) (hL : 0 ≤ L) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im)
    (x y : Fin m → ℝ) :
    ‖rawMinus L z x y‖ ≤ Real.exp (b * L) *
      ∏ i, (Ioo (x i) (upper L x i)).indicator (fun _ => (1 : ℝ)) (y i) := by
  classical
  by_cases h : MinusOrder L x y
  · have hx : x ∈ chamber m L := minusOrder_output_chamber h
    have hbx := (minusOrder_box hx y).mp h
    rw [Finset.prod_eq_one (fun i _ => indicator_of_mem (hbx i) _), mul_one]
    exact norm_rawMinus_le_strip hL hb z hz h
  · simp only [rawMinus, if_neg h, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ =>
      indicator_nonneg (fun s _ => zero_le_one) _))

theorem rawMinus_col_one (L : ℝ) (hL : 0 ≤ L) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im)
    (x y : Fin m → ℝ) :
    ‖rawMinus L z x y‖ ≤ Real.exp (b * L) *
      ∏ i, (Ioo (lower y i) (y i)).indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  by_cases h : MinusOrder L x y
  · have hy : y ∈ chamber m L := plusOrder_output_chamber (L := L) (x := y) (y := x) h
    have hbx := (plusOrder_box hy x).mp h
    rw [Finset.prod_eq_one (fun i _ => indicator_of_mem (hbx i) _), mul_one]
    exact norm_rawMinus_le_strip hL hb z hz h
  · simp only [rawMinus, if_neg h, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ =>
      indicator_nonneg (fun s _ => zero_le_one) _))

end Pointwise

section LengthSums

variable {n : ℕ}

theorem sum_len_lower (x : Fin (n + 1) → ℝ) : ∑ i, (x i - lower x i) = x 0 := by
  rw [Finset.sum_sub_distrib, sum_lower, Fin.sum_univ_succ x]
  ring

theorem sum_len_upper (L : ℝ) (y : Fin (n + 1) → ℝ) :
    ∑ i, (upper L y i - y i) = L - y (Fin.last n) := by
  rw [Finset.sum_sub_distrib, sum_upper, Fin.sum_univ_castSucc y]
  ring

theorem sum_len_upper' (L : ℝ) (x : Fin (n + 1) → ℝ) :
    ∑ i, (upper L x i - x i) = L - x (Fin.last n) := sum_len_upper L x

theorem sum_len_lower' (y : Fin (n + 1) → ℝ) : ∑ i, (y i - lower y i) = y 0 := sum_len_lower y

end LengthSums

section Integrals

variable {L : ℝ} [Fact (0 < L)] {n : ℕ}

private theorem strip_bound (K : ℝ) (hK : 0 ≤ K) (ℓ : Fin (n + 1) → ℝ)
    (h0 : ∀ i, 0 ≤ ℓ i) (hs : ∑ i, ℓ i ≤ L) :
    K * ∏ i, max (ℓ i) 0 ≤ K * (L / (n + 1 : ℕ)) ^ (n + 1) := by
  have : ∏ i, max (ℓ i) 0 = ∏ i, ℓ i :=
    Finset.prod_congr rfl (fun i _ => max_eq_left (h0 i))
  rw [this]
  exact mul_le_mul_of_nonneg_left (prod_le_pow_of_sum_le (by omega) ℓ h0 hs) hK

theorem plus_row_strip {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (x : Fin (n + 1) → AddCircle L) :
    ∫ y, ‖(plusKernel L (n + 1) z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L (n + 1) ≤
      Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) := by
  have hm : Measurable fun y : Fin (n + 1) → ℝ => ‖rawPlus L z (representatives L x) y‖ :=
    ((measurable_rawPlus (n + 1) L z).comp (measurable_const.prodMk measurable_id)).norm
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  change ∫ y, (fun y' => ‖rawPlus L z (representatives L x) y'‖) (representatives L y) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  by_cases hx : representatives L x ∈ chamber (n + 1) L
  · have hI := cube_integral_le_one L (Real.exp (b * L)) (Real.exp_pos _).le
      (fun y' => ‖rawPlus L z (representatives L x) y'‖) (fun _ => norm_nonneg _)
      (fun i => lower (representatives L x) i) (fun i => representatives L x i)
      (fun y => rawPlus_row_one L hL hb z hz _ y)
    refine hI.trans (strip_bound _ (Real.exp_pos _).le _ ?_ ?_)
    · intro i; exact sub_nonneg.mpr (lower_bounds hx i).2.le
    · rw [sum_len_lower]; exact (hx.2 0).2.le
  · have h0 : ∀ y, rawPlus L z (representatives L x) y = 0 := fun y =>
      rawPlus_zero_off_chamber hx y z
    simp only [h0, norm_zero, integral_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg hL (by positivity)) _)

theorem plus_col_strip {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (y : Fin (n + 1) → AddCircle L) :
    ∫ x, ‖(plusKernel L (n + 1) z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L (n + 1) ≤
      Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) := by
  have hm : Measurable fun x : Fin (n + 1) → ℝ => ‖rawPlus L z x (representatives L y)‖ :=
    ((measurable_rawPlus (n + 1) L z).comp (measurable_id.prodMk measurable_const)).norm
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  change ∫ x, (fun x' => ‖rawPlus L z x' (representatives L y)‖) (representatives L x) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  by_cases hy : representatives L y ∈ chamber (n + 1) L
  · have hI := cube_integral_le_one L (Real.exp (b * L)) (Real.exp_pos _).le
      (fun x' => ‖rawPlus L z x' (representatives L y)‖) (fun _ => norm_nonneg _)
      (fun i => representatives L y i) (fun i => upper L (representatives L y) i)
      (fun x => rawPlus_col_one L hL hb z hz x _)
    refine hI.trans (strip_bound _ (Real.exp_pos _).le _ ?_ ?_)
    · intro i; exact sub_nonneg.mpr (upper_bounds hy i).1.le
    · rw [sum_len_upper]
      have := (hy.2 (Fin.last n)).1
      linarith
  · have h0 : ∀ x, rawPlus L z x (representatives L y) = 0 := by
      intro x
      have h : ¬ PlusOrder L x (representatives L y) := fun hh =>
        hy (minusOrder_output_chamber (L := L) (x := representatives L y) (y := x) hh)
      simp only [rawPlus, if_neg h]
    simp only [h0, norm_zero, integral_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg hL (by positivity)) _)

theorem minus_row_strip {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (x : Fin (n + 1) → AddCircle L) :
    ∫ y, ‖(minusKernel L (n + 1) z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L (n + 1) ≤
      Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) := by
  have hm : Measurable fun y : Fin (n + 1) → ℝ => ‖rawMinus L z (representatives L x) y‖ :=
    ((measurable_rawMinus (n + 1) L z).comp (measurable_const.prodMk measurable_id)).norm
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  change ∫ y, (fun y' => ‖rawMinus L z (representatives L x) y'‖) (representatives L y) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  by_cases hx : representatives L x ∈ chamber (n + 1) L
  · have hI := cube_integral_le_one L (Real.exp (b * L)) (Real.exp_pos _).le
      (fun y' => ‖rawMinus L z (representatives L x) y'‖) (fun _ => norm_nonneg _)
      (fun i => representatives L x i) (fun i => upper L (representatives L x) i)
      (fun y => rawMinus_row_one L hL hb z hz _ y)
    refine hI.trans (strip_bound _ (Real.exp_pos _).le _ ?_ ?_)
    · intro i; exact sub_nonneg.mpr (upper_bounds hx i).1.le
    · rw [sum_len_upper']
      have := (hx.2 (Fin.last n)).1
      linarith
  · have h0 : ∀ y, rawMinus L z (representatives L x) y = 0 := fun y =>
      rawMinus_zero_off_chamber hx y z
    simp only [h0, norm_zero, integral_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg hL (by positivity)) _)

theorem minus_col_strip {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (y : Fin (n + 1) → AddCircle L) :
    ∫ x, ‖(minusKernel L (n + 1) z).fn (x, y)‖ ∂PhysicalTensor.torusPiMeasure L (n + 1) ≤
      Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) := by
  have hm : Measurable fun x : Fin (n + 1) → ℝ => ‖rawMinus L z x (representatives L y)‖ :=
    ((measurable_rawMinus (n + 1) L z).comp (measurable_id.prodMk measurable_const)).norm
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  change ∫ x, (fun x' => ‖rawMinus L z x' (representatives L y)‖) (representatives L x) ∂_ ≤ _
  rw [torus_real_integral L _ hm]
  by_cases hy : representatives L y ∈ chamber (n + 1) L
  · have hI := cube_integral_le_one L (Real.exp (b * L)) (Real.exp_pos _).le
      (fun x' => ‖rawMinus L z x' (representatives L y)‖) (fun _ => norm_nonneg _)
      (fun i => lower (representatives L y) i) (fun i => representatives L y i)
      (fun x => rawMinus_col_one L hL hb z hz x _)
    refine hI.trans (strip_bound _ (Real.exp_pos _).le _ ?_ ?_)
    · intro i; exact sub_nonneg.mpr (lower_bounds hy i).2.le
    · rw [sum_len_lower']; exact (hy.2 0).2.le
  · have h0 : ∀ x, rawMinus L z x (representatives L y) = 0 := by
      intro x
      have h : ¬ MinusOrder L x (representatives L y) := fun hh =>
        hy (plusOrder_output_chamber (L := L) (x := representatives L y) (y := x) hh)
      simp only [rawMinus, if_neg h]
    simp only [h0, norm_zero, integral_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg hL (by positivity)) _)

/-- **`lem:QR-finite-kernel`** (R-9E0CB8BA): `‖K_{r,z}‖ ≤ 2 e^{bL} (L/r)^r` for `Im z ≥ −b`, `r ≥ 1`. -/
theorem norm_physicalKernel_strip {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) :
    ‖QuantumNLS.BethePhysicalTransfer.physicalKernel L (n + 1) z‖ ≤
      2 * (Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1)) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have ha : 0 ≤ Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg hL (by positivity)) _)
  have hp : ‖(plusKernel L (n + 1) z).operator‖ ≤ Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) :=
    norm_operator_le_schur _ _ ha (plus_row_strip hb z hz) (plus_col_strip hb z hz)
  have hm : ‖(minusKernel L (n + 1) z).operator‖ ≤ Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1) :=
    norm_operator_le_schur _ _ ha (minus_row_strip hb z hz) (minus_col_strip hb z hz)
  have hR : ‖rawOperator L (n + 1) z‖ ≤ 2 * (Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1)) := by
    unfold rawOperator
    calc _ ≤ ‖(plusKernel L (n + 1) z).operator‖ + ‖(minusKernel L (n + 1) z).operator‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith
  unfold QuantumNLS.BethePhysicalTransfer.physicalKernel
  have hP := norm_positionInclusion_le (L := L) (n + 1)
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
  calc _ ≤ ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)).adjoint‖ *
        ‖(rawOperator L (n + 1) z).comp (QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1))‖ := h2
    _ ≤ 1 * (‖rawOperator L (n + 1) z‖ *
        ‖QuantumNLS.BethePhysicalTransfer.positionInclusion L (n + 1)‖) :=
        mul_le_mul hPa h3 (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ ≤ 1 * ((2 * (Real.exp (b * L) * (L / (n + 1 : ℕ)) ^ (n + 1))) * 1) := by gcongr
    _ = _ := by ring

end Integrals

/-! ### Rank sums, uniformly on the strip -/

section RankSums

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.HighMomentsFinal QuantumNLS.NormalizedTransfer

/-- The majorant `r^q (κL/r)^r` (with `r = j+1`). -/
def Mterm (L κ : ℝ) (q j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) ^ q * (κ * L / (j + 1 : ℕ)) ^ (j + 1)

theorem summable_Mterm (L κ : ℝ) (hc : 0 ≤ κ * L) (q : ℕ) : Summable (Mterm L κ q) := by
  have hg : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * (1 / 2 : ℝ) ^ (j + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one q (r := (1 / 2 : ℝ)) (by norm_num)
    exact (summable_nat_add_iff 1).mpr h
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨⌈2 * (κ * L)⌉₊, fun j hj => ?_⟩
  have h1 : 2 * (κ * L) ≤ ((j + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (2 * (κ * L))
    have h2 : ((⌈2 * (κ * L)⌉₊ : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    linarith
  have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have h3 : κ * L / (j + 1 : ℕ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have h0 : 0 ≤ κ * L / (j + 1 : ℕ) := div_nonneg hc hpos.le
  unfold Mterm
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (pow_nonneg h0 _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h3 _) (by positivity)

/-- The uniform strip rank sums `M_q(b) = 2 e^{bL} Σ_r r^q (κL/r)^r`. -/
def Mq (L κ b : ℝ) (q : ℕ) : ℝ := 2 * Real.exp (b * L) * ∑' j, Mterm L κ q j

theorem Mq_nonneg (L κ b : ℝ) (hc : 0 ≤ κ * L) (hL : 0 ≤ L) (q : ℕ) : 0 ≤ Mq L κ b q := by
  unfold Mq
  refine mul_nonneg (by positivity) (tsum_nonneg (fun j => ?_))
  unfold Mterm
  have : 0 ≤ κ * L / (j + 1 : ℕ) := div_nonneg hc (by positivity)
  positivity

/-- The constant of the abstract lemma as a function of the rank sums. -/
def CpS (S : ℕ → ℝ) (p : ℕ) : ℝ :=
  ((p : ℝ) + 1) * ∑ k ∈ Finset.range (p + 1), ((p.choose k : ℝ) ^ 2 * (S 2 + S 1) ^ (2 * (p - k)) *
    ((((2 * k) ^ (2 * k) : ℕ) : ℝ) * (2 * S (2 * (k + k))) ^ (2 * k)))

theorem CpS_mono {S S' : ℕ → ℝ} (h0 : ∀ q, 0 ≤ S q) (h : ∀ q, S q ≤ S' q) (p : ℕ) :
    CpS S p ≤ CpS S' p := by
  unfold CpS
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro k _
  have n1 : 0 ≤ S 2 + S 1 := add_nonneg (h0 2) (h0 1)
  have n2 : 0 ≤ 2 * S (2 * (k + k)) := by linarith [h0 (2 * (k + k))]
  have a1 : S 2 + S 1 ≤ S' 2 + S' 1 := add_le_add (h 2) (h 1)
  have a2 : 2 * S (2 * (k + k)) ≤ 2 * S' (2 * (k + k)) := by linarith [h (2 * (k + k))]
  have b1 := pow_le_pow_left₀ n1 a1 (2 * (p - k))
  have b2 := pow_le_pow_left₀ n2 a2 (2 * k)
  have c0 : (0 : ℝ) ≤ (((2 * k) ^ (2 * k) : ℕ) : ℝ) := Nat.cast_nonneg _
  have d1 : (0 : ℝ) ≤ (p.choose k : ℝ) ^ 2 := by positivity
  have e1 : 0 ≤ (S 2 + S 1) ^ (2 * (p - k)) := pow_nonneg n1 _
  have e2 : 0 ≤ (2 * S (2 * (k + k))) ^ (2 * k) := pow_nonneg n2 _
  have f1 : (0 : ℝ) ≤ (S' 2 + S' 1) ^ (2 * (p - k)) := le_trans e1 b1
  exact mul_le_mul (mul_le_mul_of_nonneg_left b1 d1)
    (mul_le_mul_of_nonneg_left b2 c0) (mul_nonneg c0 e2) (mul_nonneg d1 f1)

variable {L : ℝ} [Fact (0 < L)]

/-- The coefficient family of the actual transfer at `z`: `A_r = κ^r K_{r,z}`. -/
def Afam (L : ℝ) [Fact (0 < L)] (κ : ℝ) (z : ℂ) : ∀ r : ℕ, BoundedSymmetricKernel (L2T L) r :=
  fun r => ((κ ^ r : ℝ) : ℂ) • orderedKernel L r z

theorem norm_Afam_le {κ : ℝ} (hκ : 0 ≤ κ) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (j : ℕ) :
    ‖Afam L κ z (j + 1)‖ ≤ 2 * Real.exp (b * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1) := by
  unfold Afam
  have h := norm_physicalKernel_strip (L := L) (n := j) hb z hz
  have e : (κ * L / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) = κ ^ (j + 1) * (L / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) := by
    rw [mul_div_assoc, mul_pow]
  rw [e]
  calc ‖((κ ^ (j + 1) : ℝ) : ℂ) • orderedKernel L (j + 1) z‖
      ≤ ‖((κ ^ (j + 1) : ℝ) : ℂ)‖ * ‖orderedKernel L (j + 1) z‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = κ ^ (j + 1) * ‖orderedKernel L (j + 1) z‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ _)]
    _ ≤ κ ^ (j + 1) * (2 * (Real.exp (b * L) * (L / ((j + 1 : ℕ) : ℝ)) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hκ _)
    _ = _ := by ring

theorem summable_rankSum {κ : ℝ} (hκ : 0 ≤ κ) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (q : ℕ) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖Afam L κ z (j + 1)‖) := by
  have hc : 0 ≤ κ * L := mul_nonneg hκ (Fact.out : 0 < L).le
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_Mterm L κ hc q).mul_left (2 * Real.exp (b * L)))
  have h := norm_Afam_le (L := L) hκ hb z hz j
  unfold Mterm
  calc ((j + 1 : ℕ) : ℝ) ^ q * ‖Afam L κ z (j + 1)‖
      ≤ ((j + 1 : ℕ) : ℝ) ^ q * (2 * Real.exp (b * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- **Uniform rank-sum bound**: `S_q(A) ≤ M_q(b)` for every `z` with `Im z ≥ −b`. -/
theorem rankSum_le {κ : ℝ} (hκ : 0 ≤ κ) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (hz : -b ≤ z.im) (q : ℕ) :
    Sq (Afam L κ z) q ≤ Mq L κ b q := by
  have hc : 0 ≤ κ * L := mul_nonneg hκ (Fact.out : 0 < L).le
  unfold Sq Mq
  rw [mul_comm (2 * Real.exp (b * L)), ← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_rankSum hκ hb z hz q)
    ((summable_Mterm L κ hc q).mul_right _)
  have h := norm_Afam_le (L := L) hκ hb z hz j
  unfold Mterm
  calc ((j + 1 : ℕ) : ℝ) ^ q * ‖Afam L κ z (j + 1)‖
      ≤ ((j + 1 : ℕ) : ℝ) ^ q * (2 * Real.exp (b * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem Cp_eq_CpS (A : ∀ r : ℕ, BoundedSymmetricKernel (L2T L) r) (p : ℕ) :
    Cp A p = CpS (Sq A) p := rfl

/-- The uniform constant `C_p(b)` of the strip. -/
def Cunif (L κ b : ℝ) (p : ℕ) : ℝ := CpS (Mq L κ b) p

end RankSums

/-! ### Normality of the actual transfer and the moment bound -/

section Moments

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.HighMomentsFinal QuantumNLS.HighMomentsOps
  QuantumNLS.NormalizedTransfer

variable {L : ℝ} [Fact (0 < L)]

/-- **Normality criterion** (via `BasisAdjoint`): `S_N(z)^* = e^{-iL\bar z} S_N(\bar z)`, so `S_N(z)` is normal iff
it commutes with `S_N(\bar z)`. -/
theorem normal_iff_commute (κ : ℝ) (N : ℕ) (z : ℂ) :
    Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N z)) (normalizedTransfer L κ N z) ↔
      Commute (normalizedTransfer L κ N (conj z)) (normalizedTransfer L κ N z) := by
  rw [normalizedTransfer_adjoint]
  set φ := QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L z with hφ
  have hφ0 : φ ≠ 0 := Complex.exp_ne_zero _
  set A := normalizedTransfer L κ N (conj z)
  set B := normalizedTransfer L κ N z
  constructor
  · intro h
    have h' : (φ • A) * B = B * (φ • A) := h
    refine ContinuousLinearMap.ext (fun g => ?_)
    have := congrArg (fun T => T g) h'
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul] at this
    have h2 := smul_right_injective _ hφ0 (by simpa using this)
    show A (B g) = B (A g)
    exact h2
  · intro h
    show (φ • A) * B = B * (φ • A)
    refine ContinuousLinearMap.ext (fun g => ?_)
    have := congrArg (fun T => T g) (h : A * B = B * A)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this]

/-- **For real spectral parameter the actual transfer is normal** (unconditionally):
`S_N(x)^* = e^{-iLx} S_N(x)`, i.e. `e^{-iLx/2} S_N(x)` is self-adjoint (`BasisAdjoint.normalizedT_selfAdjoint`). -/
theorem normal_real (κ : ℝ) (N : ℕ) (x : ℝ) :
    Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N (x : ℂ)))
      (normalizedTransfer L κ N (x : ℂ)) := by
  rw [normal_iff_commute, Complex.conj_ofReal]

/-- **The actual-transfer application of PROP-008** (`lem:B4-high-moments`, last sentences): for the actual
transfer `S_N(z) = X_N` with `A_0 = 1 + e^{izL}`, `A_r = κ^r K_{r,z}` and `x = s(z)` the product symbol, at every
`z` of the strip `Im z ≥ −b` at which `S_N(z)` is normal, for every `p ≥ 1`, `N ≥ 1` and unit `u`:
`⟨u^N, |S_N(z) − s(z)|^{2p} u^N⟩ = ‖(S_N(z) − s(z))^p u^N‖² ≤ C_p(b)/N^p`, `C_p(b)` independent of `z`, `u`, `N`. -/
theorem transfer_moments {κ : ℝ} (hκ : 0 ≤ κ) {b : ℝ} (hb : 0 ≤ b) (u : L2T L) (hu : ‖u‖ = 1)
    (z : ℂ) (hz : -b ≤ z.im) {N : ℕ} (hN : 0 < N)
    (hnormal : Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N z))
      (normalizedTransfer L κ N z)) {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint (normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) *
        (normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cunif L κ b p / (N : ℝ) ^ p := by
  have hc : 0 ≤ κ * L := mul_nonneg hκ (Fact.out : 0 < L).le
  have e1 : normalizedTransfer L κ N z =
      Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N :=
    normalizedTransfer_eq_Xop L κ N z
  have e2 : productSymbol L κ u z = xlim u (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) :=
    productSymbol_eq_xlim L κ u z
  have hZ : Zop u (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N =
      normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N) := by
    unfold Zop
    rw [e2]
    rw [← e1]
  have hX : Commute (ContinuousLinearMap.adjoint (Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N))
      (Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N) := by
    have : Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N = normalizedTransfer L κ N z :=
      e1.symm
    rw [this]; exact hnormal
  have hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖Afam L κ z (j + 1)‖) :=
    fun q => summable_rankSum hκ hb z hz q
  have key := high_moments_of_normal u hu (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) hsum N hN hX
    p hp
  rw [hZ] at key
  refine ⟨key.1, key.2.trans ?_⟩
  have hmono : Cp (Afam L κ z) p ≤ Cunif L κ b p := by
    rw [Cp_eq_CpS]
    exact CpS_mono (fun q => tsum_nonneg (fun j => by positivity))
      (fun q => rankSum_le hκ hb z hz q) p
  exact div_le_div_of_nonneg_right hmono (by positivity)

/-- The real-axis case, unconditional: `S_N(x)` is normal for every real `x`. -/
theorem transfer_moments_real {κ : ℝ} (hκ : 0 ≤ κ) {b : ℝ} (hb : 0 ≤ b) (u : L2T L) (hu : ‖u‖ = 1)
    (x : ℝ) {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : 1 ≤ p) :
    ‖((normalizedTransfer L κ N (x : ℂ) - productSymbol L κ u (x : ℂ) •
        (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cunif L κ b p / (N : ℝ) ^ p :=
  (transfer_moments hκ hb u hu (x : ℂ) (by simpa using neg_nonpos.mpr hb) hN
    (normal_real κ N x) hp).2

end Moments

#print axioms norm_physicalKernel_strip
#print axioms rankSum_le
#print axioms transfer_moments
#print axioms transfer_moments_real
#print axioms normal_iff_commute

end QuantumNLS.HighMomentsTransfer
