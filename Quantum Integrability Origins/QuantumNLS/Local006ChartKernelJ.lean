import QuantumNLS.Local006NormalizedDerivativeJ
import QuantumNLS.Local006KernelSeriesI

/-! Independent normalization-word kernels of the actual chart and its real
 transpose. The positive operators retain absolute path coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace QuantumNLS.Local006.ChartKernelJ
open QuantumNLS.PhysicalTensor QuantumNLS.Local002Bridge QuantumNLS.Local005
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.Local006.NormalizedBindingH QuantumNLS.Local006.PositiveSlotsJ
  QuantumNLS.Local006.NormalizationKernelJ QuantumNLS.Local006.NormalizedDerivativeJ
  QuantumNLS.Local006.CollectiveF QuantumNLS.Local006.FirstJetF QuantumNLS.Local006.KernelSeriesI
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def toProfileDerivative : (ScalarInterval L →L[ℝ] Mixed) →L[ℝ] (L2T L →L[ℝ] Seq2) :=
  ((ContinuousLinearMap.compL ℝ (L2T L) Mixed Seq2) (lowerLeft.restrictScalars ℝ)).comp
    ((ContinuousLinearMap.compL ℝ (L2T L) (ScalarInterval L) Mixed).flip (toIntervalR L))

def chartWordDerivative (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L) (jl : ℕ × ℕ) : L2T L →L[ℝ] Seq2 :=
  factor L κ • toProfileDerivative (actualWordDerivative hL hκ hr hs (toInterval L u) jl)

def chartWordKernel (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L) (jl : ℕ × ℕ) : Seq2 →L[ℂ] Seq2 :=
  (‖factor L κ‖ : ℂ) • lowerLeft.comp (actualWordKernel hL hκ hr hs (toInterval L u) jl)

lemma intervalFourier_toInterval (u : L2T L) : intervalFourierIso L (toInterval L u) = fourierR L u := by
  apply lp.ext
  funext n
  exact QuantumNLS.Local006.G3Fourier.physicalFourier_toInterval u n

lemma chartWordKernel_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L) (jl : ℕ × ℕ) :
    ‖chartWordKernel hL hκ hr hs u jl‖ ≤ ‖factor L κ‖ *
      ‖actualWordKernel hL hκ hr hs (toInterval L u) jl‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(‖factor L κ‖ : ℂ) • (actualWordKernel hL hκ hr hs (toInterval L u) jl v).2.2‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (mul_le_mul_of_nonneg_left ((component_bounds _).2.2.2.trans
    ((actualWordKernel hL hκ hr hs (toInterval L u) jl).le_opNorm v)) (norm_nonneg _)).trans_eq (by ring)

lemma chartWordDerivative_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L) (jl : ℕ × ℕ) :
    ‖chartWordDerivative hL hκ hr hs u jl‖ ≤ ‖factor L κ‖ *
      ‖actualWordDerivative hL hκ hr hs (toInterval L u) jl‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖factor L κ • (actualWordDerivative hL hκ hr hs (toInterval L u) jl (toInterval L v)).2.2‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left ((component_bounds _).2.2.2.trans
    ((actualWordDerivative hL hκ hr hs (toInterval L u) jl).le_opNorm (toInterval L v)))
      (norm_nonneg _)).trans_eq (by rw [norm_toInterval]; ring)

lemma chartWord_domination (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u v : L2T L) (hu : ‖u‖ < radius L r κ) (jl : ℕ × ℕ) (n : ℤ) :
    ‖chartWordDerivative hL hκ hr hs u jl v n‖ ≤
      (chartWordKernel hL hκ hr hs u jl (moduli (fourierR L v)) n).re := by
  have h := actualWordKernel_majorizes hL hκ hr hs (toInterval L u)
    (by rw [norm_toInterval]; exact hu) jl (toInterval L v) n 1 0
  rw [intervalFourier_toInterval] at h
  change ‖factor L κ * (actualWordDerivative hL hκ hr hs (toInterval L u) jl (toInterval L v)).2.2 n‖ ≤
    ((‖factor L κ‖ : ℂ) * (actualWordKernel hL hκ hr hs (toInterval L u) jl (moduli (fourierR L v))).2.2 n).re
  rw [norm_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

lemma chartWordKernel_positive (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L) (hu : ‖u‖ < radius L r κ)
    (jl : ℕ × ℕ) (v : Seq2) (n : ℤ) :
    (chartWordKernel hL hκ hr hs u jl (moduli v) n).im = 0 ∧
      0 ≤ (chartWordKernel hL hκ hr hs u jl (moduli v) n).re := by
  have h := actualWordKernel_positive hL hκ hr hs (toInterval L u)
    (by rw [norm_toInterval]; exact hu) jl v n 1 0
  change (lowerLeft (actualWordKernel hL hκ hr hs (toInterval L u) jl (moduli v)) n).im = 0 ∧
    0 ≤ (lowerLeft (actualWordKernel hL hκ hr hs (toInterval L u) jl (moduli v)) n).re at h
  change ((‖factor L κ‖ : ℂ) * _).im = 0 ∧ 0 ≤ ((‖factor L κ‖ : ℂ) * _).re
  exact ⟨by simp [Complex.mul_im, h.1], by simpa using mul_nonneg (norm_nonneg (factor L κ)) h.2⟩

lemma chartWord_series (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L) (hu : ‖u‖ < radius L r κ) :
    Summable (fun jl => ‖chartWordKernel hL hκ hr hs u jl‖) ∧
      Summable (fun jl => ‖chartWordDerivative hL hκ hr hs u jl‖) := by
  have hp := actualWordKernel_summable hL hκ hr hs (toInterval L u)
    (by rw [norm_toInterval]; exact hu)
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (chartWordKernel_norm hL hκ hr hs u)
    (hp.mul_left ‖factor L κ‖), ?_⟩
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jl =>
    (chartWordDerivative_norm hL hκ hr hs u jl).trans (mul_le_mul_of_nonneg_left
      (actualWordDerivative_norm hL hκ hr hs (toInterval L u)
        (by rw [norm_toInterval]; exact hu) jl) (norm_nonneg _)))
    (hp.mul_left ‖factor L κ‖)

/-- Exact termwise derivative identification for the actual chart. The
summability of the entrywise-positive Fourier operators is proved separately. -/
theorem actual_chart_derivative_words (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {G : L2T L → Seq2} {ρ0 : ℝ} (hρ0 : 0 < ρ0)
    (hGe : ∀ u ∈ ball (0 : L2T L) ρ0, ∀ n, G u n = scalarG L κ r u n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ0 ∧ ρ ≤ radius L r κ ∧
      ∀ u ∈ ball (0 : L2T L) ρ,
        Summable (fun jl => ‖chartWordKernel hL hκ hr hs u jl‖) ∧
        Summable (fun jl => ‖chartWordDerivative hL hκ hr hs u jl‖) ∧
        HasSum (fun jl => chartWordDerivative hL hκ hr hs u jl) (fderiv ℝ G u) := by
  obtain ⟨ρn, hρn, hn⟩ := actual_normalized_majorant hL hκ hr hs
  let ρ := min ρ0 (min ρn (radius L r κ))
  have hρ : 0 < ρ := lt_min hρ0 (lt_min hρn (radius_pos hL hκ hr))
  have hsub : ball (0 : L2T L) ρ ⊆ ball 0 ρ0 := ball_subset_ball (min_le_left _ _)
  have hsmall {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) : ‖u‖ < radius L r κ :=
    (mem_ball_zero_iff.mp hu).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have heq : ∀ u ∈ ball (0 : L2T L) ρ, G u = factor L κ • (normalizedSource hL hκ hr hs (toInterval L u)).2.2 := by
    intro u hu
    have hui : ‖toInterval L u‖ < ρn := by
      rw [norm_toInterval]
      exact (mem_ball_zero_iff.mp hu).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    apply lp.ext
    funext n
    rw [hGe u (hsub hu) n, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      QuantumNLS.Local006.ChartMajorantH.scalarG_normalized hL hκ hr hs u (hn _ hui).2.2.2.2.2 n]
    rfl
  refine ⟨ρ, hρ, min_le_left _ _, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro u hu
  have hus : ‖toInterval L u‖ < radius L r κ := by rw [norm_toInterval]; exact hsmall hu
  have hd := normalizedSource_hasFDerivAt hL hκ hr hs (toInterval L u) hus
  have hc := (((lowerLeft.restrictScalars ℝ).hasFDerivAt).comp u
    (hd.comp u (toIntervalR L).hasFDerivAt)).const_smul (factor L κ)
  have hcG : HasFDerivAt G (factor L κ • toProfileDerivative
      (∑' jl, actualWordDerivative hL hκ hr hs (toInterval L u) jl)) u := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hu] with v hv
    exact heq v hv
  have hseries := chartWord_series hL hκ hr hs u (hsmall hu)
  have hdword : Summable (fun jl => ‖actualWordDerivative hL hκ hr hs (toInterval L u) jl‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (actualWordDerivative_norm hL hκ hr hs _ hus)
      (actualWordKernel_summable hL hκ hr hs _ hus)
  have hsum := ((toProfileDerivative (L := L)).hasSum hdword.of_norm.hasSum).const_smul (factor L κ)
  refine ⟨hseries.1, hseries.2, ?_⟩
  rw [hcG.fderiv]
  exact hsum

lemma moduli_single_scale (m : ℤ) (z : ℂ) :
    moduli (lp.single 2 m z) = (‖z‖ : ℂ) • lp.single 2 m (1 : ℂ) := by
  apply lp.ext
  funext n
  by_cases hn : n = m <;> simp [moduli_apply, lp.single_apply, hn]

lemma coefficient_bound {A : Seq2 →L[ℝ] Seq2} {K : Seq2 →L[ℂ] Seq2}
    (h : ∀ v n, ‖A v n‖ ≤ (K (moduli v) n).re)
    (n m : ℤ) (z w : ℂ) :
    |⟪A (lp.single 2 m z), lp.single 2 n w⟫_ℝ| ≤
      ‖z‖ * ‖w‖ * (K (lp.single 2 m 1) n).re := by
  have hd := h (lp.single 2 m z) n
  rw [moduli_single_scale, map_smul] at hd
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hd
  rw [lp.inner_single_right]
  exact (show |⟪A (lp.single 2 m z) n, w⟫_ℝ| ≤ ‖A (lp.single 2 m z) n‖ * ‖w‖ from
    by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (A (lp.single 2 m z) n) w).trans
      ((mul_le_mul_of_nonneg_right hd (norm_nonneg w)).trans_eq (by ring))

lemma kernel_transpose (K : Seq2 →L[ℂ] Seq2)
    (h : ∀ n m, (K (lp.single 2 m 1) n).im = 0) (n m : ℤ) :
    ContinuousLinearMap.adjoint K (lp.single 2 n 1) m = K (lp.single 2 m 1) n := by
  have he := K.adjoint_inner_right (lp.single 2 m 1) (lp.single 2 n 1)
  simp only [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    starRingEnd_apply, star_one, one_mul, mul_one] at he
  rw [he]
  apply Complex.ext <;> simp [h n m]

def absoluteBlock (A : Seq2 →L[ℝ] Seq2) (n m : ℤ) : ℝ :=
  |⟪A (lp.single 2 m 1), lp.single 2 n 1⟫_ℝ| +
  |⟪A (lp.single 2 m 1), lp.single 2 n Complex.I⟫_ℝ| +
  |⟪A (lp.single 2 m Complex.I), lp.single 2 n 1⟫_ℝ| +
  |⟪A (lp.single 2 m Complex.I), lp.single 2 n Complex.I⟫_ℝ|

def FiniteKernelBound (a : ℤ → ℤ → ℝ) (B : ℝ) : Prop :=
  ∀ (s : Finset ℤ) (v : Seq2), ∃ b : Seq2,
    (∀ n, b n = ((∑ m ∈ s, a n m * ‖v m‖ : ℝ) : ℂ)) ∧ ‖b‖ ≤ B * ‖v‖

/-- Uniform l2 bounds for every finite truncation of an entrywise-absolute
kernel. No summation of uniform coordinate bounds is used. -/
lemma finite_kernel_bound {K : Seq2 →L[ℂ] Seq2} {a : ℤ → ℤ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ n m, 0 ≤ a n m)
    (hK : ∀ n m, (K (lp.single 2 m 1) n).im = 0 ∧ 0 ≤ (K (lp.single 2 m 1) n).re)
    (hbound : ∀ n m, a n m ≤ B * (K (lp.single 2 m 1) n).re) :
    FiniteKernelBound a (B * ‖K‖) := by
  intro s v
  let q : Seq2 := ∑ m ∈ s, (‖v m‖ : ℂ) • lp.single 2 m 1
  have hq (n : ℤ) : q n = if n ∈ s then (‖v n‖ : ℂ) else 0 := by
    simp only [q, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      lp.single_apply, smul_eq_mul]
    by_cases hn : n ∈ s
    · rw [Finset.sum_eq_single n]
      · simp [hn]
      · intro b hb hbn; simp [Ne.symm hbn]
      · exact fun h => (h hn).elim
    · rw [if_neg hn]
      apply Finset.sum_eq_zero
      intro b hb
      have hnb : n ≠ b := by intro h; subst b; exact hn hb
      simp [hnb]
  have hqn : ‖q‖ ≤ ‖v‖ := lp.norm_mono (by norm_num) (fun n => by
    rw [hq]; split_ifs <;> simp)
  have he (n : ℤ) : (K q n).re = ∑ m ∈ s, ‖v m‖ * (K (lp.single 2 m 1) n).re := by
    simp only [q, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hf (n : ℤ) : (∑ m ∈ s, a n m * ‖v m‖) ≤ B * (K q n).re := by
    rw [he, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact (mul_le_mul_of_nonneg_right (hbound n m) (norm_nonneg _)).trans_eq (by ring)
  have hfn (n : ℤ) : 0 ≤ ∑ m ∈ s, a n m * ‖v m‖ :=
    Finset.sum_nonneg fun m hm => mul_nonneg (ha n m) (norm_nonneg _)
  let y : Seq2 := (B : ℂ) • K q
  have hdom (n : ℤ) : ‖((∑ m ∈ s, a n m * ‖v m‖ : ℝ) : ℂ)‖ ≤ ‖y n‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfn n)]
    calc
      _ ≤ B*(K q n).re := hf n
      _ = (y n).re := by simp [y, Complex.mul_re]
      _ ≤ ‖y n‖ := Complex.re_le_norm _
  let b : Seq2 := ⟨fun n => ((∑ m ∈ s, a n m * ‖v m‖ : ℝ) : ℂ),
    (lp.memℓp y).mono' hdom⟩
  refine ⟨b, fun n => rfl, ?_⟩
  calc
    _ ≤ ‖y‖ := lp.norm_mono (by norm_num) hdom
    _ = B*‖K q‖ := by simp [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hB]
    _ ≤ B*(‖K‖*‖q‖) := mul_le_mul_of_nonneg_left (K.le_opNorm q) hB
    _ ≤ (B*‖K‖)*‖v‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hqn (mul_nonneg hB (norm_nonneg K))

lemma absoluteBlock_bound {A : Seq2 →L[ℝ] Seq2} {K : Seq2 →L[ℂ] Seq2}
    (h : ∀ n m z w, |⟪A (lp.single 2 m z), lp.single 2 n w⟫_ℝ| ≤
      ‖z‖*‖w‖*(K (lp.single 2 m 1) n).re) (n m : ℤ) :
    absoluteBlock A n m ≤ 4*(K (lp.single 2 m 1) n).re := by
  have h11 := h n m 1 1
  have h1i := h n m 1 Complex.I
  have hi1 := h n m Complex.I 1
  have hii := h n m Complex.I Complex.I
  simp only [norm_one, Complex.norm_I, one_mul] at h11 h1i hi1 hii
  unfold absoluteBlock
  linarith

lemma absoluteBlock_adjoint (A : Seq2 →L[ℝ] Seq2) (n m : ℤ) :
    absoluteBlock (ContinuousLinearMap.adjoint A) n m = absoluteBlock A m n := by
  have h (z w : Seq2) : ⟪ContinuousLinearMap.adjoint A z, w⟫_ℝ = ⟪A w, z⟫_ℝ := by
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_right]
  simp only [absoluteBlock, h]
  ring

/-- The kernels here control all four real matrix entries in each pair of
complex Fourier coordinates. Their positive operator series and transposed
positive operator series converge in norm. -/
def KernelClauses (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (G : L2T L → Seq2) (u : L2T L) : Prop :=
  let A := fun jl => fourierOperator (chartWordDerivative hL hκ hr hs u jl)
  let K := chartWordKernel hL hκ hr hs u
  Summable (fun jl => ‖K jl‖) ∧
  Summable (fun jl => ‖ContinuousLinearMap.adjoint (K jl)‖) ∧
  Summable (fun jl => ‖A jl‖) ∧ HasSum A (fourierOperator (fderiv ℝ G u)) ∧
  Summable (fun jl => ‖ContinuousLinearMap.adjoint (A jl)‖) ∧
  HasSum (fun jl => ContinuousLinearMap.adjoint (A jl))
    (ContinuousLinearMap.adjoint (fourierOperator (fderiv ℝ G u))) ∧
  (∀ jl v n, (K jl (moduli v) n).im = 0 ∧ 0 ≤ (K jl (moduli v) n).re) ∧
  (∀ jl n m, ContinuousLinearMap.adjoint (K jl) (lp.single 2 n 1) m = K jl (lp.single 2 m 1) n) ∧
  (∀ jl n m z w,
    |⟪A jl (lp.single 2 m z), lp.single 2 n w⟫_ℝ| ≤ ‖z‖*‖w‖*(K jl (lp.single 2 m 1) n).re) ∧
  (∀ jl n m z w,
    |⟪lp.single 2 m z, ContinuousLinearMap.adjoint (A jl) (lp.single 2 n w)⟫_ℝ| ≤
      ‖z‖*‖w‖*(ContinuousLinearMap.adjoint (K jl) (lp.single 2 n 1) m).re) ∧
  (∀ jl, FiniteKernelBound (absoluteBlock (A jl)) (4*‖K jl‖)) ∧
  (∀ jl, FiniteKernelBound (absoluteBlock (ContinuousLinearMap.adjoint (A jl)))
    (4*‖ContinuousLinearMap.adjoint (K jl)‖))

/-- Actual differentiated normalization-word kernels and their transposes.
The positive kernels, rather than operator-norm convergence by itself, supply
entrywise-absolute bounds for both real directions in every Fourier slot. -/
theorem actual_chart_absolute_kernel_series (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {G : L2T L → Seq2} {ρ0 : ℝ} (hρ0 : 0 < ρ0)
    (hGe : ∀ u ∈ ball (0 : L2T L) ρ0, ∀ n, G u n = scalarG L κ r u n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ0 ∧ ρ ≤ radius L r κ ∧
      ∀ u ∈ ball (0 : L2T L) ρ, KernelClauses hL hκ hr hs G u := by
  obtain ⟨ρ, hρ, hρ0', hρR, hw⟩ := actual_chart_derivative_words hL hκ hr hs hρ0 hGe
  refine ⟨ρ, hρ, hρ0', hρR, ?_⟩
  intro u hu
  have hus : ‖u‖ < radius L r κ := (mem_ball_zero_iff.mp hu).trans_le hρR
  have hd := hw u hu
  let A := fun jl => fourierOperator (chartWordDerivative hL hκ hr hs u jl)
  let K := chartWordKernel hL hκ hr hs u
  have hA : Summable (fun jl => ‖A jl‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun jl => (fourierOperatorMap (L := L)).le_opNorm _)
      (hd.2.1.mul_left ‖fourierOperatorMap (L := L)‖)
  have hsA : HasSum A (fourierOperator (fderiv ℝ G u)) :=
    (fourierOperatorMap (L := L)).hasSum hd.2.2
  have hpos := chartWordKernel_positive hL hκ hr hs u hus
  have htrans (jl : ℕ × ℕ) (n m : ℤ) :
      ContinuousLinearMap.adjoint (K jl) (lp.single 2 n 1) m = K jl (lp.single 2 m 1) n :=
    kernel_transpose (K jl) (fun n m => by
      have h := hpos jl (lp.single 2 m 1) n
      rw [moduli_single] at h
      exact h.1) n m
  have hcoeff (jl : ℕ × ℕ) (n m : ℤ) (z w : ℂ) :
      |⟪A jl (lp.single 2 m z), lp.single 2 n w⟫_ℝ| ≤
        ‖z‖*‖w‖*(K jl (lp.single 2 m 1) n).re := by
    apply coefficient_bound
    intro v n
    have h := chartWord_domination hL hκ hr hs u ((fourierR L).symm v) hus jl n
    change ‖chartWordDerivative hL hκ hr hs u jl ((fourierR L).symm v) n‖ ≤
      (chartWordKernel hL hκ hr hs u jl (moduli v) n).re
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h
  refine ⟨hd.1, by simpa only [ContinuousLinearMap.adjoint.norm_map] using hd.1,
    hA, hsA, by simpa only [ContinuousLinearMap.adjoint.norm_map] using hA,
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hsA,
    hpos, htrans, hcoeff, ?_, ?_, ?_⟩
  · intro jl n m z w
    rw [ContinuousLinearMap.adjoint_inner_right, htrans]
    exact hcoeff jl n m z w
  · intro jl
    apply finite_kernel_bound (by norm_num) (fun n m => by unfold absoluteBlock; positivity)
    · intro n m
      have h := hpos jl (lp.single 2 m 1) n
      rw [moduli_single] at h
      exact h
    · exact absoluteBlock_bound (hcoeff jl)
  · intro jl
    apply finite_kernel_bound (by norm_num) (fun n m => by unfold absoluteBlock; positivity)
    · intro n m
      rw [htrans jl m n]
      have h := hpos jl (lp.single 2 n 1) m
      rw [moduli_single] at h
      exact h
    · intro n m
      rw [absoluteBlock_adjoint, htrans jl m n]
      exact absoluteBlock_bound (hcoeff jl) m n

end QuantumNLS.Local006.ChartKernelJ


#print axioms QuantumNLS.Local006.ChartKernelJ.actual_chart_derivative_words
#print axioms QuantumNLS.Local006.ChartKernelJ.actual_chart_absolute_kernel_series
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.ChartKernelJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006ChartKernelJ" then
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
  Lean.logInfo m!"Local006ChartKernelJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

