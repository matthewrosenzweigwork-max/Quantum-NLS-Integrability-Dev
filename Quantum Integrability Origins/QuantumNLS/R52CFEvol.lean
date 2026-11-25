import QuantumNLS.R52CFCount
import QuantumNLS.R52CFDev
import QuantumNLS.Prop020Diag

/-!
# R-52CF5DA1 stage 13a: the actual count evolution against the frozen leading contour evolution

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "All these quantum operators
commute. Multiplying the intensive reconstruction by `N`, using the scalar exponential inequality, and discarding the
scalar correction phase compares the true count evolution with `exp(-iN Σ t_n C^{(0)}_{N,n})` with uniform vector
error `O(N^{-1/2})`."

* `countOp` (`M_{N,n} = N · B_{N,n}`, the actual integer count of the accepted PROP-010 normalized count) and
  `countEvol` (`exp(-i Σ_{n∈F} t_n M_{N,n})`, the literal operator exponential);
* generic: `exp_eigen`, `exp_diff_le` (the scalar exponential inequality `|e^{-ix} - e^{-iy}| ≤ |x - y|` lifted to
  commuting diagonal operators), `norm_exp_diag` (unitarity), `reducedDensityN_phase`;
* **`evol_near`**: near a unit rough center `u`, with the PROP-010 cutoff extensions `f_n, g_n` of `u` for the labels
  `n ∈ F` and a time box `|t_n| ≤ T_n`, there are a neighborhood `U ∋ u`, a rate `ρ_N → 0` and `N₀` such that for every
  `N ≥ N₀`, unit `v ∈ U` and admissible `t` there is a unit phase `c` with
  `‖exp(-iΣ t_n M_{N,n}) v^{⊗N} - c · exp(-iN Σ t_n C^{(0)}_{N,n}) v^{⊗N}‖ ≤ ρ_N`.
No hypothesis is added; all inherited modules are read-only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped InnerProductSpace BigOperators

namespace QuantumNLS.R52CFEvol

open QuantumNLS.Prop010ContourBindingR11
open PhysicalTensor (L2T)
open LabelExactPeriod (rectIntegral)
open TraceClass

/-! ### Generic exponential estimates for commuting diagonal operators -/

section Generic
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (b : HilbertBasis ι ℂ E)

/-- `exp(-iX)` (stated generically, so that no instance search on a concrete operator algebra is needed). -/
def expG (X : E →L[ℂ] E) : E →L[ℂ] E := NormedSpace.exp ((-I) • X)

theorem exp_eigen (A : E →L[ℂ] E) (x : E) (z : ℂ) (hx : A x = z • x) :
    NormedSpace.exp A x = Complex.exp z • x := by
  have hp (k : ℕ) : (A ^ k) x = z ^ k • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ E x)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const x
  apply h1.unique
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, hp, smul_smul, smul_eq_mul,
    ← Complex.exp_eq_exp_ℂ] using h2

theorem exp_diag (X : E →L[ℂ] E) (x : ι → ℝ) (hX : ∀ i, X (b i) = ((x i : ℝ) : ℂ) • b i) (i : ι) :
    expG X (b i) = Complex.exp (-I * (x i : ℂ)) • b i := by
  unfold expG
  apply exp_eigen
  rw [ContinuousLinearMap.smul_apply, hX, smul_smul]

theorem norm_exp_neg_I_mul_sub (x y : ℝ) :
    ‖Complex.exp (-I * (x : ℂ)) - Complex.exp (-I * (y : ℂ))‖ ≤ ‖(((x - y : ℝ)) : ℂ)‖ := by
  have he : Complex.exp (-I * (x : ℂ)) - Complex.exp (-I * (y : ℂ)) =
      Complex.exp (-I * (y : ℂ)) * (Complex.exp (I * (((-(x - y)) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul]
  have h1 : ‖Complex.exp (-I * (y : ℂ))‖ = 1 := by
    rw [show -I * (y : ℂ) = ((-y : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [norm_neg, Complex.norm_real]

/-- **The scalar exponential inequality for commuting diagonal operators.** -/
theorem exp_diff_le (X Y : E →L[ℂ] E) (x y : ι → ℝ) (hX : ∀ i, X (b i) = ((x i : ℝ) : ℂ) • b i)
    (hY : ∀ i, Y (b i) = ((y i : ℝ) : ℂ) • b i) (ψ : E) :
    ‖expG X ψ - expG Y ψ‖ ≤ ‖(X - Y) ψ‖ := by
  have hT : ∀ i, (expG X - expG Y) (b i) =
      (Complex.exp (-I * (x i : ℂ)) - Complex.exp (-I * (y i : ℂ))) • b i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, exp_diag b X x hX, exp_diag b Y y hY, sub_smul]
  have hA : ∀ i, (X - Y) (b i) = (((x i - y i : ℝ)) : ℂ) • b i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, hX, hY, ← sub_smul]
    push_cast
    rfl
  have h := R52CFDev.diag_le b _ _ _ _ hT hA zero_le_one
    (fun i => by rw [one_mul]; exact norm_exp_neg_I_mul_sub (x i) (y i)) ψ
  rw [one_mul] at h
  rw [← ContinuousLinearMap.sub_apply]
  exact h

theorem norm_exp_diag (X : E →L[ℂ] E) (x : ι → ℝ) (hX : ∀ i, X (b i) = ((x i : ℝ) : ℂ) • b i) (ψ : E) :
    ‖expG X ψ‖ = ‖ψ‖ := by
  have h1 := R52CFDev.diag_sq b _ _ (exp_diag b X x hX) ψ
  have h2 := HilbertDiagOp.parseval_hasSum b ψ
  have hn : ∀ i, ‖Complex.exp (-I * (x i : ℂ))‖ = 1 := by
    intro i
    rw [show -I * (x i : ℂ) = ((-x i : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  simp only [hn, one_pow, one_mul] at h1
  have := h1.unique h2
  have h0 := norm_nonneg (expG X ψ)
  have h0' := norm_nonneg ψ
  nlinarith [sq_nonneg (‖expG X ψ‖ - ‖ψ‖), sq_nonneg (‖expG X ψ‖ + ‖ψ‖)]

theorem diag_sum {κ0 : Type*} (F : Finset κ0) (c : κ0 → ℂ) (A : κ0 → E →L[ℂ] E) (a : κ0 → ι → ℂ)
    (hA : ∀ n i, A n (b i) = a n i • b i) (i : ι) :
    (∑ n ∈ F, c n • A n) (b i) = (∑ n ∈ F, c n * a n i) • b i := by
  rw [ContinuousLinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ContinuousLinearMap.smul_apply, hA, smul_smul]

end Generic

theorem reducedDensityN_phase {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (N k : ℕ) (hk : k ≤ N) (ψ : TensorCarrier.HilbertTensorPower ℂ E N) {c : ℂ} (hc : ‖c‖ = 1) :
    PhysicalTensor.reducedDensityN N k hk (c • ψ) = PhysicalTensor.reducedDensityN N k hk ψ := by
  unfold PhysicalTensor.reducedDensityN
  rw [map_smul, Prop020Diag.reducedDensityPower_phase _ _ _ hc]

/-! ### The physical count evolution -/

section Physical
variable (L : ℝ) [Fact (0 < L)] {κ : ℝ}

/-- The actual count `M_{N,n} = N · (M_{N,n}/N)` (eigenvalue `m_n` on the Bethe vector of occupation `m`). -/
def countOp (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (n : ℤ) :
    BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N :=
  ((N : ℝ) : ℂ) • B L hκ hN n

/-- The actual count evolution `exp(-i Σ_{n∈F} t_n M_{N,n})`. -/
def countEvol (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (F : Finset ℤ) (t : ℤ → ℝ) :
    BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N :=
  expG (∑ n ∈ F, ((t n : ℝ) : ℂ) • countOp L hκ hN n)

/-- The frozen leading contour evolution `exp(-iN Σ_{n∈F} t_n C^{(0)}_{N,n})`. -/
def frozenEvol (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (F : Finset ℤ) (t : ℤ → ℝ)
    (f : ℤ → Extension (ℂ × ℂ)) (a b : ℤ → ℝ) (h : ℝ) :
    BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N :=
  expG (((N : ℝ) : ℂ) • ∑ n ∈ F, ((t n : ℝ) : ℂ) • C0 L hκ hN (f n) (a n) (b n) h)

/-- The `C^{(1)}` scalar of stage 11a. -/
def c1v (κ : ℝ) (g : Extension (ℂ × (ℂ × ℂ))) (a b h : ℝ) (v : L2T L) : ℝ :=
  ((I / (2 * Real.pi) : ℂ) * rectIntegral (fun z => g.value (z,
    (NormalizedTransfer.productSymbol L κ v z, deriv (fun w => NormalizedTransfer.productSymbol L κ v w) z)))
    a b h).re

/-- The `C^{(1)}` error rate of stage 11a. -/
def c1rate (κ : ℝ) (g : Extension (ℂ × (ℂ × ℂ))) (a b h : ℝ) (N : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ * ((2 * (b - a) + 4 * h) * (2 * g.constant *
    (Real.sqrt (HighMomentsTransfer.Cunif L κ h 1 / N) + Real.sqrt (HighMomentsDerivative.Cder L κ h 1 1 1 / N))))

theorem c1rate_tendsto (κ : ℝ) (g : Extension (ℂ × (ℂ × ℂ))) (a b h : ℝ) :
    Tendsto (c1rate L κ g a b h) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : ∀ C : ℝ, Tendsto (fun N : ℕ => Real.sqrt (C / N)) atTop (𝓝 0) := by
    intro C
    have h2 : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using h1.const_mul C
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h4
    exact h4
  have h5 := (hs (HighMomentsTransfer.Cunif L κ h 1)).add (hs (HighMomentsDerivative.Cder L κ h 1 1 1))
  have h6 := h5.const_mul (2 * (g.constant : ℝ))
  have h7 := h6.const_mul (2 * (b - a) + 4 * h)
  have h8 := h7.const_mul (2 * Real.pi)⁻¹
  simp only [add_zero, mul_zero] at h8
  exact h8

theorem B_eigen (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (n : ℤ) (i : BetheLabels.MArr N) :
    countOp L hκ hN n (basis L hκ hN i) = (((N : ℝ) * ((i.1 n : ℝ) / N) : ℝ) : ℂ) • basis L hκ hN i := by
  rw [countOp, ContinuousLinearMap.smul_apply, B_basis, smul_smul]
  push_cast
  rfl

/-- **The count evolution against the frozen leading contour evolution, near a rough center.** -/
theorem evol_near (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (F : Finset ℤ) (T : ℤ → ℝ)
    {h r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (f : ℤ → Extension (ℂ × ℂ)) (g : ℤ → Extension (ℂ × (ℂ × ℂ)))
    (hf : ∀ n, ∀ z ∈ PeriodReconstruction.Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w, ‖w - PeriodReconstructionCore.sf L κ
        (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖ < r →
      (f n).value (z, w) = localLog L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w)
    (hg : ∀ n, ∀ z ∈ PeriodReconstruction.Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w v, ‖w - PeriodReconstructionCore.sf L κ
        (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖ < r →
      ‖v‖ ≤ MixedQuadratures.Rbd L κ (h + 1) →
      (g n).value (z, (w, v)) =
        localCorrection L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w v) :
    ∃ U ∈ 𝓝 u, ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ v ∈ U, ‖v‖ = 1 → ∀ t : ℤ → ℝ, (∀ n ∈ F, |t n| ≤ T n) →
      ∃ c : ℂ, ‖c‖ = 1 ∧
        ‖countEvol L hκ hN F t (HighMomentsOps.wvec N v) -
          c • frozenEvol L hκ hN F t f (fun n => RootScalarPeriodR8.cut hκ u (n-1))
            (fun n => RootScalarPeriodR8.cut hκ u n) h (HighMomentsOps.wvec N v)‖ ≤ ρ N := by
  set a : ℤ → ℝ := fun n => RootScalarPeriodR8.cut hκ u (n-1) with ha
  set b : ℤ → ℝ := fun n => RootScalarPeriodR8.cut hκ u n with hb
  have hab : ∀ n, a n ≤ b n := fun n =>
    ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)).le
  choose D hD N₀ U hU hcount using fun n => R52CFCount.count_near L hκ u hu n hh hr (f n) (g n) (hf n) (hg n)
  let ρ : ℕ → ℝ := fun N => ∑ n ∈ F, |T n| * (D n * (N : ℝ)⁻¹ + c1rate L κ (g n) (a n) (b n) h N)
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := tendsto_finsetSum F (fun n _ =>
      ((h1.const_mul (D n)).add (c1rate_tendsto L κ (g n) (a n) (b n) h)).const_mul |T n|)
    simpa [ρ] using this
  refine ⟨⋂ n ∈ F, U n, (Filter.biInter_finset_mem F).mpr fun n _ => hU n, ρ, hρ, F.sup N₀ ⊔ 1, ?_⟩
  intro N hN hNN v hv hv1 t ht
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans le_sup_right hNN
    exact_mod_cast this
  set ψ := HighMomentsOps.wvec N v
  set φ : ℝ := ∑ n ∈ F, t n * c1v L κ (g n) (a n) (b n) h v with hφ
  refine ⟨Complex.exp (-I * (φ : ℂ)), ?_, ?_⟩
  · rw [show -I * (φ : ℂ) = ((-φ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  -- the three commuting diagonal generators
  let X := ∑ n ∈ F, ((t n : ℝ) : ℂ) • countOp L hκ hN n
  let Y1 := ((N : ℝ) : ℂ) • ∑ n ∈ F, ((t n : ℝ) : ℂ) • C L hκ hN (f n) (g n) (a n) (b n) h
  let Y2 := ((N : ℝ) : ℂ) • ∑ n ∈ F, ((t n : ℝ) : ℂ) • C0 L hκ hN (f n) (a n) (b n) h + (φ : ℂ) • 1
  let x : BetheLabels.MArr N → ℝ := fun i => ∑ n ∈ F, t n * ((N : ℝ) * ((i.1 n : ℝ) / N))
  let y1 : BetheLabels.MArr N → ℝ := fun i => (N : ℝ) * ∑ n ∈ F, t n *
    (c0 L hκ hN (f n) (a n) (b n) h i + (N : ℝ)⁻¹ * c1 L hκ hN (g n) (a n) (b n) h i)
  let y2 : BetheLabels.MArr N → ℝ := fun i => (N : ℝ) * ∑ n ∈ F, t n * c0 L hκ hN (f n) (a n) (b n) h i + φ
  have hX : ∀ i, X (basis L hκ hN i) = ((x i : ℝ) : ℂ) • basis L hκ hN i := by
    intro i
    rw [diag_sum _ F _ _ _ (fun n i => B_eigen L hκ hN n i)]
    congr 1
    simp only [x]
    push_cast
    rfl
  have hY1 : ∀ i, Y1 (basis L hκ hN i) = ((y1 i : ℝ) : ℂ) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.smul_apply, diag_sum _ F _ _ _
      (fun n i => C_basis L hκ hN (f n) (g n) (hab n) hh.le i), smul_smul]
    congr 1
    simp only [y1]
    push_cast
    rfl
  have hY2 : ∀ i, Y2 (basis L hκ hN i) = ((y2 i : ℝ) : ℂ) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, diag_sum _ F _ _ _
      (fun n i => C0_basis L hκ hN (f n) (hab n) hh.le i), smul_smul, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ← add_smul]
    congr 1
    simp only [y2]
    push_cast
    rfl
  -- `exp(-iY2) = e^{-iφ} exp(-iNΣtC0)`
  have hsplit : expG Y2 ψ = Complex.exp (-I * (φ : ℂ)) •
      frozenEvol L hκ hN F t f a b h ψ := by
    have hop : expG Y2 = Complex.exp (-I * (φ : ℂ)) • frozenEvol L hκ hN F t f a b h := by
      apply NormalityBridge.clm_ext_basis (basis L hκ hN)
      intro i
      have hY0 : ∀ i, (((N : ℝ) : ℂ) • ∑ n ∈ F, ((t n : ℝ) : ℂ) • C0 L hκ hN (f n) (a n) (b n) h)
          (basis L hκ hN i) = ((((N : ℝ) * ∑ n ∈ F, t n * c0 L hκ hN (f n) (a n) (b n) h i : ℝ)) : ℂ) •
            basis L hκ hN i := by
        intro i
        rw [ContinuousLinearMap.smul_apply, diag_sum _ F _ _ _
          (fun n i => C0_basis L hκ hN (f n) (hab n) hh.le i), smul_smul]
        congr 1
        push_cast
        rfl
      rw [exp_diag _ Y2 y2 hY2, ContinuousLinearMap.smul_apply, frozenEvol, exp_diag _ _ _ hY0, smul_smul,
        ← Complex.exp_add]
      congr 2
      simp only [y2]
      push_cast
      ring
    rw [hop, ContinuousLinearMap.smul_apply]
  have hev : countEvol L hκ hN F t ψ = expG X ψ := rfl
  rw [hev, ← hsplit]
  have e1 := exp_diff_le (basis L hκ hN) X Y1 x y1 hX hY1 ψ
  have e2 := exp_diff_le (basis L hκ hN) Y1 Y2 y1 y2 hY1 hY2 ψ
  -- `X - Y1 = N Σ t_n (B_n - C_n)` and `Y1 - Y2 = Σ t_n (C^{(1)}_n - c^{(1)}_n(v))`
  have hN0 : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (N : ℝ) ≠ 0)
  have hXY : X - Y1 = ∑ n ∈ F, ((t n : ℝ) : ℂ) • (((N : ℝ) : ℂ) • (B L hκ hN n - C L hκ hN (f n) (g n) (a n) (b n) h)) := by
    simp only [X, Y1, countOp, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_sub]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_comm ((N : ℝ) : ℂ) ((t n : ℝ) : ℂ)]
  have hYY : Y1 - Y2 = ∑ n ∈ F, ((t n : ℝ) : ℂ) • (C1 L hκ hN (g n) (a n) (b n) h -
      ((c1v L κ (g n) (a n) (b n) h v : ℝ) : ℂ) • 1) := by
    apply NormalityBridge.clm_ext_basis (basis L hκ hN)
    intro i
    have hA : ∀ n i, (C1 L hκ hN (g n) (a n) (b n) h - ((c1v L κ (g n) (a n) (b n) h v : ℝ) : ℂ) •
        (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N)) (basis L hκ hN i) =
        (((c1 L hκ hN (g n) (a n) (b n) h i : ℝ) : ℂ) - ((c1v L κ (g n) (a n) (b n) h v : ℝ) : ℂ)) •
          basis L hκ hN i := by
      intro n i
      rw [ContinuousLinearMap.sub_apply, C1_basis L hκ hN (g n) (hab n) hh.le, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, sub_smul]
    rw [diag_sum _ F _ _ _ hA, ContinuousLinearMap.sub_apply, hY1, hY2, ← sub_smul]
    congr 1
    have hN' : (N : ℝ) ≠ 0 := by linarith
    have hs : y1 i - y2 i = ∑ n ∈ F, t n * (c1 L hκ hN (g n) (a n) (b n) h i - c1v L κ (g n) (a n) (b n) h v) := by
      simp only [y1, y2, hφ, Finset.mul_sum]
      rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp
      ring
    rw [← Complex.ofReal_sub, hs]
    push_cast
    rfl
  have b1 : ‖(X - Y1) ψ‖ ≤ ∑ n ∈ F, |T n| * (D n * (N : ℝ)⁻¹) := by
    rw [hXY, ContinuousLinearMap.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, norm_smul, norm_smul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hc := hcount n N hN (le_trans (le_trans (Finset.le_sup hn) le_sup_left) hNN) v
      (Set.mem_iInter₂.mp hv n hn) hv1
    have hN' : (0 : ℝ) < N := by linarith
    calc |t n| * (|(N : ℝ)| * ‖(B L hκ hN n - C L hκ hN (f n) (g n) (a n) (b n) h) ψ‖)
        ≤ |T n| * ((N : ℝ) * (D n * ((N : ℝ)⁻¹) ^ 2)) := by
          rw [abs_of_pos hN']
          exact mul_le_mul ((ht n hn).trans (le_abs_self _)) (mul_le_mul_of_nonneg_left hc hN'.le)
            (by positivity) (abs_nonneg _)
      _ = |T n| * (D n * (N : ℝ)⁻¹) := by field_simp
  have b2 : ‖(Y1 - Y2) ψ‖ ≤ ∑ n ∈ F, |T n| * c1rate L κ (g n) (a n) (b n) h N := by
    rw [hYY, ContinuousLinearMap.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hc := R52CFDev.C1_dev L hκ hN (g n) (hab n) hh.le v hv1
    have hr0 : 0 ≤ c1rate L κ (g n) (a n) (b n) h N := (norm_nonneg _).trans hc
    exact mul_le_mul ((ht n hn).trans (le_abs_self _)) hc (norm_nonneg _) (abs_nonneg _)
  calc ‖expG X ψ - expG Y2 ψ‖
      ≤ ‖expG X ψ - expG Y1 ψ‖ +
          ‖expG Y1 ψ - expG Y2 ψ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖(X - Y1) ψ‖ + ‖(Y1 - Y2) ψ‖ := add_le_add e1 e2
    _ ≤ ∑ n ∈ F, |T n| * (D n * (N : ℝ)⁻¹) + ∑ n ∈ F, |T n| * c1rate L κ (g n) (a n) (b n) h N := add_le_add b1 b2
    _ = ρ N := by simp only [ρ, mul_add, Finset.sum_add_distrib]

end Physical

end QuantumNLS.R52CFEvol

#print axioms QuantumNLS.R52CFEvol.evol_near
#print axioms QuantumNLS.R52CFEvol.exp_diff_le
#print axioms QuantumNLS.R52CFEvol.reducedDensityN_phase
