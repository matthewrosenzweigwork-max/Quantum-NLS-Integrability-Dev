import QuantumNLS.Prop010SingleContourR17
import QuantumNLS.RootProductSymbolAnalytic
import QuantumNLS.PhysicalUpperTraceIdentity

/-!
# R-52CF5DA1 stage 11a: concentration of the fixed cutoff contour operators on product vectors

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "Lipschitz continuity of the fixed
cutoff functions and the second-moment transfer estimates then give
`‖(C^{(0)}_{N,n} - I_n(v)) v^{⊗N}‖ + ‖(C^{(1)}_{N,n} - c^{(1)}_n(v)) v^{⊗N}‖ ≤ C_* N^{-1/2}`, `|c^{(1)}_n(v)| ≤ C_*`."

Generic part (a Hilbert basis `b`): diagonal operators satisfy Parseval identities (`diag_sq`), so eigenvalue
comparisons give vector comparisons (`diag_le`, `diag_le2`); the rectangle operator integral `rectOp` of a family
continuous on the rectangle is bounded on a vector by the perimeter times the sup of the family on that vector
(`rectOp_apply_norm_le`).
Physical part, for the actual operators `C^{(0)}`, `C^{(1)}` of the accepted PROP-010 (cutoff extensions `f`, `g`,
rectangle `[a,b] × [-h,h]`), a unit `v` and `N ≥ 1`:
* **`C0_dev`**: `‖(C^{(0)} - I) v^{⊗N}‖ ≤ |(2πκ)⁻¹| (2(b-a)+4h) Lip(f) √(C_1/N)` with the scalar
  `I = -(2πκ)⁻¹ Re ∮ f(z, s(z;v)) dz`;
* **`C1_dev`**: `‖(C^{(1)} - c^{(1)}) v^{⊗N}‖ ≤ (2π)⁻¹ (2(b-a)+4h) · 2 Lip(g) (√(C_1/N) + √(C'_1/N))` with the scalar
  `c^{(1)} = Re((i/2π) ∮ g(z, s(z;v), ∂_z s(z;v)) dz)`, and `|c^{(1)}| ≤ (2π)⁻¹(2(b-a)+4h) bound(g)`;
the second moments are the accepted PROP-008 clauses `transfer_moments_physical` and
`transfer_moments_deriv_physical` (uniform over unit `v` and `|Im z| ≤ h`).
No hypothesis is added; all inherited modules are read-only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped InnerProductSpace BigOperators

namespace QuantumNLS.R52CFDev

open QuantumNLS.Prop010ContourBindingR11
open PhysicalTensor (L2T)
open LabelExactPeriod (rectIntegral)

/-! ### Generic diagonal estimates -/

section Generic
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (b : HilbertBasis ι ℂ E)

theorem diag_sq (T : E →L[ℂ] E) (t : ι → ℂ) (hT : ∀ i, T (b i) = t i • b i) (ψ : E) :
    HasSum (fun i => ‖t i‖ ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2) (‖T ψ‖ ^ 2) := by
  have hh := HilbertDiagOp.parseval_hasSum b (T ψ)
  convert hh using 1
  funext i
  rw [HilbertDiagOp.eig_coeff b T t hT, norm_mul, mul_pow]

theorem le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) (hx : 0 ≤ x) : x ≤ y := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hx, Real.sqrt_sq hy] at this

theorem diag_le (T A : E →L[ℂ] E) (t a : ι → ℂ) (hT : ∀ i, T (b i) = t i • b i)
    (hA : ∀ i, A (b i) = a i • b i) {K : ℝ} (hK : 0 ≤ K) (hle : ∀ i, ‖t i‖ ≤ K * ‖a i‖) (ψ : E) :
    ‖T ψ‖ ≤ K * ‖A ψ‖ := by
  have h1 := diag_sq b T t hT ψ
  have h2 := (diag_sq b A a hA ψ).mul_left (K ^ 2)
  have hle2 : ‖T ψ‖ ^ 2 ≤ K ^ 2 * ‖A ψ‖ ^ 2 := by
    refine hasSum_le (fun i => ?_) h1 h2
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hle i) 2
    have hw : 0 ≤ ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hp hw
    calc ‖t i‖ ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 ≤ (K * ‖a i‖) ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := this
      _ = K ^ 2 * (‖a i‖ ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2) := by ring
  exact le_of_sq (by positivity) (by rw [mul_pow]; exact hle2) (norm_nonneg _)

theorem diag_le2 (T A D : E →L[ℂ] E) (t a d : ι → ℂ) (hT : ∀ i, T (b i) = t i • b i)
    (hA : ∀ i, A (b i) = a i • b i) (hD : ∀ i, D (b i) = d i • b i) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ i, ‖t i‖ ≤ K * (‖a i‖ + ‖d i‖)) (ψ : E) :
    ‖T ψ‖ ≤ 2 * K * (‖A ψ‖ + ‖D ψ‖) := by
  have h1 := diag_sq b T t hT ψ
  have h2 := ((diag_sq b A a hA ψ).add (diag_sq b D d hD ψ)).mul_left (2 * K ^ 2)
  have hle2 : ‖T ψ‖ ^ 2 ≤ 2 * K ^ 2 * (‖A ψ‖ ^ 2 + ‖D ψ‖ ^ 2) := by
    refine hasSum_le (fun i => ?_) h1 h2
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hle i) 2
    have hw : 0 ≤ ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by positivity
    have hsq : (K * (‖a i‖ + ‖d i‖)) ^ 2 ≤ 2 * K ^ 2 * (‖a i‖ ^ 2 + ‖d i‖ ^ 2) := by
      nlinarith [sq_nonneg (‖a i‖ - ‖d i‖), sq_nonneg K]
    have := mul_le_mul_of_nonneg_right (hp.trans hsq) hw
    calc ‖t i‖ ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 ≤ 2 * K ^ 2 * (‖a i‖ ^ 2 + ‖d i‖ ^ 2) * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := this
      _ = 2 * K ^ 2 * (‖a i‖ ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 + ‖d i‖ ^ 2 * ‖⟪b i, ψ⟫_ℂ‖ ^ 2) := by ring
  refine le_of_sq (by positivity) ?_ (norm_nonneg _)
  have hA0 := norm_nonneg (A ψ)
  have hD0 := norm_nonneg (D ψ)
  have key : (2 * K * (‖A ψ‖ + ‖D ψ‖)) ^ 2 = 2 * K ^ 2 * (‖A ψ‖ ^ 2 + ‖D ψ‖ ^ 2) +
      K ^ 2 * (2 * ‖A ψ‖ ^ 2 + 2 * ‖D ψ‖ ^ 2 + 8 * (‖A ψ‖ * ‖D ψ‖)) := by ring
  have hpos : 0 ≤ K ^ 2 * (2 * ‖A ψ‖ ^ 2 + 2 * ‖D ψ‖ ^ 2 + 8 * (‖A ψ‖ * ‖D ψ‖)) := by positivity
  linarith

/-- The rectangle operator integral is bounded on a vector by the perimeter times the sup on the rectangle. -/
theorem rectOp_apply_norm_le (F : ℂ → E →L[ℂ] E) {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hc : ∀ z ∈ PeriodReconstruction.Gam a b h, ContinuousAt F z) (ψ : E) {M : ℝ}
    (hM : ∀ z ∈ PeriodReconstruction.Gam a b h, ‖F z ψ‖ ≤ M) :
    ‖rectOp F a b h ψ‖ ≤ (2 * (b - a) + 4 * h) * M := by
  have ih (y : ℝ) (hy : ∀ x ∈ uIcc a b, (x : ℂ) + y * I ∈ PeriodReconstruction.Gam a b h) :
      IntervalIntegrable (fun x : ℝ => F (x + y * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact ((hc _ (hy x hx)).comp_of_eq (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + y * I) x)
      rfl).continuousWithinAt
  have iv (x : ℝ) (hx : ∀ y ∈ uIcc (-h) h, (x : ℂ) + y * I ∈ PeriodReconstruction.Gam a b h) :
      IntervalIntegrable (fun y : ℝ => F (x + y * I)) volume (-h) h := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact ((hc _ (hx y hy)).comp_of_eq (by fun_prop : ContinuousAt (fun y : ℝ => (x : ℂ) + y * I) y)
      rfl).continuousWithinAt
  simp only [rectOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.intervalIntegral_apply (ih (-h) (fun _ hx => PeriodTwoTerm.bot_mem hab hx)),
    ContinuousLinearMap.intervalIntegral_apply (ih h (fun _ hx => PeriodTwoTerm.top_mem hab hx)),
    ContinuousLinearMap.intervalIntegral_apply (iv b (fun _ hy => PeriodTwoTerm.right_mem hh hy)),
    ContinuousLinearMap.intervalIntegral_apply (iv a (fun _ hy => PeriodTwoTerm.left_mem hh hy))]
  have b1 : ‖∫ x in a..b, F (x + ((-h : ℝ) : ℂ) * I) ψ‖ ≤ M * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hM _ (PeriodTwoTerm.bot_mem hab (Set.uIoc_subset_uIcc hx))
  have b2 : ‖∫ x in a..b, F (x + h * I) ψ‖ ≤ M * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hM _ (PeriodTwoTerm.top_mem hab (Set.uIoc_subset_uIcc hx))
  have b3 : ‖∫ y in (-h)..h, F (b + y * I) ψ‖ ≤ M * |h - -h| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy =>
      hM _ (PeriodTwoTerm.right_mem hh (Set.uIoc_subset_uIcc hy))
  have b4 : ‖∫ y in (-h)..h, F (a + y * I) ψ‖ ≤ M * |h - -h| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy =>
      hM _ (PeriodTwoTerm.left_mem hh (Set.uIoc_subset_uIcc hy))
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at b1 b2
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h - -h)] at b3 b4
  have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  calc _ ≤ ‖∫ x in a..b, F (x + ((-h : ℝ) : ℂ) * I) ψ‖ + ‖∫ x in a..b, F (x + h * I) ψ‖ +
        ‖I • ∫ y in (-h)..h, F (b + y * I) ψ‖ + ‖I • ∫ y in (-h)..h, F (a + y * I) ψ‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl
    _ ≤ M * (b - a) + M * (b - a) + M * (h - -h) + M * (h - -h) := by
        rw [norm_smul, norm_smul, hI, one_mul, one_mul]
        linarith
    _ = (2 * (b - a) + 4 * h) * M := by ring

end Generic

/-! ### The physical contour operators -/

section Physical
variable (L : ℝ) [Fact (0 < L)] {κ : ℝ}

theorem differentiable_symbol_z (hκ : 0 < κ) (v : L2T L) :
    Differentiable ℂ (fun z : ℂ => NormalizedTransfer.productSymbol L κ v z) := by
  have he : (fun z : ℂ => NormalizedTransfer.productSymbol L κ v z) =
      fun z => Complex.exp (Complex.I * z * (L : ℂ) / 2) * L2SpatialTransfer.discriminant κ v z :=
    funext fun z => RootProductSymbolAnalytic.productSymbol_eq_exp_mul_discriminant L κ hκ.le v z
  rw [he]
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * z * (L : ℂ) / 2))).mul
    (PhysicalUpperTraceIdentity.entire_discriminant κ v)

theorem continuous_deriv_symbol_z (hκ : 0 < κ) (v : L2T L) :
    Continuous (deriv (fun z : ℂ => NormalizedTransfer.productSymbol L κ v z)) :=
  (differentiable_symbol_z L hκ v).contDiff.continuous_deriv_one

theorem continuous_ev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (i : BetheLabels.MArr N) :
    Continuous (fun z => ev L hκ hN z i) :=
  (NormalityBridge.eigen_differentiable κ hκ hN i).continuous

theorem continuous_dev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (i : BetheLabels.MArr N) :
    Continuous (fun z => dev L hκ hN z i) :=
  (NormalityBridge.eigen_differentiable κ hκ hN i).contDiff.continuous_deriv_one

theorem im_ge_of_mem {a b h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ PeriodReconstruction.Gam a b h) :
    -h ≤ z.im := by
  rcases hz with ⟨-, h2 | h2⟩ | ⟨h1, -⟩
  · rw [h2]
  · rw [h2]; linarith
  · exact h1.1

/-- The second moment of the transfer deviation, uniform on the strip. -/
theorem transfer_dev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (v : L2T L) (hv : ‖v‖ = 1) {h : ℝ} (hh : 0 ≤ h)
    (z : ℂ) (hz : -h ≤ z.im) :
    ‖(NormalizedTransfer.normalizedTransfer L κ N z - NormalizedTransfer.productSymbol L κ v z •
      (1 : KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (HighMomentsOps.wvec N v)‖ ≤
      Real.sqrt (HighMomentsTransfer.Cunif L κ h 1 / N) := by
  have hm := (UnconditionalBetheBasis.transfer_moments_physical hκ hN hh v hv z hz (p := 1) le_rfl).2
  rw [pow_one, pow_one] at hm
  have := Real.abs_le_sqrt hm
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The second moment of the derivative deviation, uniform on the strip. -/
theorem transfer_deriv_dev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (v : L2T L) (hv : ‖v‖ = 1) {h : ℝ}
    (hh : 0 ≤ h) (z : ℂ) (hz : -h ≤ z.im) :
    ‖(deriv (NormalizedTransfer.normalizedTransfer L κ N) z -
      deriv (fun w => NormalizedTransfer.productSymbol L κ v w) z •
      (1 : KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (HighMomentsOps.wvec N v)‖ ≤
      Real.sqrt (HighMomentsDerivative.Cder L κ h 1 1 1 / N) := by
  have hm := (UnconditionalBetheBasis.transfer_moments_deriv_physical hκ hN hh one_pos v hv z hz 1
    (p := 1) le_rfl).2
  simp only [iteratedDeriv_one, pow_one] at hm
  have := Real.abs_le_sqrt hm
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- **Concentration of `C^{(0)}` on product vectors.** -/
theorem C0_dev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ)) {a b h : ℝ} (hab : a ≤ b)
    (hh : 0 ≤ h) (v : L2T L) (hv : ‖v‖ = 1) :
    ‖(C0 L hκ hN f a b h - (((-(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => f.value (z, NormalizedTransfer.productSymbol L κ v z)) a b h).re : ℝ)) : ℂ) •
        (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
      (HighMomentsOps.wvec N v)‖ ≤
      |(2 * Real.pi * κ)⁻¹| * ((2 * (b - a) + 4 * h) *
        (f.constant * Real.sqrt (HighMomentsTransfer.Cunif L κ h 1 / N))) := by
  set s : ℂ → ℂ := fun z => NormalizedTransfer.productSymbol L κ v z with hs
  have hsc : Continuous s := (differentiable_symbol_z L hκ v).continuous
  set J : ℝ := -(2 * Real.pi * κ)⁻¹ * (rectIntegral (fun z => f.value (z, s z)) a b h).re with hJ
  let T : ℂ → (BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N) :=
    fun z => Fop L hκ hN f z - f.value (z, s z) • 1
  have hfc : Continuous f.value := f.lipschitz.continuous
  have hTc : Continuous T :=
    (Fop_continuous L hκ hN f).sub ((hfc.comp (continuous_id.prodMk hsc)).smul continuous_const)
  have hTe : ∀ z i, T z (basis L hκ hN i) = (f.value (z, ev L hκ hN z i) - f.value (z, s z)) • basis L hκ hN i := by
    intro z i
    simp only [T, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, Fop, lift_basis, sub_smul]
  let Y := rectOp T a b h
  have hYe : ∀ i, Y (basis L hκ hN i) = rectIntegral (fun z => f.value (z, ev L hκ hN z i) - f.value (z, s z)) a b h •
      basis L hκ hN i := fun i => rectOp_basis (basis L hκ hN) T _ hab hh (fun z _ => hTc.continuousAt) hTe i
  have hCe : ∀ i, (C0 L hκ hN f a b h - (J : ℂ) • 1) (basis L hκ hN i) = (((c0 L hκ hN f a b h i : ℝ) : ℂ) - (J : ℂ)) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, C0_basis L hκ hN f hab hh, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul]
  have hle : ∀ i, ‖((c0 L hκ hN f a b h i : ℝ) : ℂ) - (J : ℂ)‖ ≤ |(2 * Real.pi * κ)⁻¹| *
      ‖rectIntegral (fun z => f.value (z, ev L hκ hN z i) - f.value (z, s z)) a b h‖ := by
    intro i
    have hsub : rectIntegral (fun z => f.value (z, ev L hκ hN z i) - f.value (z, s z)) a b h =
        rectIntegral (fun z => f.value (z, ev L hκ hN z i)) a b h - rectIntegral (fun z => f.value (z, s z)) a b h := by
      have hn : (fun z => f.value (z, ev L hκ hN z i) - f.value (z, s z)) =
          fun z => f.value (z, ev L hκ hN z i) + (-1 : ℂ) * f.value (z, s z) := by funext z; ring
      rw [hn, PeriodTwoTerm.rectIntegral_add (f := fun z => f.value (z, ev L hκ hN z i))
        (g := fun z => (-1 : ℂ) * f.value (z, s z)) hab hh
        (fun z _ => (hfc.comp (continuous_id.prodMk (continuous_ev L hκ hN i))).continuousAt)
        (fun z _ => (continuous_const.mul (hfc.comp (continuous_id.prodMk hsc))).continuousAt),
        PeriodTwoTerm.rectIntegral_const_mul]
      ring
    rw [hsub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hc0 : c0 L hκ hN f a b h i - J = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => f.value (z, ev L hκ hN z i)) a b h -
          rectIntegral (fun z => f.value (z, s z)) a b h).re := by
      simp only [c0, hJ, Complex.sub_re]
      ring
    rw [hc0, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
  have h1 := diag_le (basis L hκ hN) (C0 L hκ hN f a b h - (J : ℂ) • 1) Y _ _ hCe hYe (abs_nonneg _) hle
    (HighMomentsOps.wvec N v)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  apply rectOp_apply_norm_le T hab hh (fun z _ => hTc.continuousAt)
  intro z hz
  have hA : ∀ i, (NormalizedTransfer.normalizedTransfer L κ N z - s z •
      (1 : KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (basis L hκ hN i) = (ev L hκ hN z i - s z) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, ev_basis, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul]
  have hlip : ∀ i, ‖f.value (z, ev L hκ hN z i) - f.value (z, s z)‖ ≤ f.constant * ‖ev L hκ hN z i - s z‖ := by
    intro i
    have hl := f.lipschitz.dist_le_mul (z, ev L hκ hN z i) (z, s z)
    rw [Prod.dist_eq, dist_self, dist_eq_norm, dist_eq_norm] at hl
    simpa [max_eq_right (norm_nonneg _)] using hl
  refine (diag_le (basis L hκ hN) (T z) _ _ _ (hTe z) hA f.constant.coe_nonneg hlip (HighMomentsOps.wvec N v)).trans ?_
  exact mul_le_mul_of_nonneg_left (transfer_dev L hκ hN v hv hh z (im_ge_of_mem hh hz))
    f.constant.coe_nonneg

theorem norm_I_div_two_pi : ‖(I / (2 * Real.pi : ℂ))‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_div, Complex.norm_I]
  have : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [this, one_div]

/-- **Concentration of `C^{(1)}` on product vectors.** -/
theorem C1_dev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ))) {a b h : ℝ} (hab : a ≤ b)
    (hh : 0 ≤ h) (v : L2T L) (hv : ‖v‖ = 1) :
    ‖(C1 L hκ hN g a b h - ((((I / (2 * Real.pi) : ℂ) * rectIntegral (fun z => g.value (z,
        (NormalizedTransfer.productSymbol L κ v z,
          deriv (fun w => NormalizedTransfer.productSymbol L κ v w) z))) a b h).re : ℝ) : ℂ) •
        (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
      (HighMomentsOps.wvec N v)‖ ≤
      (2 * Real.pi)⁻¹ * ((2 * (b - a) + 4 * h) * (2 * g.constant *
        (Real.sqrt (HighMomentsTransfer.Cunif L κ h 1 / N) +
          Real.sqrt (HighMomentsDerivative.Cder L κ h 1 1 1 / N)))) := by
  set s : ℂ → ℂ := fun z => NormalizedTransfer.productSymbol L κ v z with hs
  set s' : ℂ → ℂ := fun z => deriv (fun w => NormalizedTransfer.productSymbol L κ v w) z with hs'
  have hsc : Continuous s := (differentiable_symbol_z L hκ v).continuous
  have hsc' : Continuous s' := continuous_deriv_symbol_z L hκ v
  set J : ℝ := ((I / (2 * Real.pi) : ℂ) * rectIntegral (fun z => g.value (z, (s z, s' z))) a b h).re with hJ
  let T : ℂ → (BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N) :=
    fun z => Gop L hκ hN g z - g.value (z, (s z, s' z)) • 1
  have hgc : Continuous g.value := g.lipschitz.continuous
  have hTc : Continuous T :=
    (Gop_continuous L hκ hN g).sub ((hgc.comp (continuous_id.prodMk (hsc.prodMk hsc'))).smul continuous_const)
  have hTe : ∀ z i, T z (basis L hκ hN i) =
      (g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) - g.value (z, (s z, s' z))) • basis L hκ hN i := by
    intro z i
    simp only [T, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, Gop, liftJoint_basis, sub_smul]
  let Y := rectOp T a b h
  have hYe : ∀ i, Y (basis L hκ hN i) = rectIntegral (fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) -
      g.value (z, (s z, s' z))) a b h • basis L hκ hN i :=
    fun i => rectOp_basis (basis L hκ hN) T _ hab hh (fun z _ => hTc.continuousAt) hTe i
  have hCe : ∀ i, (C1 L hκ hN g a b h - (J : ℂ) • 1) (basis L hκ hN i) =
      (((c1 L hκ hN g a b h i : ℝ) : ℂ) - (J : ℂ)) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, C1_basis L hκ hN g hab hh, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul]
  have hle : ∀ i, ‖((c1 L hκ hN g a b h i : ℝ) : ℂ) - (J : ℂ)‖ ≤ (2 * Real.pi)⁻¹ *
      ‖rectIntegral (fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) - g.value (z, (s z, s' z))) a b h‖ := by
    intro i
    have hsub : rectIntegral (fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) -
        g.value (z, (s z, s' z))) a b h =
        rectIntegral (fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i))) a b h -
          rectIntegral (fun z => g.value (z, (s z, s' z))) a b h := by
      have hn : (fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) - g.value (z, (s z, s' z))) =
          fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) + (-1 : ℂ) * g.value (z, (s z, s' z)) := by
        funext z; ring
      rw [hn, PeriodTwoTerm.rectIntegral_add (f := fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i)))
        (g := fun z => (-1 : ℂ) * g.value (z, (s z, s' z))) hab hh
        (fun z _ => (hgc.comp (continuous_id.prodMk ((continuous_ev L hκ hN i).prodMk
          (continuous_dev L hκ hN i)))).continuousAt)
        (fun z _ => (continuous_const.mul (hgc.comp (continuous_id.prodMk (hsc.prodMk hsc')))).continuousAt),
        PeriodTwoTerm.rectIntegral_const_mul]
      ring
    rw [hsub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hc1 : c1 L hκ hN g a b h i - J = ((I / (2 * Real.pi) : ℂ) *
        (rectIntegral (fun z => g.value (z, (ev L hκ hN z i, dev L hκ hN z i))) a b h -
          rectIntegral (fun z => g.value (z, (s z, s' z))) a b h)).re := by
      simp only [c1, hJ, mul_sub, Complex.sub_re]
    rw [hc1, ← norm_I_div_two_pi, ← norm_mul]
    exact Complex.abs_re_le_norm _
  have h1 := diag_le (basis L hκ hN) (C1 L hκ hN g a b h - (J : ℂ) • 1) Y _ _ hCe hYe (by positivity) hle
    (HighMomentsOps.wvec N v)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply rectOp_apply_norm_le T hab hh (fun z _ => hTc.continuousAt)
  intro z hz
  have hA : ∀ i, (NormalizedTransfer.normalizedTransfer L κ N z - s z •
      (1 : KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (basis L hκ hN i) =
        (ev L hκ hN z i - s z) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, ev_basis, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul]
  have hD : ∀ i, (deriv (NormalizedTransfer.normalizedTransfer L κ N) z - s' z •
      (1 : KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (basis L hκ hN i) =
        (dev L hκ hN z i - s' z) • basis L hκ hN i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, dev_basis, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul]
  have hlip : ∀ i, ‖g.value (z, (ev L hκ hN z i, dev L hκ hN z i)) - g.value (z, (s z, s' z))‖ ≤
      g.constant * (‖ev L hκ hN z i - s z‖ + ‖dev L hκ hN z i - s' z‖) := by
    intro i
    have hl := g.lipschitz.dist_le_mul (z, (ev L hκ hN z i, dev L hκ hN z i)) (z, (s z, s' z))
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_eq_norm, dist_eq_norm, dist_eq_norm] at hl
    refine hl.trans (mul_le_mul_of_nonneg_left ?_ g.constant.coe_nonneg)
    refine max_le (by positivity) (max_le ?_ ?_)
    · linarith [norm_nonneg (dev L hκ hN z i - s' z)]
    · linarith [norm_nonneg (ev L hκ hN z i - s z)]
  refine (diag_le2 (basis L hκ hN) (T z) _ _ _ _ _ (hTe z) hA hD g.constant.coe_nonneg hlip
    (HighMomentsOps.wvec N v)).trans ?_
  have hz' := im_ge_of_mem hh hz
  exact mul_le_mul_of_nonneg_left (add_le_add (transfer_dev L hκ hN v hv hh z hz')
    (transfer_deriv_dev L hκ hN v hv hh z hz')) (by positivity)

end Physical

end QuantumNLS.R52CFDev

#print axioms QuantumNLS.R52CFDev.C0_dev
#print axioms QuantumNLS.R52CFDev.C1_dev
#print axioms QuantumNLS.R52CFDev.rectOp_apply_norm_le
