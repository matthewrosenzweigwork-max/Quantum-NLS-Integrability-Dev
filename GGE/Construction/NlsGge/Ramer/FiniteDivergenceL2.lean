import NlsGge.Ramer.DivergenceIdentification
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite-dimensional `L²` estimate for the Gaussian divergence (obligation R1)

`V` is a finite-dimensional real inner product space with its standard Gaussian
`finiteStdGaussian V` and divergence `finiteGaussianDivergence F x = ⟪x, F x⟫ - tr DF(x)`.

For a compactly supported `C²` vector field `F : V → V` we prove the cylindrical form of
Nualart, *The Malliavin Calculus and Related Topics*, 2nd ed., Prop. 1.3.1 / eq. (1.46)
(Ramer 1974, Lemma 4.1):

  `∫ (δF)² dγ = ∫ ‖F‖² dγ + ∫ tr((DF x)∘(DF x)) dγ(x)`,
  `∫ (δF)² dγ ≤ ∫ ‖F‖² dγ + ∫ ‖DF x‖²_HS dγ(x)`.

Proof route (Nualart, finite-dimensional form): apply the Gaussian integration by parts
(`integral_mul_finiteGaussianDivergence`) with test function `φ = δF`, which is `C¹` with compact
support; expand `D(δF)(F) = ‖F‖² + δ(DF·F) + tr((DF)²)` using the symmetry of `D²F`;
and use `∫ δG dγ = 0` for compactly supported `C¹` fields `G`.

Hypotheses used: `ContDiff ℝ 2 F` and `HasCompactSupport F`. Integrability of every integrand
is a consequence (continuous with compact support against a probability measure); nothing
is assumed.

`hsNormSq A = Σ_{i,j} ⟪b i, A (b j)⟫²` is the squared Hilbert–Schmidt norm, computed in
`stdOrthonormalBasis`; `hsNormSq_eq` proves it equals the same sum in any orthonormal basis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace ContDiff

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Trace and Hilbert–Schmidt norm of a continuous linear endomorphism -/

/-- The trace of a continuous linear endomorphism, as a continuous linear functional. -/
def traceCLM (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : (V →L[ℝ] V) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ V).comp
      (ContinuousLinearMap.coeLM ℝ : (V →L[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V)))

theorem traceCLM_apply (A : V →L[ℝ] V) :
    traceCLM V A = LinearMap.trace ℝ V (A : V →ₗ[ℝ] V) := rfl

theorem traceCLM_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) :
    traceCLM V A = ∑ i, ⟪b i, A (b i)⟫ := by
  rw [traceCLM_apply]; exact LinearMap.trace_eq_sum_inner _ b

/-- Squared Hilbert–Schmidt norm, computed in the standard orthonormal basis. -/
def hsNormSq (A : V →L[ℝ] V) : ℝ :=
  ∑ i, ∑ j, ⟪stdOrthonormalBasis ℝ V i, A (stdOrthonormalBasis ℝ V j)⟫ ^ 2

theorem hsNormSq_nonneg (A : V →L[ℝ] V) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The Hilbert–Schmidt sum in any orthonormal basis equals `tr(A* A)`. -/
theorem sum_sq_inner_eq_trace_adjoint {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (A : V →L[ℝ] V) :
    ∑ i, ∑ j, ⟪b i, A (b j)⟫ ^ 2 = traceCLM V ((ContinuousLinearMap.adjoint A).comp A) := by
  rw [traceCLM_eq_sum b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ i, ⟪b i, A (b j)⟫ ^ 2 = ‖A (b j)‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (A (b j))]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

/-- **Basis independence of the Hilbert–Schmidt norm.** -/
theorem hsNormSq_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) :
    ∑ i, ∑ j, ⟪b i, A (b j)⟫ ^ 2 = hsNormSq A := by
  rw [sum_sq_inner_eq_trace_adjoint b, hsNormSq, sum_sq_inner_eq_trace_adjoint]

/-- `tr(A∘A) ≤ ‖A‖²_HS`. -/
theorem traceCLM_comp_self_le (A : V →L[ℝ] V) :
    traceCLM V (A.comp A) ≤ hsNormSq A := by
  set b := stdOrthonormalBasis ℝ V
  have hx : ∀ i, ⟪b i, A (A (b i))⟫ = ∑ j, ⟪b j, A (b i)⟫ * ⟪b i, A (b j)⟫ := by
    intro i
    conv_lhs => rw [← b.sum_repr' (A (b i))]
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, inner_smul_right]
  rw [traceCLM_eq_sum b]
  simp_rw [ContinuousLinearMap.comp_apply, hx]
  have hS : ∑ i, ∑ j, ⟪b j, A (b i)⟫ ^ 2 = hsNormSq A := by
    rw [Finset.sum_comm]; exact hsNormSq_eq b A
  have hle : ∑ i, ∑ j, ⟪b j, A (b i)⟫ * ⟪b i, A (b j)⟫ ≤
      ∑ i, ∑ j, ((⟪b j, A (b i)⟫ ^ 2 + ⟪b i, A (b j)⟫ ^ 2) / 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      nlinarith [sq_nonneg (⟪b j, A (b i)⟫ - ⟪b i, A (b j)⟫)]
  refine hle.trans (le_of_eq ?_)
  simp_rw [← Finset.sum_div, Finset.sum_add_distrib, hS, hsNormSq_eq b]
  ring

section Divergence

variable [MeasurableSpace V] [BorelSpace V]

theorem finiteGaussianDivergence_eq_traceCLM (F : V → V) (x : V) :
    finiteGaussianDivergence F x = ⟪x, F x⟫ - traceCLM V (fderiv ℝ F x) := rfl

/-- `δF` is `C¹` when `F` is `C²`. -/
theorem contDiff_finiteGaussianDivergence {F : V → V} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (finiteGaussianDivergence F) := by
  have h1 : ContDiff ℝ 1 (fun x => ⟪x, F x⟫) :=
    contDiff_id.inner ℝ (hF.of_le (by norm_num))
  have h2 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact h1.sub ((traceCLM V).contDiff.comp h2)

/-- `δG` is continuous for `C¹` fields `G`. -/
theorem continuous_finiteGaussianDivergence {G : V → V} (hG : ContDiff ℝ 1 G) :
    Continuous (finiteGaussianDivergence G) :=
  (continuous_id.inner hG.continuous).sub
    ((traceCLM V).continuous.comp (hG.continuous_fderiv (by norm_num)))

/-- `δF` vanishes outside the topological support of `F`. -/
theorem finiteGaussianDivergence_eq_zero_of_notMem {F : V → V} {x : V} (hx : x ∉ tsupport F) :
    finiteGaussianDivergence F x = 0 := by
  have h0 : F x = 0 := image_eq_zero_of_notMem_tsupport hx
  have h1 : fderiv ℝ F x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  rw [finiteGaussianDivergence_eq_traceCLM, h0, h1]
  simp

theorem hasCompactSupport_finiteGaussianDivergence {F : V → V} (hc : HasCompactSupport F) :
    HasCompactSupport (finiteGaussianDivergence F) :=
  HasCompactSupport.intro hc fun _ hx => finiteGaussianDivergence_eq_zero_of_notMem hx

/-- The derivative of `δF` for `C²` fields `F`. -/
theorem fderiv_finiteGaussianDivergence_apply {F : V → V} (hF : ContDiff ℝ 2 F) (x v : V) :
    fderiv ℝ (finiteGaussianDivergence F) x v =
      ⟪v, F x⟫ + ⟪x, fderiv ℝ F x v⟫ - traceCLM V (fderiv ℝ (fderiv ℝ F) x v) := by
  have hFd : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiable (by norm_num) x).hasFDerivAt
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have h1 := (hasFDerivAt_id x).inner ℝ hFd
  have h2 : HasFDerivAt (fun y => traceCLM V (fderiv ℝ F y))
      ((traceCLM V).comp (fderiv ℝ (fderiv ℝ F) x)) x := (traceCLM V).hasFDerivAt.comp x hA
  have h3 := h1.sub h2
  have h4 : HasFDerivAt (finiteGaussianDivergence F) _ x := h3
  rw [h4.fderiv]
  simp [fderivInnerCLM_apply]
  ring

/-- `∫ δG dγ = 0` for compactly supported `C¹` fields. -/
theorem integral_finiteGaussianDivergence_eq_zero {G : V → V} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) :
    ∫ x, finiteGaussianDivergence G x ∂(finiteStdGaussian V) = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : V)).1 hc.isCompact.isBounded
  let f : ContDiffBump (0 : V) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hsub : tsupport G ⊆ Metric.ball (0 : V) f.rIn := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]
    show dist x 0 < |R| + 1
    linarith [le_abs_self R]
  have hibp := integral_mul_finiteGaussianDivergence (V := V) (fun x => f x) G
    (f.contDiff) f.hasCompactSupport hG
  have hl : ∀ x, f x * finiteGaussianDivergence G x = finiteGaussianDivergence G x := by
    intro x
    by_cases hx : x ∈ tsupport G
    · rw [f.one_of_mem_closedBall (Metric.ball_subset_closedBall (hsub hx)), one_mul]
    · rw [finiteGaussianDivergence_eq_zero_of_notMem hx, mul_zero]
  have hr : ∀ x, fderiv ℝ (fun y => (f y : ℝ)) x (G x) = 0 := by
    intro x
    by_cases hx : x ∈ tsupport G
    · have := (f.eventuallyEq_one_of_mem_ball (hsub hx)).fderiv_eq (𝕜 := ℝ)
      rw [this]; simp
    · rw [image_eq_zero_of_notMem_tsupport hx, map_zero]
  simp_rw [hl, hr] at hibp
  simpa using hibp

/-- The field `G = DF · F`. -/
def derivField (F : V → V) (x : V) : V := fderiv ℝ F x (F x)

theorem contDiff_derivField {F : V → V} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (derivField F) :=
  (hF.fderiv_right (m := 1) (by norm_num)).clm_apply (hF.of_le (by norm_num))

theorem hasCompactSupport_derivField {F : V → V} (hc : HasCompactSupport F) :
    HasCompactSupport (derivField F) :=
  HasCompactSupport.intro hc fun x hx => by
    simp [derivField, image_eq_zero_of_notMem_tsupport hx]

/-- Pointwise expansion `D(δF)(F) = ‖F‖² + δ(DF·F) + tr((DF)²)` (symmetry of `D²F` is used). -/
theorem fderiv_finiteGaussianDivergence_self {F : V → V} (hF : ContDiff ℝ 2 F) (x : V) :
    fderiv ℝ (finiteGaussianDivergence F) x (F x) =
      ‖F x‖ ^ 2 + finiteGaussianDivergence (derivField F) x +
        traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x)) := by
  have hFd : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiable (by norm_num) x).hasFDerivAt
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have hG : HasFDerivAt (derivField F)
      ((fderiv ℝ F x).comp (fderiv ℝ F x) + (fderiv ℝ (fderiv ℝ F) x).flip (F x)) x :=
    hA.clm_apply hFd
  have hsymm := (hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hflip : (fderiv ℝ (fderiv ℝ F) x).flip (F x) = fderiv ℝ (fderiv ℝ F) x (F x) := by
    ext v
    exact hsymm v (F x)
  rw [fderiv_finiteGaussianDivergence_apply hF, finiteGaussianDivergence_eq_traceCLM,
    hG.fderiv, hflip, map_add, real_inner_self_eq_norm_sq]
  simp only [derivField]
  ring

theorem integrable_of_continuous_of_forall_notMem {F : V → V} (hc : HasCompactSupport F)
    {h : V → ℝ} (hh : Continuous h) (h0 : ∀ x, x ∉ tsupport F → h x = 0) :
    Integrable h (finiteStdGaussian V) :=
  hh.integrable_of_hasCompactSupport (HasCompactSupport.intro hc h0)

/-- **Cylindrical `L²` divergence identity** (Nualart, Prop. 1.3.1 / (1.46), finite-dimensional
form; Ramer 1974, Lemma 4.1): for a compactly supported `C²` field `F`,
`∫ (δF)² dγ = ∫ ‖F‖² dγ + ∫ tr((DF)²) dγ`. -/
theorem integral_sq_finiteGaussianDivergence {F : V → V} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) :
    ∫ x, (finiteGaussianDivergence F x) ^ 2 ∂(finiteStdGaussian V) =
      ∫ x, ‖F x‖ ^ 2 ∂(finiteStdGaussian V) +
        ∫ x, traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x)) ∂(finiteStdGaussian V) := by
  have hA : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF0 : ∀ x, x ∉ tsupport F → F x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hA0 : ∀ x, x ∉ tsupport F → fderiv ℝ F x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  have hibp := integral_mul_finiteGaussianDivergence (V := V) (finiteGaussianDivergence F) F
    (contDiff_finiteGaussianDivergence hF) (hasCompactSupport_finiteGaussianDivergence hc) hF1
  have hI1 : Integrable (fun x => ‖F x‖ ^ 2) (finiteStdGaussian V) :=
    integrable_of_continuous_of_forall_notMem hc (by have := hF1.continuous; fun_prop)
      (fun x hx => by simp [hF0 x hx])
  have hI2 : Integrable (fun x => traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x)))
      (finiteStdGaussian V) :=
    integrable_of_continuous_of_forall_notMem hc
      ((traceCLM V).continuous.comp (hA.continuous.clm_comp hA.continuous))
      (fun x hx => by simp [hA0 x hx])
  have hI3 : Integrable (fun x => finiteGaussianDivergence (derivField F) x)
      (finiteStdGaussian V) :=
    (continuous_finiteGaussianDivergence (contDiff_derivField hF)).integrable_of_hasCompactSupport
      (hasCompactSupport_finiteGaussianDivergence (hasCompactSupport_derivField hc))
  have hzero := integral_finiteGaussianDivergence_eq_zero (contDiff_derivField hF)
    (hasCompactSupport_derivField hc)
  have h12 : Integrable (fun x => ‖F x‖ ^ 2 + finiteGaussianDivergence (derivField F) x)
      (finiteStdGaussian V) := hI1.add hI3
  rw [show (fun x => (finiteGaussianDivergence F x) ^ 2) =
      fun x => finiteGaussianDivergence F x * finiteGaussianDivergence F x from
      funext fun x => pow_two _, hibp]
  simp_rw [fderiv_finiteGaussianDivergence_self hF]
  rw [integral_add h12 hI2, integral_add hI1 hI3, hzero, add_zero]

theorem continuous_hsNormSq_fderiv {F : V → V} (hF : ContDiff ℝ 2 F) :
    Continuous (fun x => hsNormSq (fderiv ℝ F x)) := by
  have hA : Continuous (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuous
  unfold hsNormSq
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_const.inner (hA.clm_apply continuous_const)).pow 2

/-- **Cylindrical `L²` divergence estimate** (Nualart, Prop. 1.3.1 / (1.46); Ramer 1974,
Lemma 4.1; v2 `eq:divergenceestimate`, finite-dimensional form): for compactly supported
`C²` `F`, `∫ (δF)² dγ ≤ ∫ ‖F‖² dγ + ∫ ‖DF x‖²_HS dγ(x)`. -/
theorem integral_sq_finiteGaussianDivergence_le {F : V → V} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) :
    ∫ x, (finiteGaussianDivergence F x) ^ 2 ∂(finiteStdGaussian V) ≤
      ∫ x, ‖F x‖ ^ 2 ∂(finiteStdGaussian V) +
        ∫ x, hsNormSq (fderiv ℝ F x) ∂(finiteStdGaussian V) := by
  have hA : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hA0 : ∀ x, x ∉ tsupport F → fderiv ℝ F x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  rw [integral_sq_finiteGaussianDivergence hF hc]
  refine add_le_add_right (integral_mono ?_ ?_ fun x => traceCLM_comp_self_le _) _
  · exact integrable_of_continuous_of_forall_notMem hc
      ((traceCLM V).continuous.comp (hA.continuous.clm_comp hA.continuous))
      (fun x hx => by simp [hA0 x hx])
  · exact integrable_of_continuous_of_forall_notMem hc (continuous_hsNormSq_fderiv hF)
      (fun x hx => by simp [hA0 x hx, hsNormSq])

/-- The same estimate with the Hilbert–Schmidt norm computed in an arbitrary orthonormal basis. -/
theorem integral_sq_finiteGaussianDivergence_le_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {F : V → V} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) :
    ∫ x, (finiteGaussianDivergence F x) ^ 2 ∂(finiteStdGaussian V) ≤
      ∫ x, ‖F x‖ ^ 2 ∂(finiteStdGaussian V) +
        ∫ x, ∑ i, ∑ j, ⟪b i, fderiv ℝ F x (b j)⟫ ^ 2 ∂(finiteStdGaussian V) := by
  simp_rw [hsNormSq_eq b]
  exact integral_sq_finiteGaussianDivergence_le hF hc

end Divergence

end NlsGge.Ramer
