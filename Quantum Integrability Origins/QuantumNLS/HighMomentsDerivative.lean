import Mathlib
import QuantumNLS.HighMomentsTransfer

/-!
# PROP-008 `lem:B4-high-moments`: spectral-parameter derivative clause on compact sets
(`source/chapters/propagation/spectral_calculus.tex:30-48`)

> "...The estimate is uniform over any parameter family for which those rank sums are uniformly bounded.
> In particular it applies to the actual transfers and their spectral-parameter derivatives on each fixed compact
> set, using the entire bounds of the explicit factorial bound (Q7A:eq:kernels) and Cauchy's estimate."

## Route (operator-valued Cauchy estimate; no termwise differentiation of kernels)
* Part 1 (`expKernel`, `hasDerivAt_expKernel`): the integral operator of `χ(p) e^{izℓ(p)}` (bounded measurable `χ`,
  `0 ≤ ℓ ≤ L`) is complex differentiable in `z` with derivative the operator of `iℓ χ e^{izℓ}`.
* Part 2: `z ↦ K_{r,z} = physicalKernel L r z` (plus and minus raw kernels) is entire as a map into bounded
  symmetric kernels.
* Part 3: `z ↦ Afam z r = κ^r K_{r,z}` is entire; Cauchy's estimate (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`)
  on the circle of radius `R` about `z` with the HMT1 strip bound at `b + R` gives
  `‖∂_z^k A_r(z)‖ ≤ k! R^{-k} · 2 e^{(b+R)L} (κL/r)^r`, hence the rank sums of the derivative family satisfy
  `S_q(∂^k A) ≤ k! R^{-k} M_q(b+R)`.
* Part 4: `∂_z^k S_N(z) = X_N(∂^k A_0, ∂^k A_r)` is the same Xop (genericU is linear), and the centering is the
  derivative of the product symbol, `xlim u (∂^k A_0) (∂^k A) = ∂_z^k s(z)` (locally uniform termwise differentiation
  of the symbol series, Cauchy bounds on the series of derivatives).
* Part 5: the derivative moment theorem, with the explicit hypothesis `hnormal` that `∂_z^k S_N(z)` is normal
  (the source's "normal in the complete Bethe basis"; NOT derived here).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators

noncomputable section

namespace QuantumNLS.HighMomentsDerivative

open QuantumNLS.BetheIntegralOperator QuantumNLS.BetheTransferKernelAdjoint
  QuantumNLS.BetheTransferOperators QuantumNLS.BetheWeakGradient

/-! ### Part 1: complex differentiability of the integral operator of `χ e^{izℓ}` -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Linearity of the integral operator in the kernel function. -/
theorem kernel_operator_lin (k j₁ j₂ j₃ : Kernel μ) (c : ℂ)
    (h : ∀ p, k.fn p = j₁.fn p - j₂.fn p - c * j₃.fn p) :
    k.operator = j₁.operator - j₂.operator - c • j₃.operator := by
  refine ContinuousLinearMap.ext (fun g => ?_)
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_right, inner_sub_right, inner_smul_right, Kernel.inner_operator, Kernel.inner_operator,
    Kernel.inner_operator, Kernel.inner_operator]
  have h1 := j₁.integrable_integrand f g
  have h2 := j₂.integrable_integrand f g
  have h3 := (j₃.integrable_integrand f g).const_mul c
  simp only [Kernel.form]
  have key : ∫ p, k.integrand f g p ∂μ.prod μ =
      ∫ p, ((j₁.integrand f g p - j₂.integrand f g p) - c * j₃.integrand f g p) ∂μ.prod μ := by
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    simp only [Kernel.integrand, h p]
    ring
  have e1 : ∫ p, ((j₁.integrand f g p - j₂.integrand f g p) - c * j₃.integrand f g p) ∂μ.prod μ =
      (∫ p, (j₁.integrand f g p - j₂.integrand f g p) ∂μ.prod μ) -
        ∫ p, c * j₃.integrand f g p ∂μ.prod μ := integral_sub (h1.sub h2) h3
  have e2 : ∫ p, (j₁.integrand f g p - j₂.integrand f g p) ∂μ.prod μ =
      (∫ p, j₁.integrand f g p ∂μ.prod μ) - ∫ p, j₂.integrand f g p ∂μ.prod μ := integral_sub h1 h2
  rw [key, e1, e2, integral_const_mul]

variable (L : ℝ) (hL : 0 ≤ L) (χ : X × X → ℂ) (hχm : Measurable χ) (hχ : ∀ p, ‖χ p‖ ≤ 1)
  (ℓ : X × X → ℝ) (hℓm : Measurable ℓ) (hℓ : ∀ p, 0 ≤ ℓ p ∧ ℓ p ≤ L)

/-- The kernel `(iℓ)^n χ e^{izℓ}`. -/
def expKernel (n : ℕ) (z : ℂ) : Kernel μ where
  fn p := (Complex.I * (ℓ p : ℂ)) ^ n * (χ p * Complex.exp (Complex.I * z * (ℓ p : ℂ)))
  measurable := by
    have hl : Measurable (fun p => (ℓ p : ℂ)) := Complex.measurable_ofReal.comp hℓm
    exact ((measurable_const.mul hl).pow_const n).mul
      (hχm.mul (Complex.continuous_exp.measurable.comp (measurable_const.mul hl)))
  bound := L ^ n * Real.exp (L * |z.im|)
  bound_nonneg := by positivity
  norm_le p := by
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (hℓ p).1]
    have e1 : ℓ p ^ n ≤ L ^ n := pow_le_pow_left₀ (hℓ p).1 (hℓ p).2 n
    have e2 := norm_phase_le L z (hℓ p).1 (hℓ p).2
    have e3 : ‖χ p‖ * ‖Complex.exp (Complex.I * z * (ℓ p : ℂ))‖ ≤ 1 * Real.exp (L * |z.im|) :=
      mul_le_mul (hχ p) e2 (norm_nonneg _) zero_le_one
    calc ℓ p ^ n * (‖χ p‖ * ‖Complex.exp (Complex.I * z * (ℓ p : ℂ))‖)
        ≤ L ^ n * (1 * Real.exp (L * |z.im|)) :=
          mul_le_mul e1 e3 (by positivity) (by positivity)
      _ = L ^ n * Real.exp (L * |z.im|) := by ring

/-- **The operator of `χ e^{izℓ}` is complex differentiable in `z`**, with derivative the operator of
`iℓ χ e^{izℓ}` (Taylor remainder `|e^x − 1 − x| ≤ |x|²` and the crude operator bound). -/
theorem hasDerivAt_expKernel (z : ℂ) :
    HasDerivAt (fun w => (expKernel (μ := μ) L hL χ hχm hχ ℓ hℓm hℓ 0 w).operator)
      ((expKernel (μ := μ) L hL χ hχm hχ ℓ hℓm hℓ 1 z).operator) z := by
  set K := fun n w => expKernel (μ := μ) L hL χ hχm hχ ℓ hℓm hℓ n w with hK
  have hδ : 0 < 1 / (L + 1) := by positivity
  set δ : ℝ := 1 / (L + 1) with hδdef
  set C : ℝ := Real.exp (L * |z.im|) * L ^ 2 * ‖oneVector μ‖ ^ 2 with hC
  have key : ∀ h : ℂ, ‖h‖ ≤ δ →
      ‖(K 0 (z + h)).operator - (K 0 z).operator - h • (K 1 z).operator‖ ≤ C * ‖h‖ ^ 2 := by
    intro h hh
    have hLh : ‖h‖ * L ≤ 1 := by
      have : ‖h‖ * L ≤ (1 / (L + 1)) * L := mul_le_mul_of_nonneg_right hh hL
      have h2 : (1 / (L + 1)) * L ≤ 1 := by
        rw [one_div, inv_mul_le_iff₀ (by positivity)]; linarith
      linarith
    have hpt : ∀ p, ‖(K 0 (z + h)).fn p - (K 0 z).fn p - h * (K 1 z).fn p‖ ≤
        Real.exp (L * |z.im|) * (L ^ 2 * ‖h‖ ^ 2) := by
      intro p
      have hx : ‖Complex.I * h * (ℓ p : ℂ)‖ ≤ 1 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (hℓ p).1]
        calc ‖h‖ * ℓ p ≤ ‖h‖ * L := mul_le_mul_of_nonneg_left (hℓ p).2 (norm_nonneg _)
          _ ≤ 1 := hLh
      have hexp := Complex.norm_exp_sub_one_sub_id_le hx
      have eq : (K 0 (z + h)).fn p - (K 0 z).fn p - h * (K 1 z).fn p =
          χ p * Complex.exp (Complex.I * z * (ℓ p : ℂ)) *
            (Complex.exp (Complex.I * h * (ℓ p : ℂ)) - 1 - Complex.I * h * (ℓ p : ℂ)) := by
        have e1 : Complex.exp (Complex.I * (z + h) * (ℓ p : ℂ)) =
            Complex.exp (Complex.I * z * (ℓ p : ℂ)) * Complex.exp (Complex.I * h * (ℓ p : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; ring
        simp only [hK, expKernel, pow_zero, one_mul, pow_one]
        rw [e1]; ring
      rw [eq, norm_mul, norm_mul]
      have e2 := norm_phase_le L z (hℓ p).1 (hℓ p).2
      have e3 : ‖Complex.I * h * (ℓ p : ℂ)‖ ^ 2 ≤ L ^ 2 * ‖h‖ ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (hℓ p).1]
        have : ‖h‖ * ℓ p ≤ ‖h‖ * L := mul_le_mul_of_nonneg_left (hℓ p).2 (norm_nonneg _)
        nlinarith [mul_nonneg (norm_nonneg h) (hℓ p).1]
      have e4 : ‖χ p‖ * ‖Complex.exp (Complex.I * z * (ℓ p : ℂ))‖ ≤ 1 * Real.exp (L * |z.im|) :=
        mul_le_mul (hχ p) e2 (norm_nonneg _) zero_le_one
      calc ‖χ p‖ * ‖Complex.exp (Complex.I * z * (ℓ p : ℂ))‖ *
            ‖Complex.exp (Complex.I * h * (ℓ p : ℂ)) - 1 - Complex.I * h * (ℓ p : ℂ)‖
          ≤ (1 * Real.exp (L * |z.im|)) * (L ^ 2 * ‖h‖ ^ 2) :=
            mul_le_mul e4 (hexp.trans e3) (norm_nonneg _) (by positivity)
        _ = Real.exp (L * |z.im|) * (L ^ 2 * ‖h‖ ^ 2) := by ring
    let R : Kernel μ :=
      { fn := fun p => (K 0 (z + h)).fn p - (K 0 z).fn p - h * (K 1 z).fn p
        measurable := ((K 0 (z + h)).measurable.sub (K 0 z).measurable).sub
          (measurable_const.mul (K 1 z).measurable)
        bound := Real.exp (L * |z.im|) * (L ^ 2 * ‖h‖ ^ 2)
        bound_nonneg := by positivity
        norm_le := hpt }
    have hR := R.norm_operator_le
    rw [kernel_operator_lin R (K 0 (z + h)) (K 0 z) (K 1 z) h (fun p => rfl)] at hR
    calc _ ≤ _ := hR
      _ = C * ‖h‖ ^ 2 := by simp only [R, hC]; ring
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h : ℂ => (K 0 (z + h)).operator - (K 0 z).operator - h • (K 1 z).operator)
      =O[𝓝 0] (fun h : ℂ => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hδ] with h hh
    rw [mem_closedBall_zero_iff] at hh
    have := key h hh
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using this
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))

end Generic

/-! ### Part 2: entire-ness of `z ↦ K_{r,z}` -/

section Physical

open QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer QuantumNLS.KernelDefinition

variable (L : ℝ) [Fact (0 < L)] (m : ℕ)

open Classical in
/-- Plus chamber indicator (on the canonical representatives). -/
def plusChi (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) : ℂ :=
  if PlusOrder L (representatives L p.1) (representatives L p.2) then 1 else 0

open Classical in
/-- Plus phase length (clamped to `0` outside the chamber). -/
def plusEll (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) : ℝ :=
  if PlusOrder L (representatives L p.1) (representatives L p.2) then
    displacement (representatives L p.1) (representatives L p.2) else 0

open Classical in
/-- Minus chamber indicator. -/
def minusChi (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) : ℂ :=
  if PlusOrder L (representatives L p.2) (representatives L p.1) then 1 else 0

open Classical in
/-- Minus phase length `L − Σ(y_a − x_a)` (clamped to `0` outside the chamber). -/
def minusEll (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) : ℝ :=
  if PlusOrder L (representatives L p.2) (representatives L p.1) then
    L - displacement (representatives L p.2) (representatives L p.1) else 0

theorem measurable_repPair : Measurable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
    (representatives L p.1, representatives L p.2)) :=
  ((measurable_representatives m L).comp measurable_fst).prodMk
    ((measurable_representatives m L).comp measurable_snd)

theorem measurableSet_plusRep : MeasurableSet {p : (Fin m → AddCircle L) × (Fin m → AddCircle L) |
    PlusOrder L (representatives L p.1) (representatives L p.2)} :=
  (measurableSet_plusOrder m L).preimage (measurable_repPair L m)

theorem measurableSet_minusRep : MeasurableSet {p : (Fin m → AddCircle L) × (Fin m → AddCircle L) |
    PlusOrder L (representatives L p.2) (representatives L p.1)} :=
  (measurableSet_plusOrder m L).preimage (measurable_swap.comp (measurable_repPair L m))

theorem measurable_plusChi : Measurable (plusChi L m) := by
  classical
  exact Measurable.ite (measurableSet_plusRep L m) measurable_const measurable_const

theorem measurable_minusChi : Measurable (minusChi L m) := by
  classical
  exact Measurable.ite (measurableSet_minusRep L m) measurable_const measurable_const

theorem measurable_plusEll : Measurable (plusEll L m) := by
  classical
  exact Measurable.ite (measurableSet_plusRep L m)
    ((measurable_displacement m).comp (measurable_repPair L m)) measurable_const

theorem measurable_minusEll : Measurable (minusEll L m) := by
  classical
  exact Measurable.ite (measurableSet_minusRep L m)
    (measurable_const.sub ((measurable_displacement m).comp
      (measurable_swap.comp (measurable_repPair L m)))) measurable_const

theorem norm_plusChi_le (p) : ‖plusChi L m p‖ ≤ 1 := by
  unfold plusChi; split_ifs <;> simp

theorem norm_minusChi_le (p) : ‖minusChi L m p‖ ≤ 1 := by
  unfold minusChi; split_ifs <;> simp

theorem plusEll_bounds (p) : 0 ≤ plusEll L m p ∧ plusEll L m p ≤ L := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  unfold plusEll
  split_ifs with h
  · exact displacement_range hL h
  · exact ⟨le_rfl, hL⟩

theorem minusEll_bounds (p) : 0 ≤ minusEll L m p ∧ minusEll L m p ≤ L := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  unfold minusEll
  split_ifs with h
  · have := displacement_range hL h
    constructor <;> linarith [this.1, this.2]
  · exact ⟨le_rfl, hL⟩

/-- The `n`-th derivative-type kernel `(iℓ)^n χ e^{izℓ}` of the plus chamber. -/
def plusExp (n : ℕ) (z : ℂ) : Kernel (torusPiMeasure L m) :=
  expKernel L (Fact.out : 0 < L).le (plusChi L m) (measurable_plusChi L m) (norm_plusChi_le L m)
    (plusEll L m) (measurable_plusEll L m) (plusEll_bounds L m) n z

/-- The `n`-th derivative-type kernel of the minus chamber. -/
def minusExp (n : ℕ) (z : ℂ) : Kernel (torusPiMeasure L m) :=
  expKernel L (Fact.out : 0 < L).le (minusChi L m) (measurable_minusChi L m) (norm_minusChi_le L m)
    (minusEll L m) (measurable_minusEll L m) (minusEll_bounds L m) n z

theorem plusKernel_operator (z : ℂ) :
    (plusKernel L m z).operator = (plusExp L m 0 z).operator := by
  have := (plusKernel L m z).operator_eq_smul_of_fn (plusExp L m 0 z) 1 (fun p => by
    classical
    simp only [plusKernel, plusExp, expKernel, rawPlus, plusChi, plusEll, one_mul, pow_zero]
    split_ifs <;> simp)
  rw [this, one_smul]

theorem minusKernel_operator (z : ℂ) :
    (minusKernel L m z).operator = (minusExp L m 0 z).operator := by
  have := (minusKernel L m z).operator_eq_smul_of_fn (minusExp L m 0 z) 1 (fun p => by
    classical
    by_cases h : PlusOrder L (representatives L p.2) (representatives L p.1)
    · have h' : MinusOrder L (representatives L p.1) (representatives L p.2) := h
      simp only [minusKernel, minusExp, expKernel, rawMinus, minusChi, minusEll, one_mul, pow_zero,
        h, h', ↓reduceIte]
      congr 1
      simp only [displacement, Complex.ofReal_sub, Complex.ofReal_sum]
      ring
    · have h' : ¬ MinusOrder L (representatives L p.1) (representatives L p.2) := h
      simp [minusKernel, minusExp, expKernel, rawMinus, minusChi, minusEll, h, h'])
  rw [this, one_smul]

theorem hasDerivAt_rawOperator (z : ℂ) :
    HasDerivAt (fun w => rawOperator L m w)
      ((plusExp L m 1 z).operator + (minusExp L m 1 z).operator) z := by
  have h1 := hasDerivAt_expKernel (μ := torusPiMeasure L m) L (Fact.out : 0 < L).le (plusChi L m)
    (measurable_plusChi L m) (norm_plusChi_le L m) (plusEll L m) (measurable_plusEll L m)
    (plusEll_bounds L m) z
  have h2 := hasDerivAt_expKernel (μ := torusPiMeasure L m) L (Fact.out : 0 < L).le (minusChi L m)
    (measurable_minusChi L m) (norm_minusChi_le L m) (minusEll L m) (measurable_minusEll L m)
    (minusEll_bounds L m) z
  have h3 := h1.add h2
  have hfun : (fun w => rawOperator L m w) =
      fun w => (plusExp L m 0 w).operator + (minusExp L m 0 w).operator := by
    funext w
    simp only [rawOperator, plusKernel_operator, minusKernel_operator]
  rw [hfun]
  exact h3

theorem differentiableAt_physicalKernel (z : ℂ) :
    DifferentiableAt ℂ (fun w => physicalKernel L m w) z := by
  have hraw := hasDerivAt_rawOperator L m z
  have hd := ((hasDerivAt_const z (positionInclusion L m).adjoint).clm_comp hraw).clm_comp
    (hasDerivAt_const z (positionInclusion L m))
  exact hd.differentiableAt

theorem differentiable_physicalKernel : Differentiable ℂ (fun w => physicalKernel L m w) :=
  fun z => differentiableAt_physicalKernel L m z

end Physical

/-! ### Part 3: Cauchy estimate for the derivative family -/

section Cauchy

open QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition QuantumNLS.HighMomentsRank
  QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsFinal QuantumNLS.HighMomentsTransfer QuantumNLS.NormalizedTransfer

variable {L : ℝ} [Fact (0 < L)]

theorem differentiable_iteratedDeriv_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    {f : ℂ → E} (hf : Differentiable ℂ f) (k : ℕ) : Differentiable ℂ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Continuous linear maps commute with iterated complex derivatives of entire functions. -/
theorem iteratedDeriv_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (Λ : E →L[ℂ] F) {f : ℂ → E} (hf : Differentiable ℂ f)
    (k : ℕ) : iteratedDeriv k (fun w => Λ (f w)) = fun w => Λ (iteratedDeriv k f w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext w
    have hg := differentiable_iteratedDeriv_aux hf k
    exact (Λ.hasFDerivAt.comp_hasDerivAt w (hg w).hasDerivAt).deriv

/-- `z ↦ A_r(z) = κ^r K_{r,z}` is entire. -/
theorem differentiable_Afam (κ : ℝ) (r : ℕ) : Differentiable ℂ (fun w => Afam L κ w r) := by
  have h := differentiable_physicalKernel L r
  intro w
  show DifferentiableAt ℂ (fun w => ((κ ^ r : ℝ) : ℂ) • physicalKernel L r w) w
  exact DifferentiableAt.const_smul (𝕜 := ℂ) (R := ℂ) (F := BoundedSymmetricKernel (L2T L) r)
    (f := fun w => physicalKernel L r w) (h w) ((κ ^ r : ℝ) : ℂ)

/-- The `k`-th spectral derivative of the coefficient family. -/
def dAfam (L : ℝ) [Fact (0 < L)] (κ : ℝ) (k : ℕ) (z : ℂ) (r : ℕ) : BoundedSymmetricKernel (L2T L) r :=
  iteratedDeriv k (fun w => Afam L κ w r) z

/-- **Cauchy estimate for the derivative kernels**: on the circle of radius `R` about `z` (`Im z ≥ −b`) the HMT1 strip
bound holds with `b + R`, so `‖∂_z^k A_{j+1}(z)‖ ≤ k! R^{-k} · 2 e^{(b+R)L} (κL/(j+1))^{j+1}`. -/
theorem norm_dAfam_le {κ : ℝ} (hκ : 0 ≤ κ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (z : ℂ)
    (hz : -b ≤ z.im) (k j : ℕ) :
    ‖dAfam L κ k z (j + 1)‖ ≤
      (k.factorial : ℝ) / R ^ k * (2 * Real.exp ((b + R) * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1)) := by
  have hsph : ∀ w ∈ Metric.sphere z R, ‖Afam L κ w (j + 1)‖ ≤
      2 * Real.exp ((b + R) * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1) := by
    intro w hw
    have hn : ‖w - z‖ = R := by simpa [mem_sphere_iff_norm] using hw
    have him : -(b + R) ≤ w.im := by
      have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h2 := (abs_le.mp h1).1
      simp only [Complex.sub_im] at h2
      linarith
    exact norm_Afam_le (L := L) hκ (by linarith) w him j
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := BoundedSymmetricKernel (L2T L) (j + 1))
    (c := z) (R := R) (f := fun w => Afam L κ w (j + 1)) k hR
    (differentiable_Afam (L := L) κ (j + 1)).diffContOnCl hsph
  unfold dAfam
  calc _ ≤ _ := this
    _ = _ := by ring

theorem summable_rankSum_der {κ : ℝ} (hκ : 0 ≤ κ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (z : ℂ)
    (hz : -b ≤ z.im) (k q : ℕ) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖dAfam L κ k z (j + 1)‖) := by
  have hc : 0 ≤ κ * L := mul_nonneg hκ (Fact.out : 0 < L).le
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_Mterm L κ hc q).mul_left ((k.factorial : ℝ) / R ^ k * (2 * Real.exp ((b + R) * L))))
  have h := norm_dAfam_le (L := L) hκ hb hR z hz k j
  unfold Mterm
  calc ((j + 1 : ℕ) : ℝ) ^ q * ‖dAfam L κ k z (j + 1)‖
      ≤ ((j + 1 : ℕ) : ℝ) ^ q * ((k.factorial : ℝ) / R ^ k *
          (2 * Real.exp ((b + R) * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- **Rank sums of the derivative family**: `S_q(∂_z^k A) ≤ k! R^{-k} M_q(b+R)`, uniformly for `Im z ≥ −b`. -/
theorem rankSum_der_le {κ : ℝ} (hκ : 0 ≤ κ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (z : ℂ)
    (hz : -b ≤ z.im) (k q : ℕ) :
    Sq (dAfam L κ k z) q ≤ (k.factorial : ℝ) / R ^ k * Mq L κ (b + R) q := by
  have hc : 0 ≤ κ * L := mul_nonneg hκ (Fact.out : 0 < L).le
  unfold Sq Mq
  have e : (k.factorial : ℝ) / R ^ k * (2 * Real.exp ((b + R) * L) * ∑' j, Mterm L κ q j) =
      ∑' j, (k.factorial : ℝ) / R ^ k * (2 * Real.exp ((b + R) * L) * Mterm L κ q j) := by
    rw [tsum_mul_left, tsum_mul_left]
  rw [e]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_rankSum_der hκ hb hR z hz k q)
    ((((summable_Mterm L κ hc q).mul_left (2 * Real.exp ((b + R) * L))).mul_left _))
  have h := norm_dAfam_le (L := L) hκ hb hR z hz k j
  unfold Mterm
  calc ((j + 1 : ℕ) : ℝ) ^ q * ‖dAfam L κ k z (j + 1)‖
      ≤ ((j + 1 : ℕ) : ℝ) ^ q * ((k.factorial : ℝ) / R ^ k *
          (2 * Real.exp ((b + R) * L) * (κ * L / (j + 1 : ℕ)) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The uniform constant of the derivative moment bound. -/
def Cder (L κ b R : ℝ) (k p : ℕ) : ℝ :=
  CpS (fun q => (k.factorial : ℝ) / R ^ k * Mq L κ (b + R) q) p

end Cauchy

/-! ### Part 4: the derivative of the actual transfer is again an `Xop` -/

section XopDeriv

open QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition QuantumNLS.HighMomentsRank
  QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsFinal QuantumNLS.HighMomentsTransfer
  QuantumNLS.NormalizedTransfer QuantumNLS.TensorCarrier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `genericU_N_r N r` as a linear map in the kernel (`RootOverlapLimit.genericU_add/smul`). -/
def Ulin0 (N r : ℕ) (hr : r ≤ N) : BoundedSymmetricKernel H r →ₗ[ℂ]
    (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) where
  toFun A := genericU_N_r N r hr A
  map_add' A B := QuantumNLS.RootOverlapLimit.genericU_add (H := H) N r hr A B
  map_smul' c A := by
    simpa using QuantumNLS.RootOverlapLimit.genericU_smul (H := H) N r hr c A

/-- `genericU_N_r N r` as a continuous linear map in the kernel (contractive by `norm_genericU_N_r_le`). -/
def Ulin (N r : ℕ) (hr : r ≤ N) : BoundedSymmetricKernel H r →L[ℂ]
    (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) where
  toLinearMap := Ulin0 (H := H) N r hr
  cont := by
    have h : Continuous (Ulin0 (H := H) N r hr) :=
      AddMonoidHomClass.continuous_of_bound (Ulin0 (H := H) N r hr) 1 (fun A : BoundedSymmetricKernel H r => by
        show ‖genericU_N_r (H := H) N r hr A‖ ≤ 1 * ‖A‖
        rw [one_mul]
        exact norm_genericU_N_r_le (H := H) N r hr A)
    exact h

theorem Ulin_apply (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r) :
    Ulin (H := H) N r hr A = genericU_N_r N r hr A := rfl

/-- The scalar part of `Xop` as a continuous linear map. -/
def Lam0 (N : ℕ) : ℂ →L[ℂ] (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :=
  ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ (SymSector ℂ H N))

/-- The rank-`j+1` part of `Xop` as a continuous linear map in the kernel. -/
def LamJ (N : ℕ) (j : Fin N) : BoundedSymmetricKernel H (j.val + 1) →L[ℂ]
    (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :=
  ((fallR N (j.val + 1) : ℝ) : ℂ) • Ulin (H := H) N (j.val + 1) j.2

theorem Xop_eq_lin (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    Xop A0 A N = Lam0 (H := H) N A0 + ∑ j : Fin N, LamJ (H := H) N j (A (j.val + 1)) := by
  unfold Xop
  congr 1
  rw [Finset.sum_range (fun j => ((fallR N (j + 1) : ℝ) : ℂ) • placed A N (j + 1))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold placed
  rw [dif_pos (show (j : ℕ) + 1 ≤ N from j.2)]
  rfl

/-- **Spectral derivatives commute with `Xop`**: `∂_z^k X_N(A_0(z), A(z)) = X_N(∂^k A_0, ∂^k A)`. -/
theorem iteratedDeriv_Xop (a0 : ℂ → ℂ) (A : ℂ → ∀ r : ℕ, BoundedSymmetricKernel H r)
    (ha0 : Differentiable ℂ a0) (hA : ∀ r, Differentiable ℂ (fun w => A w r)) (N k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => Xop (a0 w) (A w) N) z =
      Xop (iteratedDeriv k a0 z) (fun r => iteratedDeriv k (fun w => A w r) z) N := by
  have hfun : (fun w => Xop (a0 w) (A w) N) =
      fun w => Lam0 (H := H) N (a0 w) + ∑ j : Fin N, LamJ (H := H) N j (A w (j.val + 1)) :=
    funext fun w => Xop_eq_lin _ _ _
  have hf1 : ContDiff ℂ k (fun w => Lam0 (H := H) N (a0 w)) := by
    have d0 : Differentiable ℂ (Lam0 (H := H) N) := (Lam0 (H := H) N).differentiable
    have d1 : Differentiable ℂ (fun w => Lam0 (H := H) N (a0 w)) :=
      Differentiable.comp (𝕜 := ℂ) (E := ℂ) (F := ℂ)
        (G := SymSector ℂ H N →L[ℂ] SymSector ℂ H N) d0 ha0
    exact d1.contDiff
  have hf2 : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      ContDiff ℂ k (fun w => LamJ (H := H) N j (A w (j.val + 1))) := by
    intro j _
    have d0 : Differentiable ℂ (LamJ (H := H) N j) := (LamJ (H := H) N j).differentiable
    have d1 : Differentiable ℂ (fun w => LamJ (H := H) N j (A w (j.val + 1))) :=
      Differentiable.comp (𝕜 := ℂ) (E := ℂ) (F := BoundedSymmetricKernel H (j.val + 1))
        (G := SymSector ℂ H N →L[ℂ] SymSector ℂ H N) d0 (hA _)
    exact d1.contDiff
  have hf3 : ContDiff ℂ k (fun w => ∑ j : Fin N, LamJ (H := H) N j (A w (j.val + 1))) :=
    ContDiff.sum hf2
  rw [hfun, iteratedDeriv_fun_add hf1.contDiffAt hf3.contDiffAt,
    iteratedDeriv_fun_sum (fun j hj => (hf2 j hj).contDiffAt)]
  have c0 := iteratedDeriv_clm (E := ℂ) (F := SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (Lam0 (H := H) N) (f := a0) ha0 k
  rw [c0]
  rw [Xop_eq_lin]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have c1 := iteratedDeriv_clm (E := BoundedSymmetricKernel H (j.val + 1))
    (F := SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (LamJ (H := H) N j)
    (f := fun w => A w (j.val + 1)) (hA _) k
  rw [c1]

end XopDeriv

section XopDerivActual

open QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition QuantumNLS.HighMomentsRank
  QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsFinal QuantumNLS.HighMomentsTransfer
  QuantumNLS.NormalizedTransfer QuantumNLS.TensorCarrier

variable {L : ℝ} [Fact (0 < L)]

/-- The `k`-th spectral derivative of the actual normalized transfer is `X_N(∂^k A_0, ∂^k A_r)`. -/
theorem iteratedDeriv_normalizedTransfer (κ : ℝ) (N k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => normalizedTransfer L κ N w) z =
      Xop (iteratedDeriv k (fun w => 1 + Complex.exp (Complex.I * w * L)) z) (dAfam L κ k z) N := by
  have hfun : (fun w => normalizedTransfer L κ N w) =
      fun w => Xop (1 + Complex.exp (Complex.I * w * L)) (Afam L κ w) N :=
    funext fun w => normalizedTransfer_eq_Xop L κ N w
  rw [hfun]
  exact iteratedDeriv_Xop (fun w => 1 + Complex.exp (Complex.I * w * L)) (fun w => Afam L κ w)
    (by fun_prop) (fun r => differentiable_Afam κ r) N k z

end XopDerivActual

/-! ### Part 4b: the derivative of the product symbol is the `xlim` of the derivative family -/

section Symbol

open QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition QuantumNLS.HighMomentsRank
  QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsFinal QuantumNLS.HighMomentsTransfer
  QuantumNLS.NormalizedTransfer QuantumNLS.TensorCarrier

/-- The coherent symbol `A ↦ ⟨u^{⊗r}, A u^{⊗r}⟩` as a continuous linear functional of the kernel. -/
def ellCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : H) (r : ℕ) : BoundedSymmetricKernel H r →L[ℂ] ℂ :=
  (innerSL ℂ (htpow r u : HilbertTensorPower ℂ H r)).comp
    ((SymSector ℂ H r).subtypeL.comp
      (ContinuousLinearMap.apply ℂ (SymSector ℂ H r)
        (⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r)))

theorem ellCLM_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : H) (r : ℕ) (A : BoundedSymmetricKernel H r) :
    ellCLM u r A = kernelProductSymbol A u := rfl

theorem norm_ellCLM_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : H) (hu : ‖u‖ = 1) (r : ℕ) (A : BoundedSymmetricKernel H r) : ‖ellCLM u r A‖ ≤ ‖A‖ := by
  rw [ellCLM_apply]
  unfold kernelProductSymbol
  set x : SymSector ℂ H r := ⟨htpow r u, htpow_mem_symSector r u⟩ with hx
  have h1 : ⟪(htpow r u : HilbertTensorPower ℂ H r), ((A x : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r)⟫_ℂ = ⟪x, A x⟫_ℂ := rfl
  rw [h1]
  have hxn : ‖x‖ = 1 := by
    rw [← Submodule.norm_coe]
    show ‖(htpow r u : HilbertTensorPower ℂ H r)‖ = 1
    rw [norm_htpow, hu, one_pow]
  calc ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by
        gcongr
        exact A.le_opNorm x
    _ = ‖A‖ := by rw [hxn]; ring

variable {L : ℝ} [Fact (0 < L)]

/-- The `n`-th term of the product symbol series, with the scalar `A_0` term placed at index `0`. -/
def symF (L : ℝ) [Fact (0 < L)] (u : L2T L) (κ : ℝ) : ℕ → ℂ → ℂ
  | 0 => fun w => 1 + Complex.exp (Complex.I * w * L)
  | (n + 1) => fun w => ellCLM u (n + 1) (Afam L κ w (n + 1))

theorem differentiable_symF (u : L2T L) (κ : ℝ) (n : ℕ) : Differentiable ℂ (symF L u κ n) := by
  cases n with
  | zero =>
    show Differentiable ℂ (fun w : ℂ => 1 + Complex.exp (Complex.I * w * L))
    fun_prop
  | succ n =>
    have hΛ : Differentiable ℂ (ellCLM u (n + 1)) := (ellCLM u (n + 1)).differentiable
    exact Differentiable.comp (𝕜 := ℂ) (E := ℂ) (F := BoundedSymmetricKernel (L2T L) (n + 1)) (G := ℂ)
      hΛ (differentiable_Afam (L := L) κ (n + 1))

theorem norm_symF_succ_le (u : L2T L) (hu : ‖u‖ = 1) (κ : ℝ) (n : ℕ) (w : ℂ) :
    ‖symF L u κ (n + 1) w‖ ≤ ‖Afam L κ w (n + 1)‖ :=
  norm_ellCLM_le u hu (n + 1) _

theorem summable_symF {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (t : ℂ) :
    Summable (fun n => symF L u κ n t) := by
  refine (summable_nat_add_iff 1).1 ?_
  have h := summable_rankSum (L := L) hκ (abs_nonneg t.im) t (neg_abs_le _) 0
  simp only [pow_zero, one_mul] at h
  exact Summable.of_norm_bounded h (fun n => norm_symF_succ_le u hu κ n t)

theorem productSymbol_eq_tsum {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (w : ℂ) :
    productSymbol L κ u w = ∑' n, symF L u κ n w := by
  rw [Summable.tsum_eq_zero_add (summable_symF hκ u hu w)]
  have hter : ∀ j : ℕ, symbolTerm L κ u w (j + 1) = symF L u κ (j + 1) w := by
    intro j
    show symbolTerm L κ u w (j + 1) = ellCLM u (j + 1) (Afam L κ w (j + 1))
    rw [ellCLM_apply]
    exact (kernelProductSymbol_smul ((κ ^ (j + 1) : ℝ) : ℂ) (orderedKernel L (j + 1) w) u).symm
  have h2 : (∑' j : ℕ, symbolTerm L κ u w (j + 1)) = ∑' j : ℕ, symF L u κ (j + 1) w :=
    tsum_congr hter
  unfold productSymbol
  rw [h2]
  rfl

theorem iteratedDeriv_symF_succ (u : L2T L) (κ : ℝ) (i n : ℕ) (w : ℂ) :
    iteratedDeriv i (symF L u κ (n + 1)) w = ellCLM u (n + 1) (dAfam L κ i w (n + 1)) := by
  have h := iteratedDeriv_clm (E := BoundedSymmetricKernel (L2T L) (n + 1)) (F := ℂ)
    (ellCLM u (n + 1)) (f := fun w => Afam L κ w (n + 1)) (differentiable_Afam (L := L) κ (n + 1)) i
  exact congrFun h w

/-- **The derivative of the product symbol**: `∂_z^k s(z) = x(∂^k A_0, ∂^k A)` (locally uniform termwise
differentiation of the series, using the Cauchy bounds of Part 3). -/
theorem iteratedDeriv_productSymbol {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => productSymbol L κ u w) z =
      xlim u (iteratedDeriv k (fun w => 1 + Complex.exp (Complex.I * w * L)) z) (dAfam L κ k z) := by
  have hfun : (fun w => productSymbol L κ u w) = fun w => ∑' n, symF L u κ n w :=
    funext (productSymbol_eq_tsum hκ u hu)
  rw [hfun]
  have hlocal : ∀ i, 1 ≤ i → i ≤ k → SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin i (fun z => symF L u κ n z) Set.univ) Set.univ := by
    intro i _ _
    simp only [iteratedDerivWithin_univ]
    refine SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_univ ?_
    intro K _ hK
    obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
    have hb : 0 ≤ max C 0 := le_max_right _ _
    have hc : 0 ≤ κ * L := mul_nonneg hκ (Fact.out : 0 < L).le
    refine ⟨fun n : ℕ => (i.factorial : ℝ) / 1 ^ i *
      (2 * Real.exp ((max C 0 + 1) * L) * (κ * L / n) ^ n), ?_, ?_⟩
    · refine (summable_nat_add_iff 1).1 ?_
      have := (summable_Mterm L κ hc 0).mul_left
        ((i.factorial : ℝ) / 1 ^ i * (2 * Real.exp ((max C 0 + 1) * L)))
      refine this.congr (fun j => ?_)
      simp only [Mterm, pow_zero, one_mul]
      push_cast
      ring
    · rw [Filter.eventually_cofinite]
      refine (Set.finite_singleton (0 : ℕ)).subset (fun n hn => ?_)
      by_contra hne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      apply hn
      intro w hw
      have hz : -(max C 0) ≤ w.im := by
        have h1 := (abs_le.mp (Complex.abs_im_le_norm w)).1
        have h2 := hC w hw
        linarith [le_max_left C 0]
      rw [iteratedDeriv_symF_succ]
      refine (norm_ellCLM_le u hu _ _).trans ?_
      have := norm_dAfam_le (L := L) hκ hb one_pos w hz i m
      simpa using this
  have hdiff : ∀ n i r, i ≤ k → r ∈ Set.univ →
      DifferentiableAt ℂ (iteratedDerivWithin i (fun z => symF L u κ n z) Set.univ) r := by
    intro n i r _ _
    simp only [iteratedDerivWithin_univ]
    exact (differentiable_iteratedDeriv_aux (differentiable_symF u κ n) i) r
  have h := iteratedDerivWithin_tsum (𝕜 := ℂ) (s := Set.univ) (f := fun n z => symF L u κ n z) k
    isOpen_univ (Set.mem_univ z) (fun t _ => summable_symF hκ u hu t) hlocal hdiff
  simp only [iteratedDerivWithin_univ] at h
  rw [h]
  have hs : Summable (fun n => iteratedDeriv k (symF L u κ n) z) := by
    refine (summable_nat_add_iff 1).1 ?_
    have h0 := summable_rankSum_der (L := L) hκ (abs_nonneg z.im) one_pos z (neg_abs_le _) k 0
    simp only [pow_zero, one_mul] at h0
    refine Summable.of_norm_bounded h0 (fun n => ?_)
    rw [iteratedDeriv_symF_succ]
    exact norm_ellCLM_le u hu _ _
  rw [Summable.tsum_eq_zero_add hs]
  unfold xlim
  refine congrArg₂ (· + ·) rfl (tsum_congr (fun j => ?_))
  rw [iteratedDeriv_symF_succ]
  rfl

end Symbol

/-! ### Part 5: the derivative moment bound -/

section Final

open QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition QuantumNLS.HighMomentsRank
  QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsFinal QuantumNLS.HighMomentsTransfer
  QuantumNLS.NormalizedTransfer QuantumNLS.TensorCarrier QuantumNLS.HighMomentsOps

variable {L : ℝ} [Fact (0 < L)]

/-- **PROP-008, spectral-parameter derivative clause.**  For `Im z ≥ −b`, any `R > 0`, `k ≥ 0`, `p ≥ 1`, `N ≥ 1`
and unit `u`, put `D = ∂_z^k S_N(z)` (the actual `k`-th spectral derivative of the normalized transfer) and
`d = ∂_z^k s(z)` (the `k`-th derivative of the product symbol).  **If `D` is normal** (`hnormal`: the source's
"normal in the complete Bethe basis", NOT derived here), then
`⟨u^{⊗N}, |D − d|^{2p} u^{⊗N}⟩ = ‖(D − d)^p u^{⊗N}‖² ≤ Cder(b,R,k,p)/N^p` with
`Cder = C_p(k! R^{-k} M_q(b+R))` independent of `N`, `u` and `z`. -/
theorem transfer_moments_deriv {κ : ℝ} (hκ : 0 ≤ κ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (u : L2T L)
    (hu : ‖u‖ = 1) (z : ℂ) (hz : -b ≤ z.im) {N : ℕ} (hN : 0 < N) (k : ℕ)
    (hnormal : Commute
      (ContinuousLinearMap.adjoint (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
      (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
    {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N)) *
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
        iteratedDeriv k (fun w => productSymbol L κ u w) z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cder L κ b R k p / (N : ℝ) ^ p := by
  have e1 := iteratedDeriv_normalizedTransfer (L := L) κ N k z
  have e2 := iteratedDeriv_productSymbol (L := L) hκ u hu k z
  have hZ : Zop u (iteratedDeriv k (fun w => 1 + Complex.exp (Complex.I * w * L)) z)
      (dAfam L κ k z) N =
      iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
        iteratedDeriv k (fun w => productSymbol L κ u w) z •
          (1 : BoundedSymmetricKernel (L2T L) N) := by
    unfold Zop
    rw [e2, e1]
  have hX : Commute (ContinuousLinearMap.adjoint
      (Xop (iteratedDeriv k (fun w => 1 + Complex.exp (Complex.I * w * L)) z) (dAfam L κ k z) N))
      (Xop (iteratedDeriv k (fun w => 1 + Complex.exp (Complex.I * w * L)) z) (dAfam L κ k z) N) := by
    rw [← e1]; exact hnormal
  have hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖dAfam L κ k z (j + 1)‖) :=
    fun q => summable_rankSum_der hκ hb hR z hz k q
  have key := high_moments_of_normal u hu
    (iteratedDeriv k (fun w => 1 + Complex.exp (Complex.I * w * L)) z) (dAfam L κ k z) hsum N hN hX
    p hp
  rw [hZ] at key
  refine ⟨key.1, key.2.trans ?_⟩
  have hmono : Cp (dAfam L κ k z) p ≤ Cder L κ b R k p := by
    rw [Cp_eq_CpS]
    exact CpS_mono (fun q => Sq_nonneg _ q) (fun q => rankSum_der_le hκ hb hR z hz k q) p
  exact div_le_div_of_nonneg_right hmono (by positivity)

/-- **Uniform on a fixed compact set.**  For every compact `K ⊆ ℂ` and all `k, p` there is a constant `C`
(depending only on `L, κ, K, k, p`) such that for every `z ∈ K`, `N ≥ 1`, unit `u`, whenever `∂_z^k S_N(z)` is normal,
`‖(∂_z^k S_N(z) − ∂_z^k s(z))^p u^{⊗N}‖² ≤ C / N^p`. -/
theorem transfer_moments_deriv_compact {κ : ℝ} (hκ : 0 ≤ κ) {K : Set ℂ} (hK : IsCompact K) (k p : ℕ) :
    ∃ C : ℝ, ∀ (u : L2T L), ‖u‖ = 1 → ∀ z ∈ K, ∀ {N : ℕ}, 0 < N →
      Commute (ContinuousLinearMap.adjoint (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) → 1 ≤ p →
      ‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
        iteratedDeriv k (fun w => productSymbol L κ u w) z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤ C / (N : ℝ) ^ p := by
  obtain ⟨C0, hC0⟩ := hK.isBounded.exists_norm_le
  have hb : 0 ≤ max C0 0 := le_max_right _ _
  refine ⟨Cder L κ (max C0 0) 1 k p, fun u hu z hz N hN hnormal hp => ?_⟩
  have hz' : -(max C0 0) ≤ z.im := by
    have h1 := (abs_le.mp (Complex.abs_im_le_norm z)).1
    have h2 := hC0 z hz
    linarith [le_max_left C0 0]
  exact (transfer_moments_deriv hκ hb one_pos u hu z hz' hN k hnormal hp).2

end Final

#print axioms hasDerivAt_expKernel
#print axioms differentiable_Afam
#print axioms iteratedDeriv_Xop
#print axioms norm_dAfam_le
#print axioms rankSum_der_le
#print axioms differentiable_physicalKernel
#print axioms iteratedDeriv_normalizedTransfer
#print axioms iteratedDeriv_productSymbol
#print axioms transfer_moments_deriv
#print axioms transfer_moments_deriv_compact

end QuantumNLS.HighMomentsDerivative
