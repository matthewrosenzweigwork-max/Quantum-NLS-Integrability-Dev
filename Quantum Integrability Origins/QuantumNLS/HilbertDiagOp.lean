import Mathlib

/-!
# R-E67FE3C4 item 2 (generic part): diagonal operators in a Hilbert basis

For a Hilbert basis `b` of a complex inner product space `H` and a bounded family `μ : ι → ℂ`:
* `diag_exists`: there is a bounded operator `T` with `⟪b i, T v⟫ = μ i * ⟪b i, v⟫` and `‖T‖ ≤ C`;
* `diag_norm_eq`: its operator norm is the supremum of the moduli `‖μ i‖`;
* `eig_coeff`: a bounded operator with `K (b k) = λ k • b k` satisfies `⟪b k, K v⟫ = λ k * ⟪b k, v⟫`;
* `tendsto_of_norm_sq_tendsto`: squared distances tending to zero give convergence;
* `le_of_sq_le_sq_nonneg`: an elementary square-root comparison.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology

namespace QuantumNLS.HilbertDiagOp

/-- Elementary comparison: `a² ≤ b²` with `b ≥ 0` gives `a ≤ b`. -/
theorem le_of_sq_le_sq_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

/-- Convergence from convergence of squared distances. -/
theorem tendsto_of_norm_sq_tendsto {α E : Type*} [SeminormedAddCommGroup E] {l : Filter α}
    (f : α → E) (x : E) (h : Tendsto (fun a => ‖f a - x‖ ^ 2) l (𝓝 0)) :
    Tendsto f l (𝓝 x) := by
  have h2 : Tendsto (fun a => Real.sqrt (‖f a - x‖ ^ 2)) l (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  exact Tendsto.congr (fun a => Real.sqrt_sq (norm_nonneg _)) h2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} (b : HilbertBasis ι ℂ H)

/-- Parseval for the coefficient sequence: `Σ_i ‖⟪b i, v⟫‖² = ‖v‖²`. -/
theorem parseval_hasSum (v : H) :
    HasSum (fun i => ‖⟪b i, v⟫_ℂ‖ ^ 2) (‖v‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner v v
  have hc : ∀ i, ⟪v, b i⟫_ℂ = conj ⟪b i, v⟫_ℂ := by
    intro i
    rw [← inner_conj_symm (b i) v, Complex.conj_conj]
  have e1 : ∀ i, ⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ = ((‖⟪b i, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [hc i, Complex.conj_mul']
    norm_cast
  have e2 : ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [e2] at h
  have h2 : HasSum (fun i => ((‖⟪b i, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    convert h using 1
    funext i
    exact (e1 i).symm
  exact Complex.hasSum_ofReal.mp h2

/-- Coefficients of a vector built from `ℓ²` coordinates. -/
theorem inner_basis_symm (g : lp (fun _ : ι => ℂ) 2) (i : ι) :
    ⟪b i, b.repr.symm g⟫_ℂ = g i := by
  rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The coefficient sequence `i ↦ μ i * ⟪b i, v⟫` lies in `ℓ²` when `μ` is bounded. -/
theorem memℓp_mul (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) (v : H) :
    Memℓp (fun i => μ i * ⟪b i, v⟫_ℂ) 2 := by
  apply memℓp_gen
  have hs : Summable (fun i => C ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2) :=
    (parseval_hasSum b v).summable.mul_left _
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h2, Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hs
  show ‖μ i * ⟪b i, v⟫_ℂ‖ ^ 2 ≤ C ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC i) 2) (sq_nonneg _)

/-- The `ℓ²` element `i ↦ μ i * ⟪b i, v⟫`. -/
def mulCoeff (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) (v : H) : lp (fun _ : ι => ℂ) 2 :=
  ⟨fun i => μ i * ⟪b i, v⟫_ℂ, memℓp_mul b μ C hC v⟩

theorem mulCoeff_add (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) (v w : H) :
    mulCoeff b μ C hC (v + w) = mulCoeff b μ C hC v + mulCoeff b μ C hC w := by
  apply lp.ext
  funext i
  change μ i * ⟪b i, v + w⟫_ℂ = μ i * ⟪b i, v⟫_ℂ + μ i * ⟪b i, w⟫_ℂ
  rw [inner_add_right, mul_add]

theorem mulCoeff_smul (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) (a : ℂ) (v : H) :
    mulCoeff b μ C hC (a • v) = a • mulCoeff b μ C hC v := by
  apply lp.ext
  funext i
  change μ i * ⟪b i, a • v⟫_ℂ = a * (μ i * ⟪b i, v⟫_ℂ)
  rw [inner_smul_right]
  ring

/-- The diagonal map `v ↦ b.repr.symm (i ↦ μ i * ⟪b i, v⟫)` as a linear map. -/
def diagLinear (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) : H →ₗ[ℂ] H where
  toFun v := b.repr.symm (mulCoeff b μ C hC v)
  map_add' v w := by
    show b.repr.symm (mulCoeff b μ C hC (v + w))
      = b.repr.symm (mulCoeff b μ C hC v) + b.repr.symm (mulCoeff b μ C hC w)
    rw [mulCoeff_add, map_add]
  map_smul' a v := by
    show b.repr.symm (mulCoeff b μ C hC (a • v)) = a • b.repr.symm (mulCoeff b μ C hC v)
    rw [mulCoeff_smul, map_smul]

theorem diagLinear_norm_le (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) (hC0 : 0 ≤ C) (v : H) :
    ‖diagLinear b μ C hC v‖ ≤ C * ‖v‖ := by
  have hA := parseval_hasSum b (b.repr.symm (mulCoeff b μ C hC v))
  have hA' : HasSum (fun i => ‖μ i * ⟪b i, v⟫_ℂ‖ ^ 2)
      (‖b.repr.symm (mulCoeff b μ C hC v)‖ ^ 2) := by
    convert hA using 1
    funext i
    rw [inner_basis_symm]
    rfl
  have hB : HasSum (fun i => C ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2) (C ^ 2 * ‖v‖ ^ 2) :=
    (parseval_hasSum b v).mul_left _
  have hle : ‖b.repr.symm (mulCoeff b μ C hC v)‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
    refine hasSum_le (fun i => ?_) hA' hB
    show ‖μ i * ⟪b i, v⟫_ℂ‖ ^ 2 ≤ C ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC i) 2) (sq_nonneg _)
  exact le_of_sq_le_sq_nonneg (mul_nonneg hC0 (norm_nonneg v)) (by rw [mul_pow]; exact hle)

/-- **Diagonal operator.** A bounded family `μ` defines a bounded operator `T` acting diagonally in
the Hilbert basis `b`, with `⟪b i, T v⟫ = μ i ⟪b i, v⟫` and `‖T‖ ≤ C`. -/
theorem diag_exists (μ : ι → ℂ) (C : ℝ) (hC : ∀ i, ‖μ i‖ ≤ C) (hC0 : 0 ≤ C) :
    ∃ T : H →L[ℂ] H, (∀ i v, ⟪b i, T v⟫_ℂ = μ i * ⟪b i, v⟫_ℂ) ∧ ‖T‖ ≤ C := by
  refine ⟨LinearMap.mkContinuous (diagLinear b μ C hC) C
    (fun v => diagLinear_norm_le b μ C hC hC0 v), fun i v => ?_, ?_⟩
  · show ⟪b i, b.repr.symm (mulCoeff b μ C hC v)⟫_ℂ = μ i * ⟪b i, v⟫_ℂ
    rw [inner_basis_symm]
    rfl
  · exact ContinuousLinearMap.opNorm_le_bound _ hC0 (fun v => diagLinear_norm_le b μ C hC hC0 v)

/-- **Operator norm of a bounded diagonal operator is the supremum of the eigenvalue moduli.** -/
theorem diag_norm_eq [Nonempty ι] (μ : ι → ℂ) (hbdd : BddAbove (Set.range fun i => ‖μ i‖)) :
    ∃ T : H →L[ℂ] H, (∀ i v, ⟪b i, T v⟫_ℂ = μ i * ⟪b i, v⟫_ℂ) ∧ ‖T‖ = ⨆ i, ‖μ i‖ := by
  have hC : ∀ i, ‖μ i‖ ≤ ⨆ j, ‖μ j‖ := fun i => le_ciSup hbdd i
  have hS0 : 0 ≤ ⨆ j, ‖μ j‖ := le_trans (norm_nonneg _) (hC (Classical.arbitrary ι))
  obtain ⟨T, hT, hTn⟩ := diag_exists b μ (⨆ j, ‖μ j‖) hC hS0
  refine ⟨T, hT, le_antisymm hTn ?_⟩
  apply ciSup_le
  intro i
  have hbi : ‖b i‖ = 1 := b.orthonormal.1 i
  have hii : ⟪b i, b i⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hbi]
    norm_num
  have h1 : ⟪b i, T (b i)⟫_ℂ = μ i := by
    rw [hT, hii, mul_one]
  calc ‖μ i‖ = ‖⟪b i, T (b i)⟫_ℂ‖ := by rw [h1]
    _ ≤ ‖b i‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b i‖ * (‖T‖ * ‖b i‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ := by rw [hbi]; ring

/-- **Eigen-coefficients.** If `K (b k) = λ k • b k` for all `k`, then `⟪b k, K v⟫ = λ k ⟪b k, v⟫`. -/
theorem eig_coeff (K : H →L[ℂ] H) (lam : ι → ℂ) (hK : ∀ i, K (b i) = lam i • b i)
    (k : ι) (v : H) : ⟪b k, K v⟫_ℂ = lam k * ⟪b k, v⟫_ℂ := by
  classical
  have h1 : HasSum (fun i => K (b.repr v i • b i)) (K v) := (b.hasSum_repr v).mapL K
  have h2 : HasSum (fun i => ⟪b k, K (b.repr v i • b i)⟫_ℂ) ⟪b k, K v⟫_ℂ := by
    simpa only [innerSL_apply_apply] using h1.mapL (innerSL ℂ (b k))
  have h3 : HasSum (fun i => if i = k then lam k * ⟪b k, v⟫_ℂ else 0)
      (lam k * ⟪b k, v⟫_ℂ) := hasSum_ite_eq k _
  have horth : ∀ a c, ⟪b a, b c⟫_ℂ = if a = c then 1 else 0 :=
    fun a c => orthonormal_iff_ite.mp b.orthonormal a c
  have hfun : (fun i => ⟪b k, K (b.repr v i • b i)⟫_ℂ) =
      fun i => if i = k then lam k * ⟪b k, v⟫_ℂ else 0 := by
    funext i
    rw [map_smul, hK, inner_smul_right, inner_smul_right, b.repr_apply_apply, horth]
    by_cases h : i = k
    · subst h
      simp [mul_comm, mul_left_comm]
    · have h' : k ≠ i := fun e => h e.symm
      simp [h, h']
  rw [hfun] at h2
  exact h2.unique h3

end QuantumNLS.HilbertDiagOp
