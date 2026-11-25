import Mathlib

/-!
# R-F9AB39A7 `QG:lem:haar-offgrid-bessel`: square sums of operators with a common diagonalization

(`QUANTUM_GAUGE_COMPONENTS.tex:641-663`, "the two sums agree because the individual kernels have a common normal
diagonalization; monotone convergence of their bounded diagonal sums proves the assertion about strong convergence".)
Generic complex Hilbert space `E` with a Hilbert basis `b`, a family `K_m` with `K_m b_k = λ_{m,k} b_k`.  Proved:

* `adjoint_diag`: `K_m^* b_k = conj λ_{m,k} b_k` (so the family is normal);
* `hasSum_norm_sq` / `hasSum_norm_sq_adjoint`: `‖K x‖² = ∑_k |λ_k|² |⟨b_k,x⟩|²` and the same for `K^*`;
* `bessel_diag`: if `∑_{m∈F} |λ_{m,k}|² ≤ B²` for all `k` then `∑_{m∈F} ‖K_m x‖² ≤ B²‖x‖²` and
  `∑_{m∈F} ‖K_m^* x‖² ≤ B²‖x‖²` (these are the two operator inequalities `∑ K*K ≤ B²`, `∑ KK* ≤ B²`);
* `strong_sum_diag`: for every finite `F` that bound holds ⇒ `m ↦ K_m^* K_m x` (and `K_m K_m^* x`) is unconditionally
  summable in `E`, the sum `T` is a bounded positive operator, `⟨x,Tx⟩ = ∑ ‖K_m x‖² ≤ B²‖x‖²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology

namespace QuantumNLS.DiagonalBessel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type*}

theorem hasSum_norm_sq (b : HilbertBasis ι ℂ E) (y : E) :
    HasSum (fun k => ‖⟪b k, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have e : ∀ k, ⟪y, b k⟫_ℂ * ⟪b k, y⟫_ℂ = ((‖⟪b k, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    have h1 : ⟪y, b k⟫_ℂ = conj ⟪b k, y⟫_ℂ := (inner_conj_symm y (b k)).symm
    rw [h1, Complex.conj_mul']
    push_cast; rfl
  simp only [e, inner_self_eq_norm_sq_to_K] at h
  exact (Complex.hasSum_ofReal.mp (by simpa using h))

theorem adjoint_diag (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (μ : ι → ℂ)
    (hT : ∀ k, T (b k) = μ k • b k) (k : ι) :
    ContinuousLinearMap.adjoint T (b k) = conj (μ k) • b k := by
  classical
  set v := ContinuousLinearMap.adjoint T (b k) - conj (μ k) • b k with hv
  have hinner : ∀ j, ⟪b j, v⟫_ℂ = 0 := by
    intro j
    have h1 : ⟪b j, ContinuousLinearMap.adjoint T (b k)⟫_ℂ = ⟪T (b j), b k⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right T (b j) (b k)
    rw [hv, inner_sub_right, h1, hT j, inner_smul_left, inner_smul_right]
    rw [sub_eq_zero]
    by_cases hjk : j = k
    · subst hjk; rfl
    · have : ⟪b j, b k⟫_ℂ = 0 := b.orthonormal.2 hjk
      simp [this]
  have hs := b.hasSum_repr v
  have h0 : ∀ j, b.repr v j • b j = 0 := fun j => by
    rw [HilbertBasis.repr_apply_apply, hinner j, zero_smul]
  simp only [h0] at hs
  have := hs.unique (hasSum_zero)
  exact sub_eq_zero.mp this

theorem hasSum_norm_sq_adjoint (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (μ : ι → ℂ)
    (hT : ∀ k, T (b k) = μ k • b k) (x : E) :
    HasSum (fun k => ‖μ k‖ ^ 2 * ‖⟪b k, x⟫_ℂ‖ ^ 2) (‖ContinuousLinearMap.adjoint T x‖ ^ 2) := by
  have h := hasSum_norm_sq b (ContinuousLinearMap.adjoint T x)
  have e : ∀ k, ⟪b k, ContinuousLinearMap.adjoint T x⟫_ℂ = conj (μ k) * ⟪b k, x⟫_ℂ := fun k => by
    rw [ContinuousLinearMap.adjoint_inner_right, hT k, inner_smul_left]
  simp only [e, norm_mul, RCLike.norm_conj, mul_pow] at h
  exact h

theorem hasSum_norm_sq_diag (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (μ : ι → ℂ)
    (hT : ∀ k, T (b k) = μ k • b k) (x : E) :
    HasSum (fun k => ‖μ k‖ ^ 2 * ‖⟪b k, x⟫_ℂ‖ ^ 2) (‖T x‖ ^ 2) := by
  have hT' : ∀ k, ContinuousLinearMap.adjoint T (b k) = conj (μ k) • b k := adjoint_diag b T μ hT
  have := hasSum_norm_sq_adjoint b (ContinuousLinearMap.adjoint T) (fun k => conj (μ k)) hT' x
  simpa [RCLike.norm_conj] using this

theorem bessel_diag {ι' : Type*} (b : HilbertBasis ι ℂ E) (F : Finset ι') (K : ι' → E →L[ℂ] E)
    (lam : ι' → ι → ℂ) (hK : ∀ m k, K m (b k) = lam m k • b k) {B : ℝ}
    (hB : ∀ k, ∑ m ∈ F, ‖lam m k‖ ^ 2 ≤ B ^ 2) (x : E) :
    (∑ m ∈ F, ‖K m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) ∧
      (∑ m ∈ F, ‖ContinuousLinearMap.adjoint (K m) x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) := by
  have hx := (hasSum_norm_sq b x).mul_left (B ^ 2)
  have key : ∀ (f : ι' → E) (hf : ∀ m, HasSum (fun k => ‖lam m k‖ ^ 2 * ‖⟪b k, x⟫_ℂ‖ ^ 2) (‖f m‖ ^ 2)),
      ∑ m ∈ F, ‖f m‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := by
    intro f hf
    have hs : HasSum (fun k => ∑ m ∈ F, ‖lam m k‖ ^ 2 * ‖⟪b k, x⟫_ℂ‖ ^ 2) (∑ m ∈ F, ‖f m‖ ^ 2) :=
      hasSum_sum (fun m _ => hf m)
    refine hasSum_le (fun k => ?_) hs hx
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hB k) (by positivity)
  exact ⟨key (fun m => K m x) (fun m => hasSum_norm_sq_diag b (K m) (lam m) (hK m) x),
    key (fun m => ContinuousLinearMap.adjoint (K m) x)
      (fun m => hasSum_norm_sq_adjoint b (K m) (lam m) (hK m) x)⟩

end QuantumNLS.DiagonalBessel
