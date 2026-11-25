import Mathlib
import QuantumNLS.DiagonalBessel

/-!
# R-F9AB39A7: the sums `∑ K_m^* K_m` and `∑ K_m K_m^*` are strong monotone sums

(`QUANTUM_GAUGE_COMPONENTS.tex:657-663`: "Monotone convergence of their bounded diagonal sums proves the assertion about strong
convergence".)  Generic `E`, Hilbert basis `b`, `K_m b_k = λ_{m,k} b_k` with `∑_{m∈F}|λ_{m,k}|² ≤ B²` for every finite `F`.
`strong_sum_diag`: there is a bounded positive `T` with `∑_m K_m^* K_m x = T x` (unconditionally summable in `E` for every
`x`), `⟨x, T x⟩ = ∑_m ‖K_m x‖² ≤ B² ‖x‖²`; the partial sums over finite sets increase to `T`.
`strong_sum_diag'`: the same for `K_m K_m^*`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology QuantumNLS.DiagonalBessel

namespace QuantumNLS.DiagonalBesselStrong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type*}
  {ι' : Type*}

theorem strong_sum_diag (b : HilbertBasis ι ℂ E) (K : ι' → E →L[ℂ] E) (lam : ι' → ι → ℂ)
    (hK : ∀ m k, K m (b k) = lam m k • b k) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (F : Finset ι') (k : ι), ∑ m ∈ F, ‖lam m k‖ ^ 2 ≤ B ^ 2) :
    ∃ T : E →L[ℂ] E,
      (∀ x, HasSum (fun m => (ContinuousLinearMap.adjoint (K m) ∘L K m) x) (T x)) ∧
      (∀ x, ⟪x, T x⟫_ℂ = ((∑' m, ‖K m x‖ ^ 2 : ℝ) : ℂ)) ∧
      (∀ x, Summable (fun m => ‖K m x‖ ^ 2) ∧ ∑' m, ‖K m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) ∧
      T.IsPositive := by
  classical
  have hbes := fun (F : Finset ι') x => bessel_diag b F K lam hK (hB F) x
  have hsumm : ∀ x, Summable (fun m => ‖K m x‖ ^ 2) := fun x =>
    summable_of_sum_le (fun m => by positivity) (fun F => (hbes F x).1)
  have htsum : ∀ x, ∑' m, ‖K m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := fun x =>
    (hsumm x).tsum_le_of_sum_le (fun F => (hbes F x).1)
  -- diagonal action of the finite sums
  have hC : ∀ m k, (ContinuousLinearMap.adjoint (K m) ∘L K m) (b k) = ((‖lam m k‖ ^ 2 : ℝ) : ℂ) • b k := by
    intro m k
    simp only [ContinuousLinearMap.comp_apply, hK m k, map_smul, adjoint_diag b (K m) (lam m) (hK m) k,
      smul_smul]
    congr 1
    rw [mul_comm, Complex.conj_mul']
    norm_cast
  have hS : ∀ (F : Finset ι') k, (∑ m ∈ F, ContinuousLinearMap.adjoint (K m) ∘L K m) (b k) =
      ((∑ m ∈ F, ‖lam m k‖ ^ 2 : ℝ) : ℂ) • b k := by
    intro F k
    rw [ContinuousLinearMap.sum_apply]
    simp only [hC, ← Finset.sum_smul]
    push_cast
    rfl
  have hSnorm : ∀ (F : Finset ι') x, ‖(∑ m ∈ F, ContinuousLinearMap.adjoint (K m) ∘L K m) x‖ ^ 2 ≤
      B ^ 2 * ∑ m ∈ F, ‖K m x‖ ^ 2 := by
    intro F x
    have h1 := hasSum_norm_sq_diag b (∑ m ∈ F, ContinuousLinearMap.adjoint (K m) ∘L K m)
      (fun k => ((∑ m ∈ F, ‖lam m k‖ ^ 2 : ℝ) : ℂ)) (hS F) x
    have h2 : HasSum (fun k => ∑ m ∈ F, ‖lam m k‖ ^ 2 * ‖⟪b k, x⟫_ℂ‖ ^ 2) (∑ m ∈ F, ‖K m x‖ ^ 2) :=
      hasSum_sum (fun m _ => hasSum_norm_sq_diag b (K m) (lam m) (hK m) x)
    have h3 := h2.mul_left (B ^ 2)
    refine hasSum_le (fun k => ?_) h1 h3
    have hs0 : 0 ≤ ∑ m ∈ F, ‖lam m k‖ ^ 2 := Finset.sum_nonneg (fun m _ => sq_nonneg _)
    have hsB := hB F k
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hs0, ← Finset.sum_mul]
    have hsq : (∑ m ∈ F, ‖lam m k‖ ^ 2) ^ 2 ≤ B ^ 2 * ∑ m ∈ F, ‖lam m k‖ ^ 2 := by nlinarith
    calc (∑ m ∈ F, ‖lam m k‖ ^ 2) ^ 2 * ‖⟪b k, x⟫_ℂ‖ ^ 2
        ≤ (B ^ 2 * ∑ m ∈ F, ‖lam m k‖ ^ 2) * ‖⟪b k, x⟫_ℂ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = B ^ 2 * ((∑ m ∈ F, ‖lam m k‖ ^ 2) * ‖⟪b k, x⟫_ℂ‖ ^ 2) := by ring
  -- summability in E
  have hsumE : ∀ x, Summable (fun m => (ContinuousLinearMap.adjoint (K m) ∘L K m) x) := by
    intro x
    rw [summable_iff_vanishing_norm]
    intro ε hε
    have hδ : 0 < ε ^ 2 / (B ^ 2 + 1) := by positivity
    obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp (hsumm x)) (ε ^ 2 / (B ^ 2 + 1)) hδ
    refine ⟨s, fun t ht => ?_⟩
    have h1 := hs t ht
    have h2 := hSnorm t x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun m _ => sq_nonneg ‖K m x‖))] at h1
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply] at h2 ⊢
    have h3 : ‖∑ m ∈ t, (ContinuousLinearMap.adjoint (K m)) (K m x)‖ ^ 2 < ε ^ 2 := by
      calc _ ≤ B ^ 2 * ∑ m ∈ t, ‖K m x‖ ^ 2 := h2
        _ ≤ B ^ 2 * (ε ^ 2 / (B ^ 2 + 1)) := mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ < ε ^ 2 := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [sq_nonneg ε, mul_pos hε hε]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  -- the sum operator
  let Tlin : E →ₗ[ℂ] E :=
    { toFun := fun x => ∑' m, (ContinuousLinearMap.adjoint (K m) ∘L K m) x
      map_add' := fun x y => by
        simp only [map_add]
        exact (hsumE x).tsum_add (hsumE y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        exact tsum_const_smul'' c }
  have hTbound : ∀ x, ‖Tlin x‖ ≤ B ^ 2 * ‖x‖ := by
    intro x
    have hlim := (hsumE x).hasSum
    refine le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) (fun F => ?_)
    have h2 := hSnorm F x
    simp only [ContinuousLinearMap.sum_apply] at h2
    have h3 : B ^ 2 * ∑ m ∈ F, ‖K m x‖ ^ 2 ≤ (B ^ 2 * ‖x‖) ^ 2 := by
      have := (hbes F x).1
      nlinarith [sq_nonneg B, sq_nonneg ‖x‖, this]
    have : ‖∑ m ∈ F, (ContinuousLinearMap.adjoint (K m) ∘L K m) x‖ ^ 2 ≤ (B ^ 2 * ‖x‖) ^ 2 := by
      simp only [ContinuousLinearMap.comp_apply] at h2 ⊢
      exact h2.trans h3
    exact abs_le_of_sq_le_sq' this (by positivity) |>.2 |> fun h => by simpa using h
  let T : E →L[ℂ] E := LinearMap.mkContinuous Tlin (B ^ 2) hTbound
  have hT : ∀ x, T x = ∑' m, (ContinuousLinearMap.adjoint (K m) ∘L K m) x := fun x => rfl
  have hhas : ∀ x, HasSum (fun m => (ContinuousLinearMap.adjoint (K m) ∘L K m) x) (T x) := fun x => by
    rw [hT]; exact (hsumE x).hasSum
  have hinner : ∀ x, ⟪x, T x⟫_ℂ = ((∑' m, ‖K m x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have h1 := (hhas x).mapL (innerSL ℂ x)
    have h2 : HasSum (fun m => ⟪x, (ContinuousLinearMap.adjoint (K m) ∘L K m) x⟫_ℂ)
        ((∑' m, ‖K m x‖ ^ 2 : ℝ) : ℂ) := by
      have h3 := Complex.hasSum_ofReal.mpr (hsumm x).hasSum
      convert h3 using 1
      funext m
      simp only [ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      norm_cast
    exact h1.unique h2
  refine ⟨T, hhas, hinner, fun x => ⟨hsumm x, htsum x⟩, ?_⟩
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have h := hinner x
  have h' : ⟪T x, x⟫_ℂ = ((∑' m, ‖K m x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, h, Complex.conj_ofReal]
  rw [h']
  exact ⟨by simp, by simpa using tsum_nonneg (fun m => by positivity)⟩

/-- The same for `K_m K_m^*`. -/
theorem strong_sum_diag' (b : HilbertBasis ι ℂ E) (K : ι' → E →L[ℂ] E) (lam : ι' → ι → ℂ)
    (hK : ∀ m k, K m (b k) = lam m k • b k) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (F : Finset ι') (k : ι), ∑ m ∈ F, ‖lam m k‖ ^ 2 ≤ B ^ 2) :
    ∃ T : E →L[ℂ] E,
      (∀ x, HasSum (fun m => (K m ∘L ContinuousLinearMap.adjoint (K m)) x) (T x)) ∧
      (∀ x, ⟪x, T x⟫_ℂ = ((∑' m, ‖ContinuousLinearMap.adjoint (K m) x‖ ^ 2 : ℝ) : ℂ)) ∧
      (∀ x, Summable (fun m => ‖ContinuousLinearMap.adjoint (K m) x‖ ^ 2) ∧
        ∑' m, ‖ContinuousLinearMap.adjoint (K m) x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) ∧
      T.IsPositive := by
  have hK' : ∀ m k, ContinuousLinearMap.adjoint (K m) (b k) = conj (lam m k) • b k :=
    fun m k => adjoint_diag b (K m) (lam m) (hK m) k
  have := strong_sum_diag b (fun m => ContinuousLinearMap.adjoint (K m)) (fun m k => conj (lam m k)) hK' hB0
    (fun F k => by simpa [RCLike.norm_conj] using hB F k)
  simpa [ContinuousLinearMap.adjoint_adjoint] using this

end QuantumNLS.DiagonalBesselStrong
