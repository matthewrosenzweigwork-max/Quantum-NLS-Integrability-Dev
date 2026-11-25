import Mathlib
import QuantumNLS.HaarTwistedModes

/-!
# R-F611926F (R3, tensor-ONB completeness): products of an orthonormal basis are complete in `L²(𝕋_L^N)`

Derived, not assumed (repository `physUnitary`/`prodLp`/`span_range_ptprod` + `forall_of_hilbertBasis`):
* `eq_zero_of_orth_prodLp`: a vector of `L²(𝕋_L^N)` orthogonal to every product vector `∏ f_j(x_j)` is zero
  (pull back by the unitary `physUnitary`, the algebraic tensor power is spanned by pure tensors and dense in the
  completion);
* `orth_prodLp_of_basis`: if `F ⊥ ∏ b_{k_j}(x_j)` for all index tuples `k` of a Hilbert basis `b`, then `F ⊥ ∏ f_j(x_j)`
  for all `f` (coordinatewise expansion, Finset induction with `forall_of_hilbertBasis`);
* `eq_zero_of_orth_basis_prod`: hence `F = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace QuantumNLS.HaarSlaterDensity

open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.TraceClass

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem norm_prodLp (f : Fin N → L2T L) : ‖prodLp f‖ = ∏ i, ‖f i‖ := by
  have h := inner_prodLp f f
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖prodLp f‖ ^ 2 = ∏ i, ‖f i‖ ^ 2 := by exact_mod_cast h
  rw [Finset.prod_pow] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)).1 h2

/-- A vector orthogonal to all product vectors vanishes. -/
theorem eq_zero_of_orth_prodLp {F : L2TN L N}
    (h : ∀ f : Fin N → L2T L, ⟪prodLp f, F⟫_ℂ = 0) : F = 0 := by
  set χ : HilbertTensorPower ℂ (L2T L) N := (physUnitary (L := L) (N := N)).symm F with hχ
  have hF : physUnitary χ = F := (physUnitary (L := L) (N := N)).apply_symm_apply F
  let K : Submodule ℂ (AlgTensorPower ℂ (L2T L) N) :=
    { carrier := {x | ⟪(x : HilbertTensorPower ℂ (L2T L) N), χ⟫_ℂ = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [UniformSpace.Completion.coe_add, inner_add_left, hx, hy, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [UniformSpace.Completion.coe_zero, inner_zero_left]
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [UniformSpace.Completion.coe_smul, inner_smul_left, hx, mul_zero] }
  have hspan : Submodule.span ℂ (Set.range (ptprod : (Fin N → L2T L) → AlgTensorPower ℂ (L2T L) N)) ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    show ⟪((ptprod f : AlgTensorPower ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N), χ⟫_ℂ = 0
    rw [← (physUnitary (L := L) (N := N)).inner_map_map, physUnitary_ptprod, hF]
    exact h f
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← span_range_ptprod (𝕜 := ℂ) (E := L2T L) N]; exact hspan
  have hall : ∀ x : AlgTensorPower ℂ (L2T L) N, ⟪(x : HilbertTensorPower ℂ (L2T L) N), χ⟫_ℂ = 0 := by
    intro x
    have : x ∈ K := by rw [hK]; trivial
    exact this
  have hclosed : IsClosed {y : HilbertTensorPower ℂ (L2T L) N | ⟪y, χ⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hy : ∀ y : HilbertTensorPower ℂ (L2T L) N, ⟪y, χ⟫_ℂ = 0 :=
    fun y => (UniformSpace.Completion.denseRange_coe).induction_on y hclosed hall
  have h0 : χ = 0 := inner_self_eq_zero.1 (hy χ)
  rw [← hF, h0, map_zero]

/-- Coordinatewise expansion: orthogonality to all `∏ b_{k_j}(x_j)` gives orthogonality to all products. -/
theorem orth_prodLp_of_basis {ι : Type*} (b : HilbertBasis ι ℂ (L2T L)) {F : L2TN L N}
    (hF : ∀ k : Fin N → ι, ⟪prodLp (fun i => b (k i)), F⟫_ℂ = 0) (f : Fin N → L2T L) :
    ⟪prodLp f, F⟫_ℂ = 0 := by
  classical
  have key : ∀ s : Finset (Fin N), ∀ f : Fin N → L2T L, (∀ i, i ∉ s → ∃ k, f i = b k) →
      ⟪prodLp f, F⟫_ℂ = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      choose k hk using fun i => hf i (Finset.notMem_empty i)
      have : f = fun i => b (k i) := funext hk
      subst this
      exact hF k
    | insert j s hj ih =>
      intro f hf
      let Tj : L2T L →ₗ[ℂ] L2TN L N := (prodMultilinear (L := L) (N := N)).toLinearMap f j
      have hT : ∀ x, Tj x = prodLp (Function.update f j x) := fun x => rfl
      have hbound : ∀ x, ‖Tj x‖ ≤ (∏ i ∈ Finset.univ.erase j, ‖f i‖) * ‖x‖ := by
        intro x
        rw [hT, norm_prodLp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
          Function.update_self]
        have : ∏ i ∈ Finset.univ.erase j, ‖Function.update f j x i‖ =
            ∏ i ∈ Finset.univ.erase j, ‖f i‖ :=
          Finset.prod_congr rfl fun i hi => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        rw [this, mul_comm]
      have hcont : Continuous Tj :=
        AddMonoidHomClass.continuous_of_bound Tj _ hbound
      have hP := forall_of_hilbertBasis b
        (P := fun x : L2T L => ⟪prodLp (Function.update f j x), F⟫_ℂ = 0)
        (isClosed_eq ((hcont.inner continuous_const)) continuous_const)
        (by
          have : prodLp (Function.update f j (0 : L2T L)) = 0 := by rw [← hT, map_zero]
          rw [this, inner_zero_left])
        (fun x y hx hy => by
          have : prodLp (Function.update f j (x + y)) =
              prodLp (Function.update f j x) + prodLp (Function.update f j y) := by
            rw [← hT, ← hT, ← hT, map_add]
          rw [this, inner_add_left, hx, hy, add_zero])
        (fun a x hx => by
          have : prodLp (Function.update f j (a • x)) = a • prodLp (Function.update f j x) := by
            rw [← hT, ← hT, map_smul]
          rw [this, inner_smul_left, hx, mul_zero])
        (fun i => by
          refine ih (Function.update f j (b i)) (fun i' hi' => ?_)
          by_cases h : i' = j
          · subst h; exact ⟨i, by simp⟩
          · have : i' ∉ insert j s := by
              simp only [Finset.mem_insert, not_or]; exact ⟨h, hi'⟩
            obtain ⟨k, hk⟩ := hf i' this
            exact ⟨k, by rw [Function.update_of_ne h]; exact hk⟩)
        (f j)
      simpa using hP
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

theorem eq_zero_of_orth_basis_prod {ι : Type*} (b : HilbertBasis ι ℂ (L2T L)) {F : L2TN L N}
    (hF : ∀ k : Fin N → ι, ⟪prodLp (fun i => b (k i)), F⟫_ℂ = 0) : F = 0 :=
  eq_zero_of_orth_prodLp (orth_prodLp_of_basis b hF)

#print axioms eq_zero_of_orth_basis_prod

end QuantumNLS.HaarSlaterDensity
