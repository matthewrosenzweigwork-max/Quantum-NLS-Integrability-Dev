import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.NormalizedTransfer

/-!
# R-198C12E2 basis:cor:transfer-normality (joint normality after completeness)

Source: `source/chapters/foundations/periodic_basis.tex:453-466`.

Literal statement: for every fixed particle number `N ≥ 1`, positive coupling `c > 0` and period `L > 0`,
the bounded transfer operators `S_{N,c}(z) = transfer L N c z` (`z ∈ ℂ`) commute with one another and with
one another's adjoints. The four pairings `(S z, S w)`, `(S z, S w^*)`, `(S z^*, S w)`, `(S z^*, S w^*)` are
all asserted; `z = w` gives normality `S z^* S z = S z S z^*`.

Realized inputs (read-only, accepted):
* `UnconditionalBetheBasis.meanField_physicalBasis`: the complete orthonormal Bethe basis at coupling `κ/N`;
* `UnconditionalBetheBasis.transfer_physicalBasis`: `normalizedTransfer L κ N z` is diagonal in that basis with
  eigenvalues `eigen κ z m`;
* `NormalizedTransfer.normalizedTransfer_eq_transfer`: `normalizedTransfer L κ N = transfer L N (κ/N)`.
The coupling is `κ = c N`, so `κ/N = c` and `transfer L N c = normalizedTransfer L (c N) N`.

Proof route (the source's): a bounded operator diagonal in a complete orthonormal basis has adjoint diagonal with
conjugate eigenvalues, and two operators diagonal in one complete basis commute. Equality of bounded operators
agreeing on a basis is derived from density of the span (`HilbertBasis.dense_span`).

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Filter Topology

namespace QuantumNLS.TransferNormality

section Diagonal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Two bounded operators agreeing on a Hilbert basis are equal (density of the span). -/
theorem ext_of_hilbertBasis (b : HilbertBasis ι ℂ E) {f g : E →L[ℂ] E}
    (h : ∀ i, f (b i) = g (b i)) : f = g := by
  have hspan : Submodule.span ℂ (Set.range b) ≤
      LinearMap.eqLocus (f : E →ₗ[ℂ] E) (g : E →ₗ[ℂ] E) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hEq : Set.EqOn f g (Submodule.span ℂ (Set.range b) : Set E) := fun x hx => hspan hx
  have hcl := hEq.closure f.continuous g.continuous
  ext x
  have hx : x ∈ closure ((Submodule.span ℂ (Set.range b) : Submodule ℂ E) : Set E) := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]
    simp
  exact hcl hx

/-- The adjoint of an operator diagonal in a Hilbert basis is diagonal with conjugate eigenvalues. -/
theorem adjoint_diag (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (a : ι → ℂ)
    (h : ∀ i, T (b i) = a i • b i) (i : ι) :
    ContinuousLinearMap.adjoint T (b i) = conj (a i) • b i := by
  apply b.repr.injective
  ext j
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right, h, inner_smul_left, inner_smul_right]
  by_cases hj : j = i
  · subst j
    rfl
  · rw [b.orthonormal.inner_eq_zero hj, mul_zero, mul_zero]

/-- Two operators diagonal in the same Hilbert basis commute. -/
theorem commute_of_diag (b : HilbertBasis ι ℂ E) (T₁ T₂ : E →L[ℂ] E) (a c : ι → ℂ)
    (h₁ : ∀ i, T₁ (b i) = a i • b i) (h₂ : ∀ i, T₂ (b i) = c i • b i) :
    Commute T₁ T₂ := by
  show T₁ * T₂ = T₂ * T₁
  apply ext_of_hilbertBasis b
  intro i
  simp only [ContinuousLinearMap.mul_apply, h₁ i, h₂ i, map_smul, smul_smul]
  rw [mul_comm]

/-- Diagonal family in one complete basis: all four pairings of `{S z, S z^*}` commute. -/
theorem main_of_diag {ι' : Type*} (b : HilbertBasis ι' ℂ E) (S : ℂ → (E →L[ℂ] E))
    (ev : ℂ → ι' → ℂ) (h : ∀ x i, S x (b i) = ev x i • b i) (z w : ℂ) :
    Commute (S z) (S w) ∧
      Commute (S z) (ContinuousLinearMap.adjoint (S w)) ∧
      Commute (ContinuousLinearMap.adjoint (S z)) (S w) ∧
      Commute (ContinuousLinearMap.adjoint (S z)) (ContinuousLinearMap.adjoint (S w)) := by
  have hA : ∀ x i, ContinuousLinearMap.adjoint (S x) (b i) = conj (ev x i) • b i :=
    fun x i => adjoint_diag b (S x) (ev x) (h x) i
  exact ⟨commute_of_diag b _ _ _ _ (h z) (h w), commute_of_diag b _ _ _ _ (h z) (hA w),
    commute_of_diag b _ _ _ _ (hA z) (h w), commute_of_diag b _ _ _ _ (hA z) (hA w)⟩

end Diagonal

section Transfer

set_option maxHeartbeats 4000000 in
/-- **R-198C12E2 (`basis:cor:transfer-normality`).** For every `N ≥ 1`, `c > 0` and period `L > 0`, the bounded
transfer operators `S_{N,c}(z) = transfer L N c z` (`z ∈ ℂ`) commute with one another and with one another's
adjoints; in particular each is normal. -/
theorem transfer_normality (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    ∀ z w : ℂ,
      Commute (QuantumNLS.BethePhysicalTransfer.transfer L N c z)
        (QuantumNLS.BethePhysicalTransfer.transfer L N c w) ∧
      Commute (QuantumNLS.BethePhysicalTransfer.transfer L N c z)
        (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c w)) ∧
      Commute (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c z))
        (QuantumNLS.BethePhysicalTransfer.transfer L N c w) ∧
      Commute (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c z))
        (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c w)) := by
  intro z w
  have hN0 : 0 < N := by omega
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = c * (N : ℝ) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact mul_pos hc (by exact_mod_cast hN0)
  have hdiv : κ / (N : ℝ) = c := by
    rw [hκdef, mul_div_assoc, div_self hNr, mul_one]
  have hT : ∀ x : ℂ, QuantumNLS.BethePhysicalTransfer.transfer L N c x =
      QuantumNLS.NormalizedTransfer.normalizedTransfer L κ N x := by
    intro x
    rw [QuantumNLS.NormalizedTransfer.normalizedTransfer_eq_transfer, hdiv]
  obtain ⟨h1, h2, h3, h4⟩ := main_of_diag
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN0 hκ)
    (fun x => QuantumNLS.NormalizedTransfer.normalizedTransfer L κ N x)
    (fun x m => QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN0 m x)
    (fun x m => QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis (L := L) hκ hN0 x m) z w
  simp only [hT]
  exact ⟨h1, h2, h3, h4⟩

end Transfer

end QuantumNLS.TransferNormality

#print axioms QuantumNLS.TransferNormality.transfer_normality
