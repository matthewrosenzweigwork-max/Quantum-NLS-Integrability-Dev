import LiebLiniger.FixedPeriod.Quantum.SymmetricTensorBridges
import LiebLiniger.FixedPeriod.Quantum.MixedTensorCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
All-family canonical slot permutation bridge. This file is separate from the
spatial/recursive constructions to avoid their import cycle with mixed kernels.
; only the root's delegated queue runs Lean/MCP.
-/

noncomputable section
open MeasureTheory
open scoped TensorProduct InnerProductSpace BigOperators

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Concatenate arbitrary elementary tensor factors in their source order. -/
def tensorFamilyAppend {p k : ℕ} (u : Fin p → Lp ℂ 2 μ) (v : Fin k → Lp ℂ 2 μ) :
    Fin (p + k) → Lp ℂ 2 μ :=
  fun i => Sum.elim u v (finSumFinEquiv.symm i)

/-- The all-family pointwise product identity under genuine coordinate concatenation. -/
theorem mixedTensorFunction_joinCoordinates (p k : ℕ)
    (u : Fin p → Lp ℂ 2 μ) (v : Fin k → Lp ℂ 2 μ)
    (z : (Fin p → X) × (Fin k → X)) :
    (∏ i : Fin (p + k), tensorFamilyAppend μ u v i (joinCoordinates p k z i)) =
      (∏ i : Fin p, u i (z.1 i)) * ∏ i : Fin k, v i (z.2 i) := by
  calc
    _ = ∏ i : Fin p ⊕ Fin k,
        tensorFamilyAppend μ u v (finSumFinEquiv i)
          (joinCoordinates p k z (finSumFinEquiv i)) :=
      (finSumFinEquiv.prod_comp (fun i =>
        tensorFamilyAppend μ u v i (joinCoordinates p k z i))).symm
    _ = _ := by
      simp only [tensorFamilyAppend, Equiv.symm_apply_apply, joinCoordinates_apply_sum,
        Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Mixed spatial tensors factor into independently chosen first and second
blocks, with all null-set representatives transported by measure preservation. -/
theorem regroupL2_mixedTensorL2 (p k : ℕ)
    (u : Fin p → Lp ℂ 2 μ) (v : Fin k → Lp ℂ 2 μ) :
    regroupL2 μ p k (mixedTensorL2 μ (tensorFamilyAppend μ u v)) =
      separatedL2 (Measure.pi fun _ : Fin p => μ) (Measure.pi fun _ : Fin k => μ)
        (mixedTensorL2 μ u) (mixedTensorL2 μ v) := by
  apply Lp.ext
  have hl := Lp.coeFn_compMeasurePreserving
    (mixedTensorL2 μ (tensorFamilyAppend μ u v)) (joinCoordinates_measurePreserving μ p k)
  have hr := (joinCoordinates_measurePreserving μ p k).quasiMeasurePreserving.ae_eq_comp
    (coeFn_mixedTensorL2 μ (tensorFamilyAppend μ u v))
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi fun _ : Fin p => μ) (ν := Measure.pi fun _ : Fin k => μ)).ae_eq_comp
    (coeFn_mixedTensorL2 μ u)
  have hk := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.pi fun _ : Fin p => μ) (ν := Measure.pi fun _ : Fin k => μ)).ae_eq_comp
    (coeFn_mixedTensorL2 μ v)
  have hs := separatedL2_coeFn (Measure.pi fun _ : Fin p => μ)
    (Measure.pi fun _ : Fin k => μ) (mixedTensorL2 μ u) (mixedTensorL2 μ v)
  filter_upwards [hl, hr, hp, hk, hs] with z hl hr hp hk hs
  calc
    _ = mixedTensorL2 μ (tensorFamilyAppend μ u v) (joinCoordinates p k z) := hl
    _ = ∏ i : Fin (p + k), tensorFamilyAppend μ u v i (joinCoordinates p k z i) := hr
    _ = (∏ i : Fin p, u i (z.1 i)) * ∏ i : Fin k, v i (z.2 i) :=
      mixedTensorFunction_joinCoordinates μ p k u v z
    _ = mixedTensorL2 μ u z.1 * mixedTensorL2 μ v z.2 :=
      congrArg₂ (· * ·) hp.symm hk.symm
    _ = _ := hs.symm

/-- The completed binary bridge preserves every elementary tensor family,
not only diagonal powers. -/
theorem completedProductTensorEquiv_mixedTensorL2 (p k : ℕ)
    (u : Fin p → Lp ℂ 2 μ) (v : Fin k → Lp ℂ 2 μ) :
    completedProductTensorEquiv μ p k
      ((mixedTensorL2 μ u ⊗ₜ[ℂ] mixedTensorL2 μ v :
          ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) :
        UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k))) =
      mixedTensorL2 μ (tensorFamilyAppend μ u v) := by
  rw [completedProductTensorEquiv_tmul]
  apply (regroupL2 μ p k).injective
  rw [regroupL2_unregroupL2, regroupL2_mixedTensorL2]

/-- Literal recursive elementary tensors, beginning with scalar one and then
head tensor tail in the source order. -/
def recursiveHilbertElementaryTensor : (n : ℕ) →
    (Fin n → Lp ℂ 2 μ) → SpatialHilbertTensorPower μ n
  | 0, _ => (1 : ℂ)
  | n + 1, v =>
      ((v 0 ⊗ₜ[ℂ] recursiveHilbertElementaryTensor n (fun i => v i.succ) :
          Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n) :
        UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n))

/-- Equality of particle counts transports an arbitrary mixed family by the
literal inverse Fin cast. -/
theorem productL2Cast_mixedTensorL2 {m n : ℕ} (h : m = n)
    (v : Fin m → Lp ℂ 2 μ) :
    productL2Cast μ h (mixedTensorL2 μ v) =
      mixedTensorL2 μ (fun i => v (Fin.cast h.symm i)) := by
  subst n
  rfl

/-- A casted head-tail concatenation is exactly the original family. -/
theorem tensorFamilyAppend_head_tail (n : ℕ) (v : Fin (n + 1) → Lp ℂ 2 μ) :
    (fun i : Fin (n + 1) => tensorFamilyAppend μ (fun _ : Fin 1 => v 0)
      (fun j : Fin n => v j.succ) (Fin.cast (Nat.add_comm 1 n).symm i)) = v := by
  funext i
  unfold tensorFamilyAppend
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : Fin.cast (Nat.add_comm 1 n).symm (0 : Fin (n + 1)) =
        Fin.castAdd n (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hz, finSumFinEquiv_symm_apply_castAdd]
    rfl
  · have hs : Fin.cast (Nat.add_comm 1 n).symm j.succ = Fin.natAdd 1 j := by
      apply Fin.ext
      change j.val + 1 = 1 + j.val
      exact Nat.add_comm _ _
    rw [hs, finSumFinEquiv_symm_apply_natAdd]
    rfl

/-- The all-family spatial realization fixes the actual canonical tensor ABI. -/
theorem spatialTensorPowerEquiv_elementaryTensor (n : ℕ) (v : Fin n → Lp ℂ 2 μ) :
    spatialTensorPowerEquiv μ n (recursiveHilbertElementaryTensor μ n v) = mixedTensorL2 μ v := by
  induction n with
  | zero =>
    have hv : v = fun _ : Fin 0 => (0 : Lp ℂ 2 μ) := by
      funext i
      exact Fin.elim0 i
    subst v
    rw [mixedTensorL2_diagonal, pureTensorL2_zero_eq_one]
    rfl
  | succ n ih =>
    change productL2Cast μ (Nat.add_comm 1 n)
      (completedProductTensorEquiv μ 1 n
        (completionIsometryEquiv
          (TensorProduct.congrIsometry (oneProductL2Equiv μ).symm
            (spatialTensorPowerEquiv μ n))
          ((v 0 ⊗ₜ[ℂ] recursiveHilbertElementaryTensor μ n (fun i => v i.succ) :
              Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n) :
            UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n)))) = _
    rw [completionIsometryEquiv_coe]
    change productL2Cast μ (Nat.add_comm 1 n)
      (completedProductTensorEquiv μ 1 n
        ((((oneProductL2Equiv μ).symm (v 0)) ⊗ₜ[ℂ]
            spatialTensorPowerEquiv μ n
              (recursiveHilbertElementaryTensor μ n (fun i => v i.succ)) :
              ProductL2 μ (Fin 1) ⊗[ℂ] ProductL2 μ (Fin n)) :
          UniformSpace.Completion (ProductL2 μ (Fin 1) ⊗[ℂ] ProductL2 μ (Fin n)))) = _
    rw [oneProductL2Equiv_symm_eq_pureTensorL2, ih]
    have hhead : pureTensorL2 (ι := Fin 1) μ (v 0) =
        mixedTensorL2 μ (fun _ : Fin 1 => v 0) :=
      (mixedTensorL2_diagonal (ι := Fin 1) μ (v 0)).symm
    rw [hhead, completedProductTensorEquiv_mixedTensorL2, productL2Cast_mixedTensorL2,
      tensorFamilyAppend_head_tail]

/-- Arbitrary elementary tensors are total, so their slot action determines a
continuous operator on the entire completed tensor power. -/
theorem recursiveHilbertElementaryTensor_total (n : ℕ) :
    (Submodule.span ℂ (Set.range (recursiveHilbertElementaryTensor μ n))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro ψ hψ
  have hp (v : Fin n → Lp ℂ 2 μ) :
      inner ℂ ψ (recursiveHilbertElementaryTensor μ n v) = 0 :=
    (Submodule.span ℂ (Set.range (recursiveHilbertElementaryTensor μ n))).inner_left_of_mem_orthogonal
      (Submodule.subset_span ⟨v, rfl⟩) hψ
  apply (spatialTensorPowerEquiv μ n).injective
  rw [map_zero]
  apply mixedTensorL2_eq_zero_of_inner μ
  intro v
  rw [← spatialTensorPowerEquiv_elementaryTensor μ n v,
    LinearIsometryEquiv.inner_map_map]
  exact hp v

/-- The transported unitary is the canonical slot permutation on every
actual elementary tensor family. The inverse order follows from pullback. -/
theorem hilbertTensorPermutation_elementaryTensor (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → Lp ℂ 2 μ) :
    hilbertTensorPermutation μ n σ (recursiveHilbertElementaryTensor μ n v) =
      recursiveHilbertElementaryTensor μ n (fun i => v (σ.symm i)) := by
  apply (spatialTensorPowerEquiv μ n).injective
  simp only [hilbertTensorPermutation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, spatialTensorPowerEquiv_elementaryTensor]
  exact permutationL2_mixedTensorL2 μ σ v

/-- Transported invariance is equivalent to genuine spatial symmetry. -/
theorem hilbertTensorPermutation_fixed_iff (n : ℕ) (ψ : SpatialHilbertTensorPower μ n) :
    (∀ σ : Equiv.Perm (Fin n), hilbertTensorPermutation μ n σ ψ = ψ) ↔
      spatialTensorPowerEquiv μ n ψ ∈ SymmetricSectorSpace μ n := by
  rw [mem_symmetricSectorSpace, symmetrizeL2_eq_self_iff]
  constructor
  · intro h σ
    have hs := congrArg (spatialTensorPowerEquiv μ n) (h σ)
    simp only [hilbertTensorPermutation, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply] at hs
    change permutationL2 μ σ (spatialTensorPowerEquiv μ n ψ) =
      spatialTensorPowerEquiv μ n ψ at hs
    exact hs
  · intro h σ
    apply (spatialTensorPowerEquiv μ n).injective
    simp only [hilbertTensorPermutation, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply]
    change permutationL2 μ σ (spatialTensorPowerEquiv μ n ψ) =
      spatialTensorPowerEquiv μ n ψ
    exact h σ

/-- The genuine canonical symmetric tensor subspace, transported through the
all-family realization rather than characterized only on diagonal vectors. -/
def CanonicalSymmetricTensorSpace (n : ℕ) : Submodule ℂ (SpatialHilbertTensorPower μ n) :=
  (SymmetricSectorSpace μ n).comap (spatialTensorPowerEquiv μ n).toLinearMap

theorem mem_canonicalSymmetricTensorSpace (n : ℕ) (ψ : SpatialHilbertTensorPower μ n) :
    ψ ∈ CanonicalSymmetricTensorSpace μ n ↔
      ∀ σ : Equiv.Perm (Fin n), hilbertTensorPermutation μ n σ ψ = ψ :=
  (hilbertTensorPermutation_fixed_iff μ n ψ).symm

/-- The full source symmetric Hilbert tensor sector is exactly the physical
symmetric L² sector used by FockSpace. -/
def canonicalSymmetricTensorSectorEquiv (n : ℕ) :
    CanonicalSymmetricTensorSpace μ n ≃ₗᵢ[ℂ] SymmetricSector μ n where
  toLinearEquiv :=
    { toFun := fun ψ => ⟨spatialTensorPowerEquiv μ n ψ, ψ.property⟩
      invFun := fun ψ => ⟨(spatialTensorPowerEquiv μ n).symm ψ, by
        change spatialTensorPowerEquiv μ n ((spatialTensorPowerEquiv μ n).symm ψ) ∈
          SymmetricSectorSpace μ n
        simpa only [LinearIsometryEquiv.apply_symm_apply] using ψ.property⟩
      map_add' := by
        intro ψ φ
        apply Subtype.ext
        exact (spatialTensorPowerEquiv μ n).map_add ψ φ
      map_smul' := by
        intro c ψ
        apply Subtype.ext
        exact (spatialTensorPowerEquiv μ n).map_smul c ψ
      left_inv := by
        intro ψ
        apply Subtype.ext
        exact (spatialTensorPowerEquiv μ n).symm_apply_apply ψ
      right_inv := by
        intro ψ
        apply Subtype.ext
        exact (spatialTensorPowerEquiv μ n).apply_symm_apply ψ }
  norm_map' := fun ψ => (spatialTensorPowerEquiv μ n).norm_map ψ

end LiebLiniger.FixedPeriod.Quantum

namespace LiebLiniger.FixedPeriod.Quantum

section PhysicalPeriod
variable (L : ℝ) [Fact (0 < L)]

/-- The source torus carries unnormalized physical length measure of mass L. -/
theorem physicalCircle_lengthMeasure_mass :
    (volume : Measure (AddCircle L)) Set.univ = ENNReal.ofReal L :=
  AddCircle.measure_univ L

/-- Canonical slot action specialized to the source period-L torus, with its
actual length measure and no endpoint-representative replacement. -/
theorem physicalTensorPermutation_elementaryTensor (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → Lp ℂ 2 (volume : Measure (AddCircle L))) :
    hilbertTensorPermutation (volume : Measure (AddCircle L)) n σ
      (recursiveHilbertElementaryTensor (volume : Measure (AddCircle L)) n v) =
      recursiveHilbertElementaryTensor (volume : Measure (AddCircle L)) n
        (fun i => v (σ.symm i)) :=
  hilbertTensorPermutation_elementaryTensor _ n σ v

/-- The actual physical tensor fixed space equals the symmetric L² sector. -/
theorem physicalTensorPermutation_fixed_iff (n : ℕ)
    (ψ : SpatialHilbertTensorPower (volume : Measure (AddCircle L)) n) :
    (∀ σ : Equiv.Perm (Fin n),
      hilbertTensorPermutation (volume : Measure (AddCircle L)) n σ ψ = ψ) ↔
      spatialTensorPowerEquiv (volume : Measure (AddCircle L)) n ψ ∈
        SymmetricSectorSpace (volume : Measure (AddCircle L)) n :=
  hilbertTensorPermutation_fixed_iff _ n ψ

/-- Q1's concrete physical permutation average is an orthogonal contraction. -/
theorem physicalTensorSymmetrize_contraction (n : ℕ) :
    (hilbertTensorSymmetrize (volume : Measure (AddCircle L)) n).toLinearMap.IsSymmetricProjection ∧
      ‖hilbertTensorSymmetrize (volume : Measure (AddCircle L)) n‖ ≤ 1 :=
  hilbertTensorSymmetrize_contraction _ n

end PhysicalPeriod
end LiebLiniger.FixedPeriod.Quantum
