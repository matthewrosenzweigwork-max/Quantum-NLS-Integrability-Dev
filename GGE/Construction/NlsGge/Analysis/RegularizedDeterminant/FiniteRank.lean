import NlsGge.Analysis.RegularizedDeterminant.FiniteDimensional
import NlsGge.Analysis.RegularizedDeterminant.FiniteSections

/-!
A genuine signed determinant on finite-rank real operators.  The canonical
finite-dimensional carrier is the actual range.  A rectangular determinant
identity proves independence of every finite-dimensional containing subspace.

This constructs the finite-rank input for the completion route; it does not
construct the infinite-dimensional extension or prove its HS continuity.
-/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis.RegularizedDeterminant

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A linear map into its actual range. -/
def mapToRange (B : E →ₗ[ℝ] E) : E →ₗ[ℝ] LinearMap.range B where
  toFun x := Subtype.mk (B x) (Exists.intro x rfl)
  map_add' x y := Subtype.ext (map_add B x y)
  map_smul' c x := Subtype.ext (map_smul B c x)

/-- Restriction to the range; this range is invariant without any additional assumption. -/
def rangeEnd (B : E →ₗ[ℝ] E) : LinearMap.range B →ₗ[ℝ] LinearMap.range B :=
  (mapToRange B).comp (LinearMap.range B).subtype

/-- Restriction to a containing subspace; containment of the range proves invariance. -/
def restrictedEnd (B : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hV : LinearMap.range B ≤ V) : V →ₗ[ℝ] V where
  toFun x := Subtype.mk (B x) (hV (Exists.intro x.val rfl))
  map_add' x y := Subtype.ext (map_add B x.val y.val)
  map_smul' c x := Subtype.ext (map_smul B c x.val)

/-- Canonical finite-rank value.  The finite-range proof is not a determinant hypothesis. -/
def finiteRankDet2 (B : E →ₗ[ℝ] E) (hB : FiniteDimensional ℝ (LinearMap.range B)) : ℝ := by
  letI := hB
  exact finiteDet2 (rangeEnd B)

/-- Independence of the chosen finite-dimensional invariant containing subspace. -/
theorem finiteRankDet2_eq_restriction (B : E →ₗ[ℝ] E)
    (hB : FiniteDimensional ℝ (LinearMap.range B))
    (V : Submodule ℝ E) [FiniteDimensional ℝ V] (hV : LinearMap.range B ≤ V) :
    finiteRankDet2 B hB = finiteDet2 (restrictedEnd B V hV) := by
  letI := hB
  let r : V →ₗ[ℝ] LinearMap.range B := (mapToRange B).comp V.subtype
  let j : LinearMap.range B →ₗ[ℝ] V :=
    { toFun := fun z => Subtype.mk z.val (hV z.property)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : r.comp j = rangeEnd B := by ext x; rfl
  have hj : j.comp r = restrictedEnd B V hV := by ext x; rfl
  change finiteDet2 (rangeEnd B) = _
  rw [← hr, finiteDet2_comp_comm j r, hj]

/-- Full real finite matrix formula, with no invertibility or orthogonality requirement. -/
theorem finiteRankDet2_eq_matrix (B : E →ₗ[ℝ] E)
    (hB : FiniteDimensional ℝ (LinearMap.range B))
    (V : Submodule ℝ E) [FiniteDimensional ℝ V] (hV : LinearMap.range B ≤ V)
    {I : Type*} [Fintype I] [DecidableEq I] (b : Module.Basis I ℝ V) :
    finiteRankDet2 B hB =
      Matrix.det (1 + LinearMap.toMatrix b b (restrictedEnd B V hV)) *
        Real.exp (-Matrix.trace (LinearMap.toMatrix b b (restrictedEnd B V hV))) := by
  rw [finiteRankDet2_eq_restriction B hB V hV, finiteDet2_eq_matrix b]
  rfl

theorem finiteRankDet2_zero (h0 : FiniteDimensional ℝ (LinearMap.range (0 : E →ₗ[ℝ] E))) :
    finiteRankDet2 (0 : E →ₗ[ℝ] E) h0 = 1 := by
  letI := h0
  have h : rangeEnd (0 : E →ₗ[ℝ] E) = 0 := by ext x; rfl
  change finiteDet2 (rangeEnd (0 : E →ₗ[ℝ] E)) = 1
  rw [h, finiteDet2_zero]

/-- Injectivity on the ambient space implies finite-rank nonvanishing. -/
theorem finiteRankDet2_ne_zero_of_injective (B : E →ₗ[ℝ] E)
    (hB : FiniteDimensional ℝ (LinearMap.range B))
    (hI : Function.Injective (1 + B : E →ₗ[ℝ] E)) : finiteRankDet2 B hB ≠ 0 := by
  letI := hB
  change finiteDet2 (rangeEnd B) ≠ 0
  apply finiteDet2_ne_zero_of_injective
  intro x y hxy
  apply Subtype.ext
  apply hI
  exact congrArg (fun z : LinearMap.range B => (z : E)) hxy

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- D5 on finite-rank bounded maps, using an actual bounded left inverse. -/
theorem finiteRankDet2_ne_zero_of_boundedInverse (B C : H →L[ℝ] H)
    (hB : HilbertSchmidt.HasFiniteRank B)
    (hC : C.comp (ContinuousLinearMap.id ℝ H + B) = ContinuousLinearMap.id ℝ H) :
    finiteRankDet2 B.toLinearMap hB ≠ 0 := by
  have hl : Function.LeftInverse C (1 + B.toLinearMap : H →ₗ[ℝ] H) := by
    intro x
    exact congrArg (fun T : H →L[ℝ] H => T x) hC
  exact finiteRankDet2_ne_zero_of_injective B.toLinearMap hB hl.injective

/-- The compression has the exact finite determinant/trace formula on the projecting subspace. -/
theorem compression_finiteRankDet2_formula (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    (T : HilbertSchmidt H H) :
    finiteRankDet2 (HilbertSchmidt.compression V T).toCLM.toLinearMap
      (HilbertSchmidt.compression_finiteRank V T) =
    finiteDet2 (restrictedEnd (HilbertSchmidt.compression V T).toCLM.toLinearMap V
      (by
        rintro z ⟨x, rfl⟩
        change (HilbertSchmidt.compression V T).toCLM x ∈ V
        rw [HilbertSchmidt.toCLM_compression]
        exact V.starProjection_apply_mem _)) := by
  apply finiteRankDet2_eq_restriction

end Hilbert
end NlsGge.Analysis.RegularizedDeterminant
