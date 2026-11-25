import NlsGge.Schur.FreeDomainPointwise
import NlsGge.Schur.PhysicalSector
import NlsGge.Spectral.ActualFreeWeightedDomainReflBasisEvaluationPrerequisiteV2

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private theorem lpSingle_mem_freeWeightedDomainPointwise
    (n : ℤ) (i : Bool × Sector n) :
    lp.single (E := fun _ : Bool × Sector n => ℂ) 2 i (1 : ℂ) ∈ freeWeightedDomainPointwise n := by
  change Memℓp (freeWeightedCoordinates n (lp.single (E := fun _ : Bool × Sector n => ℂ) 2 i (1 : ℂ))) 2
  have hcoordinates :
      freeWeightedCoordinates n (lp.single (E := fun _ : Bool × Sector n => ℂ) 2 i (1 : ℂ)) =
        (spectralCenter i.2.val) • lp.single (E := fun _ : Bool × Sector n => ℂ) 2 i (1 : ℂ) := by
    funext j
    by_cases hji : j = i <;>
      simp [freeWeightedCoordinates, lp.single_apply, hji]
  rw [hcoordinates]
  exact (lp.memℓp (lp.single (E := fun _ : Bool × Sector n => ℂ) 2 i (1 : ℂ))).const_smul
    (spectralCenter i.2.val)

/-- The actual weighted free-coordinate domain is dense in the full
square-summable sector space. Its finite coordinate vectors already lie in
the weighted domain. -/
theorem freeWeightedDomainPointwise_dense (n : ℤ) :
    Dense (freeWeightedDomainPointwise n : Set (SectorSquare n)) := by
  let b : HilbertBasis (Bool × Sector n) ℂ (SectorSquare n) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (SectorSquare n))
  have hb (i : Bool × Sector n) :
      b i = lp.single (E := fun _ : Bool × Sector n => ℂ) 2 i (1 : ℂ) := by
    rw [← b.repr_symm_single i]
    exact sectorLinearIsometryRefl_symm_apply n _
  have hspan : Submodule.span ℂ (Set.range b) ≤ freeWeightedDomainPointwise n := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hb]
    exact lpSingle_mem_freeWeightedDomainPointwise n i
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply le_antisymm le_top
  calc
    ⊤ = (Submodule.span ℂ (Set.range b)).topologicalClosure := by
      rw [b.dense_span]
    _ ≤ (freeWeightedDomainPointwise n).topologicalClosure :=
      Submodule.topologicalClosure_mono hspan

end NlsGge.Schur

end
