import NlsGge.Analysis.ComplexHilbertSchmidtFiniteBasis

/-! NEW-F02.06 physical-source bridge: a complex unitary change of domain and
codomain preserves HS energy, membership and norm. This applies to the actual
parity/interval isometries and introduces no artificial period or sqrt-two scale. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators
namespace NlsGge.Pilot
variable {E F G H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def transportComplexOperator (T : E →L[ℂ] F)
    (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] H) : G →L[ℂ] H :=
  f.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp e.symm.toLinearIsometry.toContinuousLinearMap)

theorem complexHilbertSchmidtEnergy_unitaryTransport
    (T : E →L[ℂ] F) (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] H) :
    complexHilbertSchmidtEnergy (transportComplexOperator T e f) =
      complexHilbertSchmidtEnergy T := by
  classical
  let bE := chosenComplexHilbertBasis (E := E)
  let bG : HilbertBasis (chosenComplexHilbertBasisIndex (E := E)) ℂ G :=
    ⟨e.symm.trans bE.repr⟩
  have hb (i : chosenComplexHilbertBasisIndex (E := E)) : bG i = e (bE i) := by
    rw [← bG.repr_symm_single i, ← bE.repr_symm_single i]
    change (e.symm.trans bE.repr).symm (lp.single 2 i (1 : ℂ)) =
      e (bE.repr.symm (lp.single 2 i (1 : ℂ)))
    rfl
  rw [complexHilbertSchmidtEnergy_eq_basis _ bG,
    complexHilbertSchmidtEnergy_eq_basis T bE]
  apply tsum_congr
  intro i
  rw [hb]
  simp [transportComplexOperator]

theorem isComplexHilbertSchmidt_unitaryTransport_iff
    (T : E →L[ℂ] F) (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] H) :
    IsComplexHilbertSchmidt (transportComplexOperator T e f) ↔
      IsComplexHilbertSchmidt T := by
  unfold IsComplexHilbertSchmidt
  rw [complexHilbertSchmidtEnergy_unitaryTransport]

theorem complexHilbertSchmidtNorm_unitaryTransport
    (T : E →L[ℂ] F) (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] H) :
    complexHilbertSchmidtNorm (transportComplexOperator T e f) =
      complexHilbertSchmidtNorm T := by
  unfold complexHilbertSchmidtNorm
  rw [complexHilbertSchmidtEnergy_unitaryTransport]
end NlsGge.Pilot
