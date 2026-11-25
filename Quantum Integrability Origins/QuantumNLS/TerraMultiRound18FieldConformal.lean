import QuantumNLS.TerraMultiRound17D01Repair

/-! Infinitesimal conformal symplectic identity of the D01 field. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
namespace QuantumNLS.TerraMultiRound18FieldConformal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem omega_fderiv_Y (S : Hyp H) (u h k : H) :
    omega (fderiv ℝ S.Y u h) k = fderiv ℝ S.abar u h k := by
  obtain ⟨J, hJ, -⟩ := QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := H)
  let B : H →L[ℝ] (H →L[ℝ] ℝ) := J.toContinuousLinearMap
  have hY := (QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 u
  have hA := analyticAt_of_isRealAnalyticPoly (S.abar_analytic u)
  have he : (fun x => B (S.Y x) k) = (fun x => S.abar x k) := by
    funext x
    change J (S.Y x) k = S.abar x k
    rw [hJ]
    change omega (S.Y x) k = S.abar x k
    rw [Hyp.Y, omega_Winv]
  have hleft := ((B.flip k).hasFDerivAt.comp u hY.differentiableAt.hasFDerivAt)
  change HasFDerivAt (fun x => B (S.Y x) k) ((B.flip k).comp (fderiv ℝ S.Y u)) u at hleft
  have hright := hA.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const (c := k) u)
  have hh := (he ▸ hleft).unique hright
  have hh' := congrArg (fun L : H →L[ℝ] ℝ => L h) hh
  simpa [B, hJ, omega] using hh'

theorem infinitesimal_conformal (S : Hyp H) (u h k : H) :
    omega (fderiv ℝ S.Y u h) k + omega h (fderiv ℝ S.Y u k) = omega h k := by
  rw [omega_swap h, omega_fderiv_Y, omega_fderiv_Y]
  exact S.abar_d u h k

#print axioms omega_fderiv_Y
#print axioms infinitesimal_conformal
end QuantumNLS.TerraMultiRound18FieldConformal
