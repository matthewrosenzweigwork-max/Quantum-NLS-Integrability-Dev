import Mathlib
import NlsGge.Atomic.G4.G4039Host
import NlsGge.Atomic.G4.G4039
import NlsGge.Atomic.G4.G4042
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.GK38.Defs

/- G4-044 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author; not accepted).
   Target NlsGge/Atomic/G4/G4044.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G4044` VERBATIM from design STATEMENTS/G4.md (G4-044 section; identical in followup1..10; no Pro round 4-12 entry restates it,
   BINDING_INDEX_FP80_06 lists G4-044 only under the Armstrong-scope note with no head).
   Route (G4044_ROUTE.md not needed: it is the packet skeleton).  No X-006 analyticity field, no Armstrong analytic anchor, no Armstrong import.
   (1) differentiability: landed G4-042 clause 1 (Hilbert-valued complex analyticity on sourceBetaW) gives DifferentiableAt.
   (2) the coordinate functional `evalCLM (true,n)` / `(false,n)` is a bounded linear map, so the n-th coordinate of `fderiv Omega phi h`
       is `fderiv (fun psi => Omega psi j) phi h` (chain rule through a CLM).
   (3) `Omega psi (true,n) = cartesianX n psi` (and false/Y) for psi in the open set sourceBetaW (G4-039), i.e. eventually equal near phi,
       so the fderivs agree. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open scoped ENNReal

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4044Aux

/-- The `j`-th coordinate of the derivative is the derivative of the `j`-th coordinate function (chain rule through the bounded
coordinate functional). -/
theorem coord_fderiv (φ : PotPair) (hd : DifferentiableAt ℂ birkhoffCartesian φ) (j : Bool × ℤ) (h : PotPair) :
    (fderiv ℂ birkhoffCartesian φ h) j = fderiv ℂ (fun ψ : PotPair => birkhoffCartesian ψ j) φ h := by
  have hev := ((lp.evalCLM ℂ (fun _ : Bool × ℤ => ℂ) 2 j).hasFDerivAt (x := birkhoffCartesian φ)).comp φ hd.hasFDerivAt
  have := congrArg (fun L => L h) hev.fderiv
  exact this.symm

/-- Near a point of `sourceBetaW` the `j`-th coordinate function equals the corresponding Cartesian coordinate function. -/
theorem coord_eventuallyEq (φ : PotPair) (hφ : φ ∈ sourceBetaW) (n : ℤ) :
    (fun ψ : PotPair => birkhoffCartesian ψ (true, n)) =ᶠ[𝓝 φ] cartesianX n ∧
    (fun ψ : PotPair => birkhoffCartesian ψ (false, n)) =ᶠ[𝓝 φ] cartesianY n := by
  have hnh : sourceBetaW ∈ 𝓝 φ := sourceFamily.V_open.mem_nhds hφ
  refine ⟨?_, ?_⟩
  · filter_upwards [hnh] with ψ hψ using (G4042Aux.coord_of_mem ψ hψ n).1
  · filter_upwards [hnh] with ψ hψ using (G4042Aux.coord_of_mem ψ hψ n).2

end G4044Aux

theorem G4044 (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
  DifferentiableAt ℂ birkhoffCartesian φ ∧
  ∀ (h : PotPair) (n : ℤ),
    (fderiv ℂ birkhoffCartesian φ h) (true, n) = fderiv ℂ (cartesianX n) φ h ∧
    (fderiv ℂ birkhoffCartesian φ h) (false, n) = fderiv ℂ (cartesianY n) φ h := by
  have hd : DifferentiableAt ℂ birkhoffCartesian φ := (G4042.1 φ hφ).differentiableAt
  refine ⟨hd, fun h n => ?_⟩
  obtain ⟨hX, hY⟩ := G4044Aux.coord_eventuallyEq φ hφ n
  refine ⟨?_, ?_⟩
  · rw [G4044Aux.coord_fderiv φ hd (true, n) h, hX.fderiv_eq]
  · rw [G4044Aux.coord_fderiv φ hd (false, n) h, hY.fderiv_eq]

end
end NlsGge.GKDefinitionDesign
