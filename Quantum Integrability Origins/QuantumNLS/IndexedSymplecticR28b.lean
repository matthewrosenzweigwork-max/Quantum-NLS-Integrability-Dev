import QuantumNLS.IndexedRegularityR28b
import QuantumNLS.RB01Main
import QuantumNLS.RootMassPropernessR27
import QuantumNLS.RootMassInvolutionBatchR9
import QuantumNLS.ProductTorusSymplectic

/-! LOCAL-016: discharge the hypotheses of the full variational symplectic theorem.
B01 (R-EC25334D) is accepted and supplies collective analyticity; properness
and involution are the accepted R-0191D778 and R-507DD869. No torus period or
coordinate construction is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
namespace QuantumNLS.IndexedSymplecticR28b
open PhysicalTensor (L2T)
open TerraMultiRound30HessianBridge (Actions)
open ProductTorusGenerator ProductTorusFlow ProductTorusCommute
open RootMassInvolutionR8 (mass)
variable {L κ : ℝ} [Fact (0 < L)]
abbrev realNS : NormedSpace ℝ (L2T L) := by
  letI : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
  exact NormedSpace.complexToReal

theorem realNS_eq : realNS (L := L) = (inferInstance : NormedSpace ℝ (L2T L)) := by
  let : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
  exact NormedSpace.restrictScalars_eq ℝ ℂ

theorem realNS_eq_lp : realNS (L := L) =
    (MeasureTheory.Lp.instNormedSpace : NormedSpace ℝ (L2T L)) := by
  let : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
  exact NormedSpace.restrictScalars_eq (h :=
    (MeasureTheory.Lp.instNormedSpace : NormedSpace ℝ (L2T L))) ℝ ℂ

theorem complex_module_eq_lp :
    (InnerProductSpace.complexToReal (G := L2T L)).toModule =
      (MeasureTheory.Lp.instModule : Module ℝ (L2T L)) :=
  congrArg (fun A : NormedSpace ℝ (L2T L) => A.toModule) (realNS_eq_lp (L := L))

theorem complex_normed_eq_lp :
    (InnerProductSpace.complexToReal (G := L2T L)).toNormedSpace =
      (MeasureTheory.Lp.instNormedSpace : NormedSpace ℝ (L2T L)) := realNS_eq_lp

local instance realNormed : NormedSpace ℝ (L2T L) := realNS
local instance realModule : Module ℝ (L2T L) := (realNS (L := L)).toModule
local instance realSMul : SMul ℝ (L2T L) := (realNS (L := L)).toSMul
local instance additiveGroup : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

theorem analytic_actions (hκ : 0 < κ) : AnalyticOnNhd ℝ (Actions (L := L) hκ) univ :=
  fun u _ => by
    simpa +instances only [realNormed, realNS_eq] using RB01Main.analyticAt_actions hκ u

theorem coordinate_derivative (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    (coord n).comp (fderiv ℝ (Actions (L := L) hκ) u) = fderiv ℝ (mass (L := L) hκ n) u :=
  ((coord n).hasFDerivAt.comp u
    ((analytic_actions hκ u (mem_univ u)).differentiableAt.hasFDerivAt)).fderiv.symm

theorem Winv_hamField (F : L2T L → ℝ) (u : L2T L) :
    Winv (fderiv ℝ F u) = SymplecticBracket.hamField F u := by
  unfold Winv SymplecticBracket.hamField SymplecticBracket.gradient
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  ring

theorem coordinate_field (hκ : 0 < κ) (n : ℤ) :
    X (fderiv ℝ (Actions (L := L) hκ)) (e n) = SymplecticBracket.hamField (mass (L := L) hκ n) := by
  rw [X_e]
  funext u
  rw [Xn, coordinate_derivative hκ _ _, Winv_hamField]

theorem physical_hyp (hκ : 0 < κ) : Hyp (Actions (L := L) hκ) (fderiv ℝ (Actions (L := L) hκ)) where
  hasFDerivAt u := (analytic_actions hκ u (mem_univ u)).differentiableAt.hasFDerivAt
  contDiff := (analytic_actions hκ).fderiv.contDiff
  involutive := by
    intro u n j
    have hd := coordinate_derivative hκ n u
    have hj : Xn (fderiv ℝ (Actions (L := L) hκ)) j u = SymplecticBracket.hamField (mass (L := L) hκ j) u := by
      rw [Xn, coordinate_derivative hκ _ _, Winv_hamField]
    change ((coord n).comp (fderiv ℝ (Actions (L := L) hκ) u)) (Xn _ j u) = 0
    rw [hd, hj]
    exact (RootMassInvolutionR9.root_mass_involution hκ).2 n j u
  fibre_compact u := by
    have he : (Actions (L := L) hκ) ⁻¹' {Actions (L := L) hκ u} =
        (RootIndexedMasses.masses (L := L) hκ) ⁻¹' {RootIndexedMasses.masses (L := L) hκ u} := by
      ext v
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [he]
    exact (RootMassPropernessR27.root_mass_properness hκ).2.2.2.1 _

/-- Identification by ODE uniqueness, without a period assumption. -/
theorem flow_eq_collective (hκ : 0 < κ) (n : ℤ) (t : ℝ) :
    IndexedGlobalR27b.flow (L := L) hκ n t =
      ProductTorusFlow.flow (fderiv ℝ (Actions hκ)) (e n) t := by
  funext u
  have he := IndexedGlobalR27b.solution_unique hκ n u
    (γ := fun s => ProductTorusFlow.flow (fderiv ℝ (Actions hκ)) (e n) s u)
    (flow_zero (physical_hyp hκ) (e n) u)
    (fun s => by
      have hh := (hasDerivAt_flow (physical_hyp hκ) (e n) u s).isLittleO
      let : AddCommGroup (L2T L) := MeasureTheory.Lp.instAddCommGroup
      let : Module ℝ (L2T L) := MeasureTheory.Lp.instModule
      let : NormedSpace ℝ (L2T L) := MeasureTheory.Lp.instNormedSpace
      apply HasDerivAt.of_isLittleO
      simpa +instances only [coordinate_field hκ n,IndexedFieldR27b.field,
        complex_module_eq_lp,complex_normed_eq_lp] using hh)
  exact (congrFun he t).symm

/-- Preservation of the physical form by the full Frechet differential.
The imported variational theorem uses the full bounded Hessian. -/
theorem symplectic_flow (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u a b : L2T L) :
    SymplecticBracket.omega
      (fderiv ℝ (IndexedGlobalR27b.flow hκ n t) u a)
      (fderiv ℝ (IndexedGlobalR27b.flow hκ n t) u b) =
        SymplecticBracket.omega a b := by
  rw [flow_eq_collective]
  exact ProductTorusSymplectic.symplectic (physical_hyp hκ) (e n) t u a b

end QuantumNLS.IndexedSymplecticR28b
#print axioms QuantumNLS.IndexedSymplecticR28b.physical_hyp
#print axioms QuantumNLS.IndexedSymplecticR28b.flow_eq_collective
#print axioms QuantumNLS.IndexedSymplecticR28b.symplectic_flow
