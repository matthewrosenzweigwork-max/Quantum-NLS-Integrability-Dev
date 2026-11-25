import QuantumNLS.RB01Main
import QuantumNLS.RootMassPropernessR27
import QuantumNLS.RootMassInvolutionBatchR9
import QuantumNLS.ProductTorusSymplectic

/-! R107: actual physical hypotheses for the frozen complete Hamiltonian flow.
B01 (R-EC25334D) is accepted and supplies collective analyticity; properness
and involution are the accepted R-0191D778 and R-507DD869. No torus period or
coordinate construction is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
namespace QuantumNLS.CompleteFlowPhysicalR107
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

/-- The actual complete n-th mass flow, with the printed time normalization. -/
def phi (hκ : 0 < κ) (n : ℤ) : ℝ → L2T L → L2T L :=
  flow (fderiv ℝ (Actions (L := L) hκ)) (e n)

theorem phi_spec (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    phi hκ n 0 u = u ∧ ∀ t,
      HasDerivAt (fun s => phi hκ n s u)
        (SymplecticBracket.hamField (mass (L := L) hκ n) (phi hκ n t u)) t := by
  refine ⟨flow_zero (physical_hyp hκ) (e n) u, fun t => ?_⟩
  simpa only [phi, coordinate_field hκ n] using
    hasDerivAt_flow (physical_hyp hκ) (e n) u t

end QuantumNLS.CompleteFlowPhysicalR107
#print axioms QuantumNLS.CompleteFlowPhysicalR107.physical_hyp
#print axioms QuantumNLS.CompleteFlowPhysicalR107.phi_spec

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.CompleteFlowPhysicalR107." ||
        n.toString.startsWith "_private.QuantumNLS.CompleteFlowPhysicalR107." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R107 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
