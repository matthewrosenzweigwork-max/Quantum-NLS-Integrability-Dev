import QuantumNLS.Ext006SourceWeylR44a
import QuantumNLS.Ext006OriginalNormalizationR42a
import QuantumNLS.Ext006VacuumNumberR30a

/-! The natural source Weyl implementer: positive vacuum normalization,
and uniqueness among all source implementers with that normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006NaturalWeylR44a
open Ext006SourceWeylR44a Ext006OriginalVacuumR42a Ext006OriginalNormalizationR42a
open Ext006KernelHilbertSchmidt Ext006PhysFockCoord Ext006PhysQuasifree
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

abbrev PF := Ext025B3PhysicalSectors.Fock L

def phaseUnitary (U : PF (L := L) ≃ₗᵢ[ℂ] PF (L := L)) (z : ℂ) (hz : ‖z‖=1) :
    PF (L := L) ≃ₗᵢ[ℂ] PF (L := L) :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap := z • U.toLinearMap
       norm_map' := by
         intro x
         change ‖z • U x‖=‖x‖
         rw [norm_smul,hz,U.norm_map,one_mul] } :
      PF (L := L) →ₗᵢ[ℂ] PF (L := L))
    (by
      intro x
      refine ⟨U.symm (z⁻¹ • x),?_⟩
      have hn : z ≠ 0 := by intro he; simp [he] at hz
      change z • U (U.symm (z⁻¹ • x))=x
      rw [LinearIsometryEquiv.apply_symm_apply,smul_smul,mul_inv_cancel₀ hn,one_smul])

lemma phaseUnitary_apply (U : PF (L := L) ≃ₗᵢ[ℂ] PF (L := L)) (z : ℂ) (hz : ‖z‖=1) (x : PF (L := L)) :
    phaseUnitary U z hz x=z • U x := rfl

lemma phase_implements (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (U : PF (L := L) ≃ₗᵢ[ℂ] PF (L := L)) (hU : SourceWeylImplementer S U)
    (z : ℂ) (hz : ‖z‖=1) : SourceWeylImplementer S (phaseUnitary U z hz) := by
  have hf (f : PhysicalTensor.L2T L) (x : PF (L := L)) :
      U (sourceWeyl f x)=sourceWeyl (S f) (U x) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hU f (U x)
  intro f x
  rw [phaseUnitary_apply,hf,← map_smul]
  have he : z • U ((phaseUnitary U z hz).symm x)=x :=
    (phaseUnitary U z hz).apply_symm_apply x
  rw [he]

/-- Existence of an implementer with exactly the positive-normalized
original-source vacuum, with no free vacuum phase. -/
theorem natural_exists
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ U : PF (L := L) ≃ₗᵢ[ℂ] PF (L := L),
      SourceWeylImplementer S U ∧ U vac=originalVacuum S hS hβ := by
  obtain ⟨U,hU,z,hz,hvac⟩ := sourceWeyl_exists S hS hβ
  have hzi : ‖z⁻¹‖=1 := by rw [norm_inv,hz,inv_one]
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  refine ⟨phaseUnitary U z⁻¹ hzi,phase_implements S U hU z⁻¹ hzi,?_⟩
  rw [phaseUnitary_apply,hvac,smul_smul,inv_mul_cancel₀ hn,one_smul]

lemma phase_eq_one (d : ℂ) (c : ℝ) (hd : ‖d‖=1) (hc : 0<c)
    (him : (d*(c : ℂ)).im=0) (hre : 0<(d*(c : ℂ)).re) : d=1 := by
  have hdim : d.im=0 := by
    simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add] at him
    exact (mul_eq_zero.mp him).resolve_right hc.ne'
  have hdr : 0<d.re := by
    simp only [Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero] at hre
    exact (mul_pos_iff_of_pos_right hc).mp hre
  have hn := Complex.normSq_eq_norm_sq d
  simp only [Complex.normSq_apply,hdim,hd,zero_mul,add_zero,one_pow] at hn
  have hreal : d.re=1 := by nlinarith
  exact Complex.ext hreal (by simpa only [Complex.one_im] using hdim)

/-- Positivity of the vacuum expectation selects a unique source Weyl
implementer, as in BD Theorem 4.2(iv). -/
theorem natural_unique
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (U V : PF (L := L) ≃ₗᵢ[ℂ] PF (L := L))
    (hU : SourceWeylImplementer S U) (hV : SourceWeylImplementer S V)
    (hUv : U vac=originalVacuum S hS hβ)
    (hVi : (inner ℂ vac (V vac)).im=0) (hVr : 0<(inner ℂ vac (V vac)).re) :
    ∀ x : PF (L := L), V x=U x := by
  obtain ⟨d,hd,hphase⟩ := sourceWeyl_unique_phase S U V hU hV
  let c : ℝ := (Ext006FredholmTracePower.fredholmDet
    ((squeeze (physicalBasis L) S hS).adjoint ∘L squeeze (physicalBasis L) S hS))^(1/4 : ℝ)
  have hc : 0<c := by
    have he := originalVacuum_vacuum_positive S hS hβ
    rw [originalVacuum_vacuum_expectation] at he
    exact he
  have hv : inner ℂ vac (V vac)=d*(c : ℂ) := by
    rw [hphase,hUv,inner_smul_right,originalVacuum_vacuum_expectation]
  have hd1 := phase_eq_one d c hd hc (hv ▸ hVi) (hv ▸ hVr)
  intro x
  rw [hphase,hd1,one_smul]

/-- Number expectation at the ORIGINAL beta block. The intermediate row
construction is reoriented, and its beta Hilbert-Schmidt mass is proved
equal to the original one before the conclusion is restated. -/
theorem original_number_hs
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext006NumberPhase.numberExpectation (fun n => (n : ℝ≥0∞)) (originalVacuum S hS hβ) =
      TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) := by
  obtain ⟨U,hA,-,⟨z,hz,hvac⟩,-⟩ :=
    Ext006GlobalCovarianceR43a.original_source_bounded_covariance S hS hβ
  have he := Ext006VacuumNumberR30a.vacuum_number U hA
  rw [hvac,Ext006NumberPhase.«FIN-CORE-BD-02-phase» z hz] at he
  change Ext006NumberPhase.numberExpectation (fun n => (n : ℝ≥0∞)) (originalVacuum S hS hβ) =
    TraceClass.hsSq Ext006VacuumNumberR30a.modeBasis
      (Ext006VacuumNumberR30a.coordinateOperator (physicalBasis L)
        (beta (physicalBasis L) (Ext006ReorientationR42a.reorient S))) at he
  rw [Ext006VacuumNumberR30a.coordinateOperator_hsSq,
    Ext006ReorientationR42a.reorient_beta_hsSq (physicalBasis L) S hS] at he
  exact he

theorem original_number_trace
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext006NumberPhase.numberExpectation (fun n => (n : ℝ≥0∞)) (originalVacuum S hS hβ) =
      TraceClass.posTrace ((beta (physicalBasis L) S).adjoint ∘L beta (physicalBasis L) S) := by
  rw [original_number_hs S hS hβ,
    TraceClass.posTrace_eq (physicalBasis L) (ContinuousLinearMap.isPositive_adjoint_comp_self _),
    TraceClass.traceIn_adjoint_comp_self]

end QuantumNLS.Ext006NaturalWeylR44a
#print axioms QuantumNLS.Ext006NaturalWeylR44a.natural_exists
#print axioms QuantumNLS.Ext006NaturalWeylR44a.natural_unique
#print axioms QuantumNLS.Ext006NaturalWeylR44a.original_number_trace

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006NaturalWeylR44a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
