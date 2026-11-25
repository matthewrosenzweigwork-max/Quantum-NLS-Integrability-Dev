import QuantumNLS.Ext006ExponentialInnerR43a
import Mathlib.Analysis.Normed.Operator.Extend

/-! Bounded unitaries on the whole occupation Fock space, constructed by
extending the ACTUAL entire field sums on a proved dense finite-particle
core. No self-adjointness or Weyl uniqueness premise is introduced. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006BoundedExponentialR43a
open Ext006IdentityCyclicR35a Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006ExponentialInnerR43a

/-- Smooth vectors with bounded particle number, allowing infinite mode support. -/
def particleDomain : Submodule ℂ D where
  carrier := {v | ∃ N, ParticleBound N v.1}
  zero_mem' := ⟨0,by intro m _; simp⟩
  add_mem' := by
    rintro v w ⟨N,hN⟩ ⟨M,hM⟩
    refine ⟨max N M,fun m hm => ?_⟩
    change v.1 m+w.1 m=0
    rw [hN m (lt_of_le_of_lt (le_max_left N M) hm),
      hM m (lt_of_le_of_lt (le_max_right N M) hm),zero_add]
  smul_mem' := by
    rintro z v ⟨N,hN⟩
    refine ⟨N,fun m hm => ?_⟩
    change z*v.1 m=0
    rw [hN m hm,mul_zero]

abbrev Core := particleDomain

def inclusion : Core →ₗ[ℂ] Fock :=
  Ext006SmoothOperatorsR34a.domain.subtype.comp particleDomain.subtype

lemma core_dense : DenseRange inclusion := by
  intro x
  have hket (m : Occ) : (ketD m).1 ∈ inclusion.range :=
    ⟨⟨ketD m,⟨total m,ket_particleBound m⟩⟩,rfl⟩
  have ht : inclusion.range.topologicalClosure = ⊤ := by
    apply top_unique
    intro y _
    apply inclusion.range.isClosed_topologicalClosure.mem_of_tendsto
      (lp.hasSum_single (by norm_num) y)
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro m _
    have hm : (lp.single 2 m (y m) : Fock) = y m • (ketD m).1 := by
      rw [ketD,← lp.single_smul]
      simp
    rw [hm]
    exact Submodule.smul_mem _ _ (inclusion.range.le_topologicalClosure (hket m))
  have hx : x ∈ inclusion.range.topologicalClosure := by rw [ht]; trivial
  change x ∈ closure (inclusion.range : Set Fock) at hx
  change x ∈ closure (Set.range (fun v : Core => inclusion v))
  have hr : Set.range (fun v : Core => inclusion v) = (inclusion.range : Set Fock) := by
    ext z
    rfl
  rw [hr]
  exact hx

lemma term_add (h : H) (t : ℝ) (v w : D) (n : ℕ) :
    exponentialTerm h t (v+w) n = exponentialTerm h t v n+exponentialTerm h t w n := by
  simp only [exponentialTerm,map_add,Submodule.coe_add,smul_add]

lemma term_smul (h : H) (t : ℝ) (z : ℂ) (v : D) (n : ℕ) :
    exponentialTerm h t (z • v) n = z • exponentialTerm h t v n := by
  simp only [exponentialTerm,map_smul,Submodule.coe_smul,smul_smul]
  congr 1
  exact mul_comm _ _

/-- A linear map on the proved dense core, from convergent literal sums. -/
def exponentialLinear (h : H) (t : ℝ) : Core →ₗ[ℂ] Fock where
  toFun v := exponential h t v.1
  map_add' v w := by
    obtain ⟨N,hN⟩ := v.2
    obtain ⟨M,hM⟩ := w.2
    simp only [exponential,Submodule.coe_add,term_add]
    exact (entire_summable h t v.1 hN).tsum_add (entire_summable h t w.1 hM)
  map_smul' z v := by
    simp only [exponential,Submodule.coe_smul,term_smul,RingHom.id_apply]
    obtain ⟨N,hN⟩ := v.2
    exact (entire_summable h t v.1 hN).tsum_const_smul z

lemma exponentialLinear_norm (h : H) (t : ℝ) (v : Core) :
    ‖exponentialLinear h t v‖ = ‖inclusion v‖ := by
  obtain ⟨N,hN⟩ := v.2
  exact exponential_norm h t v.1 hN

/-- The whole-space isometry is an extension, not an assumption. -/
def evolution (h : H) (t : ℝ) : Fock →ₗᵢ[ℂ] Fock :=
  LinearMap.extendOfIsometry (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Core) (Eₗ := Fock) (F := Fock)
    (σ₁₂ := RingHom.id ℂ) (exponentialLinear h t) (e := inclusion) core_dense
    (exponentialLinear_norm h t)

lemma evolution_core (h : H) (t : ℝ) (v : Core) :
    evolution h t (inclusion v) = exponential h t v.1 :=
  by
    unfold evolution
    rw [LinearMap.extendOfIsometry_eq]
    rfl

/-- Adjointness comes from the actual series and is extended by density. -/
theorem evolution_adjoint (h : H) (t : ℝ) (x y : Fock) :
    inner ℂ x (evolution h t y) = inner ℂ (evolution h (-t) x) y := by
  apply core_dense.induction_on₂
    (p := fun x y => inner ℂ x (evolution h t y) = inner ℂ (evolution h (-t) x) y)
    (isClosed_eq (continuous_fst.inner ((evolution h t).continuous.comp continuous_snd))
      (((evolution h (-t)).continuous.comp continuous_fst).inner continuous_snd)) ?_ x y
  intro v w
  obtain ⟨N,hN⟩ := v.2
  obtain ⟨M,hM⟩ := w.2
  rw [evolution_core,evolution_core]
  have he := inner_exponentials h (-t) 0 v.1 w.1 hN hM
  simpa only [exponential_zero,zero_sub,neg_neg,inclusion,LinearMap.comp_apply,Submodule.subtype_apply] using he.symm

/-- The two bounded extensions are inverse on ALL Fock vectors. -/
theorem evolution_inverse (h : H) (t : ℝ) (x : Fock) :
    evolution h (-t) (evolution h t x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [evolution_adjoint,neg_neg,(evolution h t).inner_map_map]

/-- Bounded unitary of the literal field exponential on the whole Fock space. -/
def unitary (h : H) (t : ℝ) : Fock ≃ₗᵢ[ℂ] Fock :=
  LinearIsometryEquiv.ofSurjective (evolution h t) (fun x =>
    ⟨evolution h (-t) x,by simpa only [neg_neg] using evolution_inverse h (-t) x⟩)

lemma unitary_core (h : H) (t : ℝ) (v : Core) :
    unitary h t (inclusion v) = exponential h t v.1 := evolution_core h t v

end QuantumNLS.Ext006BoundedExponentialR43a
#print axioms QuantumNLS.Ext006BoundedExponentialR43a.core_dense
#print axioms QuantumNLS.Ext006BoundedExponentialR43a.unitary
#print axioms QuantumNLS.Ext006BoundedExponentialR43a.unitary_core

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006BoundedExponentialR43a." then
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
  Lean.logInfo m!"Round43a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
