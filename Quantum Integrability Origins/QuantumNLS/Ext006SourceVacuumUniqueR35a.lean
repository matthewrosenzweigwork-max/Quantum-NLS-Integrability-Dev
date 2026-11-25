import QuantumNLS.Ext006FockEmbeddingR35a

/-! Uniqueness for the actual source-block annihilation equations.
The source P inverse and the proved symmetric squeeze kernel reduce those
equations to the frozen weak recurrence. No implementer is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SourceVacuumUniqueR35a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006SmoothOperatorsR34a
open Ext006SourceCCRR34a Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

lemma p_inverse_basis (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) (a : ℤ) :
    p b S (sourcePInv S hS (b a)) = lp.single 2 a 1 := by
  rw [p,sourcePInv_right,b.repr_self]

lemma r_inverse_basis (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) (a c : ℤ) :
    r b S (sourcePInv S hS (b a)) c =
      Ext006CompressionR32a.coordinates b (squeeze b S hS) a c := by
  have hk := kernel_sourceP b S hS (sourcePInv S hS (b a))
  rw [sourcePInv_right] at hk
  change b.repr (conjugation b (sourceQ b S (sourcePInv S hS (b a)))) c = _
  rw [← hk]
  have he : Ext006SymplecticKernel.kernel S hS (b a) = squeeze b S hS (b a) := by
    simp only [squeeze,antiRepresentative_apply,conjugation_basis]
  rw [he,b.repr_apply_apply]
  exact squeeze_matrix_symmetric b S hS c a

/-- Strong source annihilation implies exactly the original weak squeezed
recurrence, with K=bar(Q P^-1) and its fixed sign. -/
theorem source_ann_implies_weak (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hv : ∀ f,sourceAnn b S f v=0) :
    WeakVacuum (Ext006CompressionR32a.coordinates b (squeeze b S hS)) v.1 := by
  intro a m
  have he := congrArg (fun w : D => w.1 m) (hv (sourcePInv S hS (b a)))
  change inner ℂ (p b S (sourcePInv S hS (b a))) (xvec v.1 m) +
    (∑ c ∈ m.support, r b S (sourcePInv S hS (b a)) c * creCoeff c v.1 m) = 0 at he
  rw [p_inverse_basis,lp.inner_single_left] at he
  simp only [RCLike.inner_apply,map_one,mul_one,r_inverse_basis,creCoeff] at he
  change (Real.sqrt ((m a : ℝ)+1) : ℂ)*v.1 (m+e a) = _
  simpa only [mul_assoc,xvec_apply,xcoord] using eq_neg_of_add_eq_zero_left he

/-- All normalized smooth source vacua are unique up to phase. This is a
vacuum theorem, without any unitary or surjectivity premise. -/
theorem source_vacuum_unique_phase (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S f w=0) :
    ∃ c : ℂ, ‖c‖=1 ∧ w=c • v := by
  obtain ⟨c,hc,he⟩ := normalized_unique_phase
    (source_ann_implies_weak b S hS v hv) (source_ann_implies_weak b S hS w hw) hvn hwn
  exact ⟨c,hc,Subtype.ext he⟩

end QuantumNLS.Ext006SourceVacuumUniqueR35a

#print axioms QuantumNLS.Ext006SourceVacuumUniqueR35a.r_inverse_basis
#print axioms QuantumNLS.Ext006SourceVacuumUniqueR35a.source_ann_implies_weak
#print axioms QuantumNLS.Ext006SourceVacuumUniqueR35a.source_vacuum_unique_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SourceVacuumUniqueR35a." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round35a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
