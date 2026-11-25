import QuantumNLS.Ext006RowPairingR37a

/-! Every unitary satisfying both frozen Heisenberg predicates for the same
symplectic row pair has the SAME squeezed-vacuum recurrence. No smoothness,
canonical construction, or supplied vacuum relation is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006HeisVacuumR37a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006PhysFockCoord Ext006PhysQuasifree Ext006PhysSymplectic
variable {L : ℝ} [Fact (0 < L)]

lemma heis_rows
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hA : HeisAnn V A B) (hC : HeisCre V A B) (n m : Occ) :
    xvec (Vtil V (lp.single 2 m 1)) n=A (uvec V n m)+B (wvec V n m) ∧
    yvec (Vtil V (lp.single 2 m 1)) n=bar A (wvec V n m)+bar B (uvec V n m) := by
  constructor
  · apply lp.ext
    funext d
    rw [xvec_Vtil]
    exact hA d n m _ _ (uvec_apply V n m) (wvec_apply V n m)
  · apply lp.ext
    funext d
    rw [yvec_Vtil]
    exact hC d n m _ _ (uvec_apply V n m) (wvec_apply V n m)

lemma uvec_vacuum
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L) (n : Occ) :
    uvec V n 0=0 := by
  apply lp.ext
  funext c
  rw [uvec_apply,inner_Ann_core]
  simp

/-- Kernel recurrence from an injective annihilator block and its actual
factorization. This lemma is purely algebraic on completed Fock coordinates. -/
lemma weak_from_relation (α β K : H →L[ℂ] H) (hc : α ∘L K=β)
    (hi : Function.Injective α) (z : Fock)
    (hz : ∀ n, α (xvec z n)+β (yvec z n)=0) :
    WeakVacuum (fun a b => K (lp.single 2 b 1) a) z := by
  intro a n
  have hx : xvec z n= -(K (yvec z n)) := by
    apply hi
    rw [map_neg,← ContinuousLinearMap.comp_apply,hc]
    exact eq_neg_of_add_eq_zero_left (hz n)
  have hcoord := congrArg (fun x : H => x a) hx
  simp only [xvec_apply,xcoord,lp.coeFn_neg,Pi.neg_apply] at hcoord
  rw [yvec_eq_sum,map_sum,lp.coeFn_sum] at hcoord
  simp only [Finset.sum_apply,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] at hcoord
  rw [hcoord,neg_inj]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ycoord]
  ring

lemma vacuum_relation
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hs : PhysSymplectic A B)
    (hA : HeisAnn V A B) (hC : HeisCre V A B) (n : Occ) :
    A.adjoint (xvec (Vtil V vacuum) n)+(-tp B) (yvec (Vtil V vacuum) n)=0 := by
  obtain ⟨hX,hY⟩ := heis_rows V A B hA hC n 0
  have hi := invpair_identity hs hX (by simpa only [bar_apply] using hY)
  rw [uvec_vacuum] at hi
  change A.adjoint (xvec (Vtil V (lp.single 2 (0 : Occ) 1)) n)-
    tp B (yvec (Vtil V (lp.single 2 (0 : Occ) 1)) n)=0
  exact hi.symm

/-- A common normalized vacuum phase is derived for ALL implementing
unitaries, not just the constructed source embeddings. -/
theorem all_implementer_vacua_phase
    (V W : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hs : PhysSymplectic A B)
    (hVA : HeisAnn V A B) (hVC : HeisCre V A B)
    (hWA : HeisAnn W A B) (hWC : HeisCre W A B) :
    ∃ c : ℂ, ‖c‖=1 ∧ Vtil W vacuum=c • Vtil V vacuum := by
  obtain ⟨K,hK,-,hi⟩ := exists_kernel (invpair_isBogoliubov hs)
  have hK' : A.adjoint ∘L K=(-tp B) := by
    ext x : 1
    exact hK x
  exact normalized_unique_phase
    (weak_from_relation A.adjoint (-tp B) K hK' hi _ (vacuum_relation V A B hs hVA hVC))
    (weak_from_relation A.adjoint (-tp B) K hK' hi _ (vacuum_relation W A B hs hWA hWC))
    ((Vtil V).norm_map vacuum |>.trans vacuum_norm)
    ((Vtil W).norm_map vacuum |>.trans vacuum_norm)

end QuantumNLS.Ext006HeisVacuumR37a

#print axioms QuantumNLS.Ext006HeisVacuumR37a.weak_from_relation

#print axioms QuantumNLS.Ext006HeisVacuumR37a.vacuum_relation

#print axioms QuantumNLS.Ext006HeisVacuumR37a.all_implementer_vacua_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006HeisVacuumR37a." then
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
  Lean.logInfo m!"Round37a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
