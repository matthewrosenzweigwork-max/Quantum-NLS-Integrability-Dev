import QuantumNLS.Prop001RthirteenProduct
import QuantumNLS.RootOverlapLimit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.Prop001RfourteenSlots
open TensorCarrier TensorPlacements RootOverlapCommutator PhysicalEnergyTrace
  Ext025A12Collision Prop001RthirteenProduct Ext025A8 Prop001
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exchange the two finite tails while retaining a distinguished coordinate. -/
def shuffle (n k : ℕ) : Option (Fin n) ⊕ Fin k ≃ Option (Fin k) ⊕ Fin n where
  toFun := fun x => match x with
    | .inl none => .inl none
    | .inl (some i) => .inr i
    | .inr i => .inl (some i)
  invFun := fun x => match x with
    | .inl none => .inl none
    | .inl (some i) => .inr i
    | .inr i => .inl (some i)
  left_inv := by rintro ((_|i)|i) <;> rfl
  right_inv := by rintro ((_|i)|i) <;> rfl

/-- Active coordinates first, with the selected output slot distinguished. -/
def slotEquiv (k n : ℕ) (j : Fin (k+1)) : Fin (n+1+k) ≃ Fin ((k+1)+n) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (finSuccEquiv n) (Equiv.refl _)).trans
    ((shuffle n k).trans ((Equiv.sumCongr (finSuccEquiv' j).symm (Equiv.refl _)).trans
      finSumFinEquiv)))

@[simp] theorem slotEquiv_zero (k n : ℕ) (j : Fin (k+1)) :
    slotEquiv k n j (Fin.castAdd k 0) = Fin.castAdd n j := by
  simp [slotEquiv,shuffle]

@[simp] theorem slotEquiv_succ (k n : ℕ) (j : Fin (k+1)) (i : Fin n) :
    slotEquiv k n j (Fin.castAdd k i.succ) = Fin.natAdd (k+1) i := by
  simp [slotEquiv,shuffle]

@[simp] theorem slotEquiv_tail (k n : ℕ) (j : Fin (k+1)) (i : Fin k) :
    slotEquiv k n j (Fin.natAdd (n+1) i) = Fin.castAdd n (j.succAbove i) := by
  simp [slotEquiv,shuffle,finSuccEquiv'_symm_some]

def slotPerm (k n : ℕ) (j : Fin (k+1)) : Equiv.Perm (Fin (n+1+k)) :=
  (slotEquiv k n j).trans (finCongr (by omega))

theorem slotPerm_maps (k n : ℕ) (j : Fin (k+1)) :
    placementSubsetOfPerm (slotPerm k n j) = oneOverlapSubset k n j := by
  classical
  apply Subtype.ext
  ext x
  simp only [placementSubsetOfPerm,firstPositions,Finset.mem_map,Finset.mem_univ,
    true_and,Fin.castAddEmb_apply,Equiv.coe_toEmbedding]
  change (∃ a : Fin (n+1+k), (∃ i : Fin (n+1), Fin.castAdd k i = a) ∧
    slotPerm k n j a = x) ↔ _
  simp only [exists_exists_eq_and]
  unfold oneOverlapSubset
  simp only [Finset.mem_map,Finset.mem_insert,Finset.mem_univ,true_and,
    Fin.natAddEmb_apply,Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun a => ?_) i
    · refine ⟨Fin.castAdd n j,Or.inl rfl,?_⟩
      simp [slotPerm]
    · refine ⟨Fin.natAdd (k+1) a,Or.inr ⟨a,rfl⟩,?_⟩
      simp [slotPerm]
  · rintro ⟨y,(hy|⟨a,rfl⟩),rfl⟩
    · subst y
      exact ⟨0,by simp [slotPerm]⟩
    · exact ⟨a.succ,by simp [slotPerm]⟩

theorem placedInteraction_slotPerm (k n : ℕ) (j : Fin (k+1))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) :
    placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A =
      placedInteraction k n (slotPerm k n j) A := by
  unfold placedInteraction
  congr 1
  exact (permutedPlacement_eq_subsetPlacement _ _ (subsetRepresentative_maps _) A).trans
    (permutedPlacement_eq_subsetPlacement _ _ (slotPerm_maps k n j) A).symm

end QuantumNLS.Prop001RfourteenSlots

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RfourteenSlots" then
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
  Lean.logInfo m!"Prop001RfourteenSlots audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfourteenSlots.shuffle

#print axioms QuantumNLS.Prop001RfourteenSlots.slotEquiv

#print axioms QuantumNLS.Prop001RfourteenSlots.slotEquiv_zero

#print axioms QuantumNLS.Prop001RfourteenSlots.slotEquiv_succ

#print axioms QuantumNLS.Prop001RfourteenSlots.slotEquiv_tail

#print axioms QuantumNLS.Prop001RfourteenSlots.slotPerm

#print axioms QuantumNLS.Prop001RfourteenSlots.slotPerm_maps

#print axioms QuantumNLS.Prop001RfourteenSlots.placedInteraction_slotPerm
