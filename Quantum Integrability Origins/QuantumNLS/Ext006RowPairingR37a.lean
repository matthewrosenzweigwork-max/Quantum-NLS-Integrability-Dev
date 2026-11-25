import QuantumNLS.Ext006SurjectivityR36a
import QuantumNLS.Ext006PhysQuasifree

/-! Exact row-coordinate matrix elements of the actual source fields.
The input smearing can have infinite support. All pairings are on the
constructed smooth domain and use the proved arbitrary-smearing adjointness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006RowPairingR37a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006IdentityCyclicR35a
open Ext006KernelHilbertSchmidt Ext006StrongVacuumR33a
open Ext006SmearedDomainR33a Ext006ModeDomainR33a

lemma inner_ket (z : Fock) (m : Occ) :
    inner ℂ z (ketD m).1=star (z m) := by
  simp [ketD,lp.inner_single_right,RCLike.inner_apply]

lemma C_coefficient (h : H) (z : D) (m : Occ) :
    (C h z).1 m=inner ℂ (star h) (yvec z.1 m) := by
  rw [yvec_eq_sum,inner_sum]
  simp only [inner_smul_right,lp.inner_single_right,RCLike.inner_apply,
    lp.star_apply,Complex.star_def,Complex.conj_conj]
  change (∑ a ∈ m.support, h a * creCoeff a z.1 m)=_
  apply Finset.sum_congr rfl
  intro a _
  simp only [creCoeff,ycoord]
  ring

lemma pair_A (h : H) (z : D) (m : Occ) :
    inner ℂ z.1 (A h (ketD m)).1=inner ℂ h (star (yvec z.1 m)) := by
  rw [show inner ℂ z.1 (A h (ketD m)).1=inner ℂ (C h z).1 (ketD m).1 from
    Ext006SmearedAdjointR34a.adjoint_pairing h z.1 (ketD m).1 z.2 (ketD m).2,
    inner_ket,C_coefficient]
  simpa only [star_star,Complex.star_def] using
    (Ext006PhysSymplectic.inner_star' (star h) (yvec z.1 m)).symm

lemma pair_C (h : H) (z : D) (m : Occ) :
    inner ℂ z.1 (C h (ketD m)).1=inner ℂ (star h) (star (xvec z.1 m)) := by
  rw [show inner ℂ z.1 (C h (ketD m)).1=inner ℂ (A h z).1 (ketD m).1 from
    Ext006SmearedAdjointR34a.adjoint_pairing_rev h z.1 (ketD m).1 z.2 (ketD m).2,
    inner_ket]
  exact (Ext006PhysSymplectic.inner_star' h (xvec z.1 m)).symm

lemma A_mode_ket (a : ℤ) (m : Occ) :
    A (lp.single 2 a 1) (ketD m)=
      (Real.sqrt (m a : ℝ) : ℂ) • ketD (m-e a) := by
  apply Subtype.ext
  apply lp.ext
  funext n
  change inner ℂ (lp.single 2 a (1 : ℂ)) (xvec (ketD m).1 n)=_
  simp only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one]
  change (Real.sqrt ((n a : ℝ)+1) : ℂ)*(lp.single 2 m (1 : ℂ) : Fock) (n+e a)=
    (Real.sqrt (m a : ℝ) : ℂ)*(lp.single 2 (m-e a) (1 : ℂ) : Fock) n
  by_cases hm : m a=0
  · have hne : n+e a ≠ m := by
      intro he
      have hh := congrArg (fun k : Occ => k a) he
      simp only [Finsupp.add_apply,Finsupp.single_eq_same,hm] at hh
      omega
    simp [lp.single_apply,hne,hm]
  · have hma : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr hm
    have he : n+e a=m ↔ n=m-e a := by
      constructor
      · intro h
        apply add_right_cancel (b := e a)
        rw [shift_sub_add hma,h]
      · rintro rfl
        exact shift_sub_add hma
    by_cases hn : n=m-e a
    · subst n
      have ha : ((m-e a) a : ℝ)+1=(m a : ℝ) := by
        have hh := congrArg (fun k : Occ => k a) (shift_sub_add hma)
        simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
        exact_mod_cast hh
      rw [shift_sub_add hma,lp.single_apply_self,lp.single_apply_self,ha]
    · simp [lp.single_apply,hn,he]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Row blocks for the inverse of the constructed source unitary.
These are derived actual blocks; no row implementation identity is assumed. -/
def rowA (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) : H →L[ℂ] H :=
  (coordinateOp b (sourceP S)).adjoint

def rowB (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) : H →L[ℂ] H :=
  tp (coordinateOp b (beta b S))

omit [CompleteSpace E] in
lemma star_r (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (d : ℤ) :
    star (r b S (b d))=star (coordinateOp b (beta b S) (lp.single 2 d 1)) := by
  congr 1
  change b.repr (conjugation b (conjugation b
    (Ext006Blocks.antilinearPart S.toContinuousLinearMap (b d))))=_
  rw [conjugation_sq]
  change b.repr (Ext006Blocks.antilinearPart S.toContinuousLinearMap (b d))=
    b.repr (Ext006Blocks.antilinearPart S.toContinuousLinearMap
      (conjugation b (b.repr.symm (lp.single 2 d 1))))
  rw [b.repr_symm_single]
  rw [conjugation_basis]

omit [CompleteSpace E] in
lemma pair_sourceAnn (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (d : ℤ) (z : D) (m : Occ) :
    inner ℂ z.1 (sourceAnn b S (b d) (ketD m)).1=
      (rowA b S (star (yvec z.1 m))) d+(rowB b S (star (xvec z.1 m))) d := by
  change inner ℂ z.1 ((A (p b S (b d)) (ketD m)).1+
    (C (r b S (b d)) (ketD m)).1)=_
  rw [inner_add_right,pair_A,pair_C,star_r]
  have hp : p b S (b d)=coordinateOp b (sourceP S) (lp.single 2 d 1) := by
    change b.repr (sourceP S (b d))=b.repr (sourceP S (b.repr.symm (lp.single 2 d 1)))
    rw [b.repr_symm_single]
  rw [hp,rowA,rowB,← ContinuousLinearMap.adjoint_inner_right,
    lp.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one]
  rw [Ext006PhysSymplectic.inner_star',← ContinuousLinearMap.adjoint_inner_right,
    lp.inner_single_left,tp_apply,lp.star_apply]
  simp only [RCLike.inner_apply,map_one,mul_one,star_star,Complex.star_def]

omit [CompleteSpace E] in
lemma pair_sourceCre (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (d : ℤ) (z : D) (m : Occ) :
    inner ℂ z.1 (sourceCre b S (b d) (ketD m)).1=
      (Ext006PhysSymplectic.bar (rowA b S) (star (xvec z.1 m))) d+
      (Ext006PhysSymplectic.bar (rowB b S) (star (yvec z.1 m))) d := by
  change inner ℂ z.1 ((C (p b S (b d)) (ketD m)).1+
    (A (r b S (b d)) (ketD m)).1)=_
  rw [inner_add_right,pair_C,pair_A]
  have hp : p b S (b d)=coordinateOp b (sourceP S) (lp.single 2 d 1) := by
    change b.repr (sourceP S (b d))=b.repr (sourceP S (b.repr.symm (lp.single 2 d 1)))
    rw [b.repr_symm_single]
  have hr : r b S (b d)=coordinateOp b (beta b S) (lp.single 2 d 1) :=
    star_injective (star_r b S d)
  simp only [hp,hr,rowA,rowB,Ext006PhysSymplectic.bar_apply,lp.star_apply,tp_apply,star_star]
  rw [Ext006PhysSymplectic.inner_star',
    ← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.adjoint_inner_right,
    lp.inner_single_left,lp.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one,Complex.star_def]

end QuantumNLS.Ext006RowPairingR37a

#print axioms QuantumNLS.Ext006RowPairingR37a.pair_sourceCre

#print axioms QuantumNLS.Ext006RowPairingR37a.pair_A

#print axioms QuantumNLS.Ext006RowPairingR37a.pair_C

#print axioms QuantumNLS.Ext006RowPairingR37a.A_mode_ket

#print axioms QuantumNLS.Ext006RowPairingR37a.star_r

#print axioms QuantumNLS.Ext006RowPairingR37a.pair_sourceAnn

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006RowPairingR37a." then
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
