import QuantumNLS.Ext006SmearedAdjointR34a
import QuantumNLS.Ext006ModeCCRR33a

/-! CCR for arbitrary l2 smearings on the completed invariant domain.
Finite donor sums handle creation. Adjointness then proves annihilator
commutation without interchanging an unproved double infinite sum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SmearedCCRR34a
open Occupation Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006BogoliubovAlg
open Ext006ModeCCRR33a

/-- Creation on arbitrary coefficient functions, before completion. -/
def rawCre (h : H) (w : Occ → ℂ) (m : Occ) : ℂ :=
  ∑ a ∈ m.support, h a*creCoeff a w m

lemma rawCre_eq (h : H) (w : Occ → ℂ) (m : Occ) (s : Finset ℤ)
    (hs : m.support ⊆ s) : rawCre h w m = ∑ a ∈ s, h a*creCoeff a w m := by
  apply Finset.sum_subset hs
  intro a _ ha
  have hz : m a = 0 := by simpa using ha
  simp [creCoeff,hz]

lemma mode_ann_rawCre (h : H) (w : Occ → ℂ) (a : ℤ) (m : Occ) :
    annCoeff a (rawCre h w) m = rawCre h (annCoeff a w) m + h a*w m := by
  let s := insert a ((m+e a).support ∪ m.support)
  have hs1 : (m+e a).support ⊆ s := by intro b hb; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hb)
  have hs2 : m.support ⊆ s := by intro b hb; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hb)
  have he : annCoeff a (rawCre h w) m = ∑ b ∈ s, h b*annCoeff a (creCoeff b w) m := by
    rw [annCoeff, rawCre_eq h w (m+e a) s hs1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [annCoeff]
    ring
  rw [he,rawCre_eq h (annCoeff a w) m s hs2]
  have hc (b : ℤ) : annCoeff a (creCoeff b w) m =
      creCoeff b (annCoeff a w) m + (if a=b then (1 : ℂ) else 0)*w m := by
    have := ann_cre_coeff a b w m
    linear_combination this
  simp only [hc, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Ne.symm hba]
  · simp [s]

lemma mode_cre_rawCre (h : H) (w : Occ → ℂ) (a : ℤ) (m : Occ) :
    creCoeff a (rawCre h w) m = rawCre h (creCoeff a w) m := by
  have he : creCoeff a (rawCre h w) m =
      ∑ b ∈ m.support, h b*creCoeff a (creCoeff b w) m := by
    rw [creCoeff, rawCre_eq h w (m-e a) m.support Finsupp.support_tsub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [creCoeff]
    ring
  rw [he,rawCre]
  apply Finset.sum_congr rfl
  intro b _
  rw [congrFun (cre_cre_coeff a b w) m]

lemma rawCre_comm (h k : H) (w : Occ → ℂ) :
    rawCre h (rawCre k w) = rawCre k (rawCre h w) := by
  funext m
  change (∑ a ∈ m.support, h a*creCoeff a (rawCre k w) m) = _
  simp only [mode_cre_rawCre,rawCre,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [congrFun (cre_cre_coeff a b w) m]
  ring

/-- Completed creators commute for all l2 test vectors. -/
theorem cre_cre (h k : H) (w : Fock) (hw : Smooth w) :
    smearedCre h (smearedCre k w hw) (smearedCre_smooth k w hw) =
      smearedCre k (smearedCre h w hw) (smearedCre_smooth h w hw) := by
  apply lp.ext
  exact rawCre_comm h k w

/-- The annihilation-coordinate vector after one smeared creation. -/
lemma xvec_cre (k : H) (w : Fock) (hw : Smooth w) (m : Occ) :
    xvec (smearedCre k w hw) m =
      (∑ b ∈ m.support, (k b*(Real.sqrt (m b : ℝ) : ℂ)) • xvec w (m-e b)) + (w m) • k := by
  apply lp.ext
  funext a
  change annCoeff a (rawCre k w) m = _
  rw [mode_ann_rawCre]
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,rawCre,creCoeff]
  rw [mul_comm (k a) (w m)]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  change k b*((Real.sqrt (m b : ℝ) : ℂ)*annCoeff a w (m-e b)) =
    k b*(Real.sqrt (m b : ℝ) : ℂ)*annCoeff a w (m-e b)
  ring

/-- The mixed CCR includes its full inner product, not a finite-mode sum. -/
theorem ann_cre (h k : H) (w : Fock) (hw : Smooth w) :
    smearedAnn h (smearedCre k w hw) (smearedCre_smooth k w hw) -
      smearedCre k (smearedAnn h w hw) (smearedAnn_smooth h w hw) =
        (inner ℂ h k) • w := by
  apply lp.ext
  funext m
  change inner ℂ h (xvec (smearedCre k w hw) m) -
    smearedCreCoeff k (smearedAnn h w hw) m = inner ℂ h k*w m
  rw [xvec_cre,inner_add_right,inner_sum,inner_smul_right]
  have he : (∑ b ∈ m.support, inner ℂ h
      ((k b*(Real.sqrt (m b : ℝ) : ℂ)) • xvec w (m-e b))) =
      smearedCreCoeff k (smearedAnn h w hw) m := by
    simp only [inner_smul_right,smearedCreCoeff,creCoeff]
    apply Finset.sum_congr rfl
    intro b _
    change k b*(Real.sqrt (m b : ℝ) : ℂ)*inner ℂ h (xvec w (m-e b)) =
      k b*((Real.sqrt (m b : ℝ) : ℂ)*inner ℂ h (xvec w (m-e b)))
    ring
  rw [he]
  ring

lemma single_smooth (m : Occ) : Smooth (lp.single 2 m (1 : ℂ) : Fock) := by
  intro p
  apply summable_of_ne_finset_zero (s := {m})
  intro n hn
  have hnm : n ≠ m := by simpa using hn
  simp [lp.single_apply,hnm]

/-- Annihilators commute by the proved adjoint pairing and creator algebra. -/
theorem ann_ann (h k : H) (w : Fock) (hw : Smooth w) :
    smearedAnn h (smearedAnn k w hw) (smearedAnn_smooth k w hw) =
      smearedAnn k (smearedAnn h w hw) (smearedAnn_smooth h w hw) := by
  have he (m : Occ) :
      inner ℂ (lp.single 2 m (1 : ℂ) : Fock)
        (smearedAnn h (smearedAnn k w hw) (smearedAnn_smooth k w hw)) =
      inner ℂ (lp.single 2 m (1 : ℂ) : Fock)
        (smearedAnn k (smearedAnn h w hw) (smearedAnn_smooth h w hw)) := by
    let v : Fock := lp.single 2 m (1 : ℂ)
    have hv : Smooth v := single_smooth m
    calc
      _ = inner ℂ (smearedCre h v hv) (smearedAnn k w hw) :=
        Ext006SmearedAdjointR34a.adjoint_pairing h v _ hv _
      _ = inner ℂ (smearedCre k (smearedCre h v hv) (smearedCre_smooth h v hv)) w :=
        Ext006SmearedAdjointR34a.adjoint_pairing k _ w _ hw
      _ = inner ℂ (smearedCre h (smearedCre k v hv) (smearedCre_smooth k v hv)) w := by
        rw [cre_cre]
      _ = inner ℂ (smearedCre k v hv) (smearedAnn h w hw) :=
        (Ext006SmearedAdjointR34a.adjoint_pairing h _ w _ hw).symm
      _ = _ := (Ext006SmearedAdjointR34a.adjoint_pairing k v _ hv _).symm
  apply lp.ext
  funext m
  simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using he m

end QuantumNLS.Ext006SmearedCCRR34a

#print axioms QuantumNLS.Ext006SmearedCCRR34a.cre_cre
#print axioms QuantumNLS.Ext006SmearedCCRR34a.ann_cre
#print axioms QuantumNLS.Ext006SmearedCCRR34a.ann_ann

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SmearedCCRR34a." then
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
  Lean.logInfo m!"Round34a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
