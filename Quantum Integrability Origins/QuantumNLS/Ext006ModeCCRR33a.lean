import QuantumNLS.Ext006ModeDomainR33a

/-! Strong CCR on the completed common polynomial-number domain. Transpose
identities on the finite core prove the coefficient identities without any
unjustified interchange of infinite sums. Every finite word then has a
constructed Fock vector and a proved invariant domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006ModeCCRR33a
open Occupation Ext006VacuumRecurrence Ext006ModeDomainR33a

/-- Algebraic testing against finite-support vectors. -/
def test (w : Occ → ℂ) : FS →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ w

@[simp] lemma test_ket (w : Occ → ℂ) (m : Occ) : test w (ket m) = w m := by simp [test, ket]

lemma test_ann (a : ℤ) (w : Occ → ℂ) (v : FS) :
    test (annCoeff a w) v = test w (Cre a v) := by
  have he : test (annCoeff a w) = (test w).comp (Cre a) := by
    apply Finsupp.lhom_ext
    intro m c
    have hc : Finsupp.single m c = c • ket m := by simp
    change test (annCoeff a w) (Finsupp.single m c) = test w (Cre a (Finsupp.single m c))
    simp only [hc, map_smul, Cre_ket, test_ket, smul_eq_mul]
    rfl
  exact LinearMap.congr_fun he v

lemma test_cre (a : ℤ) (w : Occ → ℂ) (v : FS) :
    test (creCoeff a w) v = test w (Ann a v) := by
  have he : test (creCoeff a w) = (test w).comp (Ann a) := by
    apply Finsupp.lhom_ext
    intro m c
    have hc : Finsupp.single m c = c • ket m := by simp
    change test (creCoeff a w) (Finsupp.single m c) = test w (Ann a (Finsupp.single m c))
    simp only [hc, map_smul, Ann_ket, test_ket, smul_eq_mul]
    rfl
  exact LinearMap.congr_fun he v

/-- The full coefficient CCR for arbitrary coefficient functions. -/
theorem ann_cre_coeff (a b : ℤ) (w : Occ → ℂ) (m : Occ) :
    annCoeff a (creCoeff b w) m - creCoeff b (annCoeff a w) m =
      (if a=b then (1 : ℂ) else 0)*w m := by
  calc
    _ = test w ((Ann b*Cre a-Cre a*Ann b) (ket m)) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub,
        ← test_cre, ← test_ann, test_ket]
    _ = _ := by
      rw [Ann_Cre_comm]
      by_cases hab : a=b <;> simp [hab, eq_comm]

theorem ann_ann_coeff (a b : ℤ) (w : Occ → ℂ) :
    annCoeff a (annCoeff b w) = annCoeff b (annCoeff a w) := by
  funext m
  have h := congrArg (fun T : Module.End ℂ FS => test w (T (ket m))) (Cre_Cre_comm b a)
  simpa only [Module.End.mul_apply, ← test_ann, test_ket] using h

theorem cre_cre_coeff (a b : ℤ) (w : Occ → ℂ) :
    creCoeff a (creCoeff b w) = creCoeff b (creCoeff a w) := by
  funext m
  have h := congrArg (fun T : Module.End ℂ FS => test w (T (ket m))) (Ann_Ann_comm b a)
  simpa only [Module.End.mul_apply, ← test_cre, test_ket] using h

/-- Strong CCR with all four operator domains proved by invariance. -/
theorem ann_cre (a b : ℤ) (w : Fock) (hw : Smooth w) :
    ann a (cre b w hw) (cre_smooth b w hw) -
      cre b (ann a w hw) (ann_smooth a w hw) =
        (if a=b then (1 : ℂ) else 0) • w := by
  apply lp.ext
  funext m
  exact ann_cre_coeff a b w m

theorem ann_ann (a b : ℤ) (w : Fock) (hw : Smooth w) :
    ann a (ann b w hw) (ann_smooth b w hw) =
      ann b (ann a w hw) (ann_smooth a w hw) := by
  apply lp.ext
  exact ann_ann_coeff a b w

theorem cre_cre (a b : ℤ) (w : Fock) (hw : Smooth w) :
    cre a (cre b w hw) (cre_smooth b w hw) =
      cre b (cre a w hw) (cre_smooth a w hw) := by
  apply lp.ext
  exact cre_cre_coeff a b w

inductive Mode where
  | annihilate (a : ℤ)
  | create (a : ℤ)

def act : Mode → (Occ → ℂ) → (Occ → ℂ)
  | .annihilate a => annCoeff a
  | .create a => creCoeff a

def word : List Mode → (Occ → ℂ) → (Occ → ℂ)
  | [], w => w
  | op::ops, w => act op (word ops w)

lemma smooth_act (op : Mode) {w : Occ → ℂ} (hw : Smooth w) : Smooth (act op w) := by
  cases op with
  | annihilate a => exact hw.ann a
  | create a => exact hw.cre a

/-- No word of finite length requires a new domain hypothesis. -/
theorem smooth_word (ops : List Mode) {w : Occ → ℂ} (hw : Smooth w) :
    Smooth (word ops w) := by
  induction ops with
  | nil => exact hw
  | cons op ops ih => exact smooth_act op ih

/-- Actual vector obtained by an arbitrary ordered mode polynomial monomial. -/
def wordVector (ops : List Mode) (w : Fock) (hw : Smooth w) : Fock :=
  ⟨word ops w, (smooth_word ops hw).memℓp⟩

end QuantumNLS.Ext006ModeCCRR33a

#print axioms QuantumNLS.Ext006ModeCCRR33a.ann_cre_coeff

#print axioms QuantumNLS.Ext006ModeCCRR33a.ann_ann_coeff

#print axioms QuantumNLS.Ext006ModeCCRR33a.cre_cre_coeff

#print axioms QuantumNLS.Ext006ModeCCRR33a.ann_cre

#print axioms QuantumNLS.Ext006ModeCCRR33a.ann_ann

#print axioms QuantumNLS.Ext006ModeCCRR33a.cre_cre

#print axioms QuantumNLS.Ext006ModeCCRR33a.smooth_word

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ModeCCRR33a." then
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
  Lean.logInfo m!"Round33a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
