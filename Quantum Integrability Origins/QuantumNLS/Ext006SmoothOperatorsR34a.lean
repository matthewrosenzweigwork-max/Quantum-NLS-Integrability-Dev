import QuantumNLS.Ext006SmearedCCRR34a

/-! The actual smeared operators as linear endomorphisms of their common
invariant domain. All CCR and adjoint pairings are derived from their actions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SmoothOperatorsR34a
open Occupation Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006BogoliubovAlg

lemma smooth_smul (c : ℂ) {w : Occ → ℂ} (hw : Smooth w) : Smooth (c • w) := by
  intro p
  convert (hw p).mul_left (‖c‖^2) using 1
  ext m
  simp only [Pi.smul_apply,norm_smul,mul_pow]
  ring

/-- A submodule of the actual completed Fock carrier. -/
def domain : Submodule ℂ Fock where
  carrier := {w | Smooth w}
  zero_mem' := by intro p; simp
  add_mem' := fun hv hw => Ext006StrongVacuumR33a.smooth_add hv hw
  smul_mem' := fun c _ hw => smooth_smul c hw

abbrev D := domain

lemma xvec_add (v w : Fock) (m : Occ) : xvec (v+w) m = xvec v m+xvec w m := by
  apply lp.ext
  funext a
  change (Real.sqrt ((m a : ℝ)+1) : ℂ)*(v (m+e a)+w (m+e a)) = _
  change _ = (Real.sqrt ((m a : ℝ)+1) : ℂ)*v (m+e a)+(Real.sqrt ((m a : ℝ)+1) : ℂ)*w (m+e a)
  ring

lemma xvec_smul (c : ℂ) (w : Fock) (m : Occ) : xvec (c • w) m = c • xvec w m := by
  apply lp.ext
  funext a
  change (Real.sqrt ((m a : ℝ)+1) : ℂ)*(c*w (m+e a)) = c*((Real.sqrt ((m a : ℝ)+1) : ℂ)*w (m+e a))
  ring

/-- Annihilation on the constructed common domain. -/
def A (h : H) : Module.End ℂ D where
  toFun w := ⟨smearedAnn h w.1 w.2,smearedAnn_smooth h w.1 w.2⟩
  map_add' v w := by
    apply Subtype.ext
    apply lp.ext
    funext m
    change inner ℂ h (xvec (v.1+w.1) m) = inner ℂ h (xvec v.1 m)+inner ℂ h (xvec w.1 m)
    rw [xvec_add,inner_add_right]
  map_smul' c w := by
    apply Subtype.ext
    apply lp.ext
    funext m
    change inner ℂ h (xvec (c • w.1) m) = c*inner ℂ h (xvec w.1 m)
    rw [xvec_smul,inner_smul_right]

/-- Creation on the same domain, with no intermediate domain inputs. -/
def C (h : H) : Module.End ℂ D where
  toFun w := ⟨smearedCre h w.1 w.2,smearedCre_smooth h w.1 w.2⟩
  map_add' v w := by
    apply Subtype.ext
    apply lp.ext
    funext m
    change (∑ a ∈ m.support, h a*creCoeff a (v.1+w.1) m) = _
    simp only [creCoeff,Pi.add_apply,mul_add,Finset.sum_add_distrib]
    rfl
  map_smul' c w := by
    apply Subtype.ext
    apply lp.ext
    funext m
    change (∑ a ∈ m.support, h a*creCoeff a (c • w.1) m) =
      c*(∑ a ∈ m.support, h a*creCoeff a w.1 m)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [creCoeff,Pi.smul_apply,smul_eq_mul]
    ring

/-- All algebraic relations below hold as actual domain endomorphisms. -/
theorem AC (h k : H) : A h*C k-C k*A h = (inner ℂ h k) • (1 : Module.End ℂ D) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact Ext006SmearedCCRR34a.ann_cre h k w.1 w.2

theorem AA (h k : H) : A h*A k = A k*A h := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact Ext006SmearedCCRR34a.ann_ann h k w.1 w.2

theorem CC (h k : H) : C h*C k = C k*C h := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact Ext006SmearedCCRR34a.cre_cre h k w.1 w.2

/-- General Bogoliubov annihilator and its actual adjoint creator. -/
def B (h k : H) : Module.End ℂ D := A h+C k
def Bstar (h k : H) : Module.End ℂ D := C h+A k

theorem BBstar (h k p q : H) : B h k*Bstar p q-Bstar p q*B h k =
    (inner ℂ h p-inner ℂ q k) • (1 : Module.End ℂ D) := by
  calc
    _ = (A h*C p-C p*A h)-(A q*C k-C k*A q)+
        (A h*A q-A q*A h)+(C k*C p-C p*C k) := by unfold B Bstar; noncomm_ring
    _ = _ := by rw [AC,AC,AA h q,CC k p]; module

theorem BB (h k p q : H) : B h k*B p q-B p q*B h k =
    (inner ℂ h q-inner ℂ p k) • (1 : Module.End ℂ D) := by
  calc
    _ = (A h*C q-C q*A h)-(A p*C k-C k*A p)+
        (A h*A p-A p*A h)+(C k*C q-C q*C k) := by unfold B; noncomm_ring
    _ = _ := by rw [AC,AC,AA h p,CC k q]; module

theorem BstarBstar (h k p q : H) : Bstar h k*Bstar p q-Bstar p q*Bstar h k =
    (inner ℂ k p-inner ℂ q h) • (1 : Module.End ℂ D) := by
  simpa only [Bstar,B,add_comm] using BB k h q p

theorem B_adjoint (h k : H) (v w : D) :
    inner ℂ v.1 ((B h k w).1) = inner ℂ ((Bstar h k v).1) w.1 := by
  change inner ℂ v.1 (smearedAnn h w.1 w.2+smearedCre k w.1 w.2) =
    inner ℂ (smearedCre h v.1 v.2+smearedAnn k v.1 v.2) w.1
  rw [inner_add_right,inner_add_left,
    Ext006SmearedAdjointR34a.adjoint_pairing h v.1 w.1 v.2 w.2,
    Ext006SmearedAdjointR34a.adjoint_pairing_rev k v.1 w.1 v.2 w.2]

end QuantumNLS.Ext006SmoothOperatorsR34a

#print axioms QuantumNLS.Ext006SmoothOperatorsR34a.AC
#print axioms QuantumNLS.Ext006SmoothOperatorsR34a.BBstar
#print axioms QuantumNLS.Ext006SmoothOperatorsR34a.BB
#print axioms QuantumNLS.Ext006SmoothOperatorsR34a.B_adjoint

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SmoothOperatorsR34a." then
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
