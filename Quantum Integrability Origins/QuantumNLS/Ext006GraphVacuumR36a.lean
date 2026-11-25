import QuantumNLS.Ext006InverseGraphsR36a

/-! Reduce inverse weak-graph vacuum equations to the original coefficient
recurrence without assuming smoothness of that vector. The extension uses
a continuous FINITE-coordinate functional and the proved dense polynomial
core. It therefore identifies the nonzero pulled-back vacuum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006GraphVacuumR36a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006SmoothOperatorsR34a
open Ext006SourceCCRR34a Ext006CreationGramR34a Ext006CyclicIsometryR34a
open Ext006IdentityCyclicR35a Ext006FockEmbeddingR35a Ext006CoreTransportR35a
open Ext006SourceVacuumUniqueR35a Ext006ClosedFieldGraphsR36a
open Ext006AdjointTransportR36a Ext006InverseSourceR36a Ext006InverseGraphsR36a
open Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Each recurrence uses only finitely many Fock coordinates. -/
def recurrenceFunctional (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (a : ℤ) (m : Occ) (x : Fock) : ℂ :=
  (Real.sqrt ((m a : ℝ)+1) : ℂ)*x (m+e a)+
    ∑ c ∈ m.support, Ext006CompressionR32a.coordinates b (squeeze b S hS) a c * creCoeff c x m

lemma recurrenceFunctional_continuous (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) (a : ℤ) (m : Occ) :
    Continuous (recurrenceFunctional b S hS a m) := by
  have hev (n : Occ) : Continuous (fun x : Fock => x n) :=
    (lp.evalCLM (E := fun _ : Occ => ℂ) (p := 2) ℂ n).continuous
  exact (continuous_const.mul (hev _)).add
    (continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_const.mul (hev _))))

lemma source_test_smooth (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (a : ℤ) (m : Occ) (w : D) :
    inner ℂ (sourceCre b S (sourcePInv S hS (b a)) (ketD m)).1 w.1 =
      recurrenceFunctional b S hS a m w.1 := by
  rw [← source_adjoint]
  have hket (y : Fock) : inner ℂ (ketD m).1 y=y m := by
    simp [ketD,lp.inner_single_left,RCLike.inner_apply]
  rw [hket]
  change inner ℂ (p b S (sourcePInv S hS (b a))) (xvec w.1 m)+
    (∑ c ∈ m.support, r b S (sourcePInv S hS (b a)) c * creCoeff c w.1 m) = _
  rw [p_inverse_basis,lp.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one,r_inverse_basis]
  rfl

/-- Extend the exact test equation to every Fock vector using continuity of
its finite-coordinate right side. No domain premise is added to x. -/
theorem source_test_recurrence (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (a : ℤ) (m : Occ) (x : Fock) :
    inner ℂ (sourceCre b S (sourcePInv S hS (b a)) (ketD m)).1 x =
      recurrenceFunctional b S hS a m x := by
  have hcont : Continuous (fun y : Fock =>
      inner ℂ (sourceCre b S (sourcePInv S hS (b a)) (ketD m)).1 y) :=
    continuous_const.inner continuous_id
  have he := (identity_eval_dense b).equalizer
    hcont (recurrenceFunctional_continuous b S hS a m)
    (funext fun c => by
      simp only [Function.comp_apply]
      rw [← evalDomain_val b identitySource (ketD 0) c]
      exact source_test_smooth b S hS a m (evalDomain b identitySource (ketD 0) c))
  exact congrFun he x

/-- Weak-graph annihilation implies the original weak squeezed recurrence,
even when the input vector has no supplied smooth-domain membership. -/
theorem graph_vacuum_weak (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (x : Fock) (hx : ∀ f, AnnGraph b S f x 0) :
    WeakVacuum (Ext006CompressionR32a.coordinates b (squeeze b S hS)) x := by
  intro a m
  have h := hx (sourcePInv S hS (b a)) m
  rw [inner_zero_right,source_test_recurrence] at h
  change (Real.sqrt ((m a : ℝ)+1) : ℂ)*x (m+e a) = _
  have hz : (Real.sqrt ((m a : ℝ)+1) : ℂ)*x (m+e a)+
      (∑ c ∈ m.support, Ext006CompressionR32a.coordinates b (squeeze b S hS) a c *
        (Real.sqrt (m c : ℝ) : ℂ)*x (m-e c))=0 := by
    simpa only [recurrenceFunctional,creCoeff,mul_assoc] using h.symm
  exact eq_neg_of_add_eq_zero_left hz

/-- Identify the pulled-back vacuum with a nonzero scalar multiple of ANY
normalized smooth inverse-source vacuum. All graph-to-recurrence and scalar
uniqueness steps are derived; the pullback's smoothness follows afterwards. -/
theorem pullback_vacuum_scalar (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S.symm f w=0) :
    ∃ c : ℂ, c ≠ 0 ∧ pullback b S hS v hvn hv vacuum=c • w.1 := by
  let x := pullback b S hS v hvn hv vacuum
  have hx : WeakVacuum (Ext006CompressionR32a.coordinates b
      (squeeze b S.symm (inverse_symplectic S hS))) x :=
    graph_vacuum_weak b S.symm (inverse_symplectic S hS) x
      (pullback_vacuum_inverse_graph b S hS v hvn hv)
  have hweak := source_ann_implies_weak b S.symm (inverse_symplectic S hS) w hw
  let c : ℂ := x 0/w.1 0
  have he : x=c • w.1 := by
    apply vacuum_coefficient_injective hx (hweak.smul c)
    change x 0=c*w.1 0
    exact (div_mul_cancel₀ _ (vacuum_coefficient_ne_zero hweak hwn)).symm
  refine ⟨c,?_,he⟩
  intro hz
  have hzero : x=0 := by rw [he,hz,zero_smul]
  exact pullback_vacuum_ne_zero b S hS v hvn hv hzero

end QuantumNLS.Ext006GraphVacuumR36a

#print axioms QuantumNLS.Ext006GraphVacuumR36a.source_test_recurrence
#print axioms QuantumNLS.Ext006GraphVacuumR36a.graph_vacuum_weak
#print axioms QuantumNLS.Ext006GraphVacuumR36a.pullback_vacuum_scalar

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006GraphVacuumR36a." then
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
  Lean.logInfo m!"Round36a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
