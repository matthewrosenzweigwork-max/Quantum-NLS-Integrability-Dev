import QuantumNLS.DEF014DiscriminantAnalytic
import QuantumNLS.DEF014Crossings
import QuantumNLS.Ext025A5Triangular

/-! The actual selected separators are real analytic, by the accepted GP-03
analytic implicit theorem applied to the literal discriminant zero equation.
Their continuity identifies the implicit branch with the quantum-selected label. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.DEF014SeparatorAnalytic
open PhysicalTensor (L2T)
open DEF014Phase
variable {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)

def realTrace (p : L2T L × ℝ) : ℝ :=
  (L2SpatialTransfer.discriminant κ p.1 (p.2 : ℂ)).re

theorem analyticAt_realTrace (p : L2T L × ℝ) : AnalyticAt ℝ (realTrace (κ := κ)) p := by
  have hz : AnalyticAt ℝ (fun q : L2T L × ℝ => (q.1, (q.2 : ℂ))) p :=
    analyticAt_fst.prod ((Complex.ofRealCLM.analyticAt _).comp analyticAt_snd)
  exact (Complex.reCLM.analyticAt _).comp
    ((DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ (p.1,(p.2 : ℂ))).comp
      (f := fun q : L2T L × ℝ => (q.1, (q.2 : ℂ))) hz)

/-- Every indexed separator is real analytic on the full real Hilbert space,
including vacuum. No nonzero mass, open-gap, or smallness premise is needed. -/
theorem analyticAt_separator (n : ℤ) (u : L2T L) :
    AnalyticAt ℝ (fun v : L2T L => separator (⟨κ,hκ⟩,v) n) u := by
  let s : L2T L → ℝ := fun v => separator (⟨κ,hκ⟩,v) n
  let f : L2T L × ℝ → ℝ := realTrace (κ := κ)
  let b := s u
  let D := fderiv ℝ f (u,b)
  let A := D.comp (ContinuousLinearMap.inl ℝ (L2T L) ℝ)
  let d := deriv (fun x : ℝ => f (u,x)) b
  have hsimp := DEF014Crossings.separator_simple (⟨κ,hκ⟩,u) n
  have hd : d ≠ 0 := hsimp.2
  let B : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd)
  have hf : AnalyticAt ℝ f (u,b) := analyticAt_realTrace (u,b)
  have hpartial : D.comp (ContinuousLinearMap.inr ℝ (L2T L) ℝ) =
      B.toContinuousLinearMap := by
    have hc := hf.differentiableAt.hasFDerivAt.comp b
      ((hasFDerivAt_const u b).prodMk (hasFDerivAt_id b))
    have hsc : HasDerivAt (fun x : ℝ => f (u,x)) d b :=
      (differentiableAt_of_deriv_ne_zero hd).hasDerivAt
    have he := hc.unique hsc.hasFDerivAt
    change D.comp (ContinuousLinearMap.inr ℝ (L2T L) ℝ) = _ at he
    rw [he]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsplit : A.coprod B.toContinuousLinearMap = D := by
    rw [← hpartial]
    exact D.coprod_comp_inl_inr
  have hder : HasFDerivAt f (A.coprod B.toContinuousLinearMap) (u,b) :=
    hsplit.symm ▸ hf.differentiableAt.hasFDerivAt
  obtain ⟨ψ,hψ,_,_,huniq,_⟩ := Ext025A5.analytic_implicit A B hf hder
  have hsc : Continuous s := (continuous_separator n).comp
    (continuous_const.prodMk continuous_id)
  have hg : ContinuousAt (fun v : L2T L => (v,s v)) u :=
    continuousAt_id.prodMk hsc.continuousAt
  have heq : s =ᶠ[𝓝 u] ψ := by
    filter_upwards [hg.tendsto.eventually huniq] with v hv
    apply (hv.mp ?_).symm
    change (L2SpatialTransfer.discriminant κ v (s v : ℂ)).re =
      (L2SpatialTransfer.discriminant κ u (s u : ℂ)).re
    have hv0 : (L2SpatialTransfer.discriminant κ v (s v : ℂ)).re = 0 :=
      (facts (⟨κ,hκ⟩,v)).separator_zero n
    have hu0 : (L2SpatialTransfer.discriminant κ u (s u : ℂ)).re = 0 :=
      (facts (⟨κ,hκ⟩,u)).separator_zero n
    exact hv0.trans hu0.symm
  exact hψ.congr heq.symm

/-- Contract-fidelity check: half-integer phase separators are strictly
away from the discriminant edge equation Delta^2=4. -/
theorem separator_edge_polynomial (n : ℤ) (u : L2T L) :
    L2SpatialTransfer.discriminant κ u
      (separator (⟨κ,hκ⟩,u) n : ℂ) ^ 2 - 4 = -4 := by
  have he : L2SpatialTransfer.discriminant κ u
      (separator (⟨κ,hκ⟩,u) n : ℂ) = 0 :=
    (facts (⟨κ,hκ⟩,u)).separator_complex_zero n
  rw [he]
  norm_num

end QuantumNLS.DEF014SeparatorAnalytic

-- ROUND 4 AUTHOR AUDIT
#print axioms QuantumNLS.DEF014SeparatorAnalytic.analyticAt_realTrace
#print axioms QuantumNLS.DEF014SeparatorAnalytic.analyticAt_separator
#print axioms QuantumNLS.DEF014SeparatorAnalytic.separator_edge_polynomial

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014SeparatorAnalytic." then
      pending := pending.push n
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
  Lean.logInfo m!"DEF014SeparatorAnalytic audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
