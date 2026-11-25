import QuantumNLS.Ext025A4HeldDependence

/-! Joint time/initial-data analyticity from the accepted GP-04 theorem.
Time is a frozen state coordinate; the enlarged analytic field is
(s,x) ↦ (0,s f(x)). Compactness is the continuous image of [0,1]. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Metric Topology
namespace QuantumNLS.JointAnalyticFlowR107
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A complete autonomous analytic flow is jointly analytic, with no
boundedness premise on arbitrary balls or uniformity over vector fields. -/
theorem joint_analytic {f : V → V} {φ : ℝ → V → V}
    (hf : AnalyticOnNhd ℝ f univ)
    (hd : ∀ x t, HasDerivAt (fun t => φ t x) (f (φ t x)) t)
    (h0 : ∀ x, φ 0 x = x) (p : ℝ × V) :
    AnalyticAt ℝ (fun q : ℝ × V => φ q.1 q.2) p := by
  let g : ℝ × V → ℝ × V := fun q => (0, q.1 • f q.2)
  let Ψ : Unit → ℝ → ℝ × V → ℝ × V := fun _ t q => (q.1, φ (q.1*t) q.2)
  have hg : AnalyticOnNhd ℝ g univ := by
    intro q _
    exact analyticAt_const.prod (analyticAt_fst.smul ((hf q.2 (mem_univ _)).comp analyticAt_snd))
  have hΨ (i : Unit) (q : ℝ × V) (t : ℝ) :
      HasDerivAt (fun t => Ψ i t q) (g (Ψ i t q)) t := by
    have hh := (hd q.2 (q.1*t)).scomp t ((hasDerivAt_id t).const_mul q.1)
    simpa only [Ψ,g,mul_one,Function.comp_def,id_eq] using
      (hasDerivAt_const t q.1).prodMk hh
  have hinit (i : Unit) (q : ℝ × V) : Ψ i 0 q = q := by simp [Ψ,h0]
  let S : Set (ℝ × V) := (fun t => Ψ () t p) '' Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.image
    (continuous_iff_continuousAt.mpr fun t => (hΨ () p t).continuousAt)
  obtain ⟨r,hr,C,h⟩ := Ext025A4HeldDependence.held (V := ℝ × V) (W := ℝ × V)
    Unit g (fun _ => ContinuousLinearMap.id ℝ (ℝ × V)) 1 Ψ S p hS
    (hg.mono (subset_univ _)) (fun _ => by simp)
    (fun i q t => hΨ i q t) hinit
    (fun _ t ht => ⟨t,ht,rfl⟩)
  obtain ⟨a,ha,_⟩ := h ()
  have ha' : AnalyticAt ℝ (Ψ () 1) p := ha.analyticAt
  have hs := analyticAt_snd.comp ha'
  simpa only [Ψ,mul_one,Function.comp_def] using hs

end QuantumNLS.JointAnalyticFlowR107
#print axioms QuantumNLS.JointAnalyticFlowR107.joint_analytic

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.JointAnalyticFlowR107." ||
        n.toString.startsWith "_private.QuantumNLS.JointAnalyticFlowR107." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R107 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
