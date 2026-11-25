import QuantumNLS.Ext006SeriesIdentificationR43a

/-! The literal exponential sums lie in the CLOSED graph of the actual
field. This is graph identification on entire vectors, without assuming
essential self-adjointness of the closure. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ExponentialGraphR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006ExponentialInnerR43a Ext006FieldClosureR42a
open Ext006BoundedExponentialR43a Ext006SeriesIdentificationR43a

/-- Finite partial sums remain in the actual invariant smooth domain. -/
def partialSum (h : H) (t : ℝ) (v : D) (s : Finset ℕ) : D :=
  ∑ n ∈ s, ((Complex.I*(t : ℂ))^n/(n.factorial : ℂ)) • ((field h)^n) v

lemma partial_val (h : H) (t : ℝ) (v : D) (s : Finset ℕ) :
    (partialSum h t v s).1 = ∑ n ∈ s, exponentialTerm h t v n := by
  simp only [partialSum,Submodule.coe_sum,Submodule.coe_smul,exponentialTerm]

lemma power_field (h : H) (v : D) (n : ℕ) :
    field h (((field h)^n) v) = ((field h)^n) (field h v) := by
  have he := congrArg (fun T : Module.End ℂ D => T v)
    ((pow_succ' (field h) n).symm.trans (pow_succ (field h) n))
  exact he

lemma partial_field (h : H) (t : ℝ) (v : D) (s : Finset ℕ) :
    (field h (partialSum h t v s)).1 = ∑ n ∈ s, exponentialTerm h t (field h v) n := by
  simp only [partialSum,map_sum,map_smul,power_field,Submodule.coe_sum,
    Submodule.coe_smul,exponentialTerm]

/-- Convergence of the vector series and the field-image series puts the
sum in the actual closed graph. No maximal-domain equality is assumed. -/
theorem exponential_in_closed_graph (h : H) (t : ℝ) (v : D)
    (hv : Summable (exponentialTerm h t v))
    (hf : Summable (exponentialTerm h t (field h v))) :
    (exponential h t v,exponential h t (field h v)) ∈ closedFieldGraph h := by
  have hx : Tendsto (fun s : Finset ℕ => (partialSum h t v s).1) atTop (𝓝 (exponential h t v)) := by
    simpa only [HasSum,SummationFilter.unconditional,partial_val,exponential] using hv.hasSum
  have hy : Tendsto (fun s : Finset ℕ => (field h (partialSum h t v s)).1) atTop
      (𝓝 (exponential h t (field h v))) := by
    simpa only [HasSum,SummationFilter.unconditional,partial_field,exponential] using hf.hasSum
  apply (closedFieldGraph_closed h).mem_of_tendsto (hx.prodMk_nhds hy)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  exact ⟨partialSum h t v s,rfl⟩

/-- All bounded-particle vectors yield closed-graph solutions at all times. -/
theorem bounded_particle_closed_graph {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) :
    (exponential h t v,exponential h t (field h v)) ∈ closedFieldGraph h :=
  exponential_in_closed_graph h t v (entire_summable h t v hv)
    (entire_summable h t (field h v) (field_particleBound h v hv))

/-- The bounded unitary preserves the actual closed field graph on the
constructed entire core; maximality of this graph is not assumed. -/
theorem unitary_in_closed_graph {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) :
    (unitary h t v.1,unitary h t (field h v).1) ∈ closedFieldGraph h := by
  rw [unitary_series h t v (entire_summable h t v hv),
    unitary_series h t (field h v) (entire_summable h t (field h v) (field_particleBound h v hv))]
  exact bounded_particle_closed_graph h t v hv

end QuantumNLS.Ext006ExponentialGraphR43a
#print axioms QuantumNLS.Ext006ExponentialGraphR43a.exponential_in_closed_graph
#print axioms QuantumNLS.Ext006ExponentialGraphR43a.bounded_particle_closed_graph
#print axioms QuantumNLS.Ext006ExponentialGraphR43a.unitary_in_closed_graph

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ExponentialGraphR43a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round43a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
