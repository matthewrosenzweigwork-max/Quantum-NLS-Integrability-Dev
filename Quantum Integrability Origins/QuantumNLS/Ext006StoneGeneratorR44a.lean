import QuantumNLS.Ext006SelfAdjointR44a
import QuantumNLS.Ext006WeakDifferentiationR44a
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Exact strong generator domain of the constructed exponential group.
Graph limits are justified by uniform convergence of the transported
field images; no maximality or differentiability premise is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006StoneGeneratorR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006FieldClosureR42a Ext006FieldMaximalityR44a Ext006SelfAdjointR44a
open Ext006SeriesIdentificationR43a Ext006ExponentialDerivativeR43a
open WithLp

/-- Every vector in the actual closed field graph has the full strong
time derivative, with its actual closed field image, at every real time. -/
theorem graph_hasDerivAt (h : H) (x y : Fock)
    (hxy : (x,y) ∈ closedFieldGraph h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitary h s x) (Complex.I • unitary h t y) t := by
  have hc := (analytic_core_graph h x y).mpr hxy
  change toLp 2 (x,y) ∈ closure ((graphMap h).range : Set Pair) at hc
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hc
  choose v hv using hp
  have hx : Tendsto (fun n => inclusion (v n)) atTop (𝓝 x) := by
    have he := (WithLp.continuous_fst 2 Fock Fock).continuousAt.tendsto.comp ht
    simpa only [Function.comp_def,← hv,graphMap_apply,toLp_fst] using he
  have hy : Tendsto (fun n => (field h (v n).1).1) atTop (𝓝 y) := by
    have he := (WithLp.continuous_snd 2 Fock Fock).continuousAt.tendsto.comp ht
    simpa only [Function.comp_def,← hv,graphMap_apply,toLp_snd] using he
  have hu : TendstoUniformly
      (fun (n : ℕ) (s : ℝ) => Complex.I • unitary h s (field h (v n).1).1)
      (fun s : ℝ => Complex.I • unitary h s y) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hy) ε hε] with n hn
    intro s
    simpa only [dist_smul₀,Complex.norm_I,one_mul,LinearIsometryEquiv.dist_map,dist_comm] using hn
  have hf : ∀ n, ∀ s : ℝ, HasDerivAt (fun u : ℝ => unitary h u (inclusion (v n)))
      (Complex.I • unitary h s (field h (v n).1).1) s := by
    intro n s
    obtain ⟨N,hN⟩ := (v n).2
    exact unitary_hasDerivAt h (v n).1 hN s
  exact hasDerivAt_of_tendstoUniformly hu (Eventually.of_forall hf)
    (fun s => (unitary h s).continuous.continuousAt.tendsto.comp hx) t

/-- Any strong derivative at zero belongs to the adjoint graph, and hence
to the proved self-adjoint closure. -/
theorem derivative_mem_graph (h : H) (x y : Fock)
    (hx : HasDerivAt (fun t : ℝ => unitary h t x) (Complex.I • y) 0) :
    (x,y) ∈ closedFieldGraph h := by
  rw [← analytic_core_graph,closedCoreGraph_eq_weak]
  intro v
  obtain ⟨N,hN⟩ := v.2
  have hdv := (unitary_hasDerivAt h v.1 hN (-(0 : ℝ))).scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have dl := hdv.inner ℂ (hasDerivAt_const 0 x)
  have dr := (hasDerivAt_const 0 (inclusion v)).inner ℂ hx
  have he : (fun t : ℝ => inner ℂ (unitary h (-t) (inclusion v)) x) =
      (fun t : ℝ => inner ℂ (inclusion v) (unitary h t x)) := by
    funext t
    exact (evolution_adjoint h t (inclusion v) x).symm
  have de := dl.unique (he ▸ dr)
  simp only [neg_zero,unitary_zero,inner_zero_left,inner_zero_right,zero_add,add_zero,
    neg_one_smul] at de
  change inner ℂ (-(Complex.I • (field h v.1).1)) x = inner ℂ (inclusion v) (Complex.I • y) at de
  simp only [inner_neg_left,inner_smul_left,inner_smul_right,Complex.conj_I,neg_mul,neg_neg] at de
  exact mul_left_cancel₀ Complex.I_ne_zero de

/-- Stone's infinitesimal generator is precisely the self-adjoint closure
of the actual smeared field on the analytic-vector core, including its
entire domain. The sign is U(t)=exp(i t closure(phi)). -/
theorem generator_iff (h : H) (x y : Fock) :
    HasDerivAt (fun t : ℝ => unitary h t x) (Complex.I • y) 0 ↔
      (x,y) ∈ (closureField h).graph := by
  rw [closureField_graph,graph_mem_closed]
  constructor
  · exact derivative_mem_graph h x y
  · intro hxy
    simpa only [unitary_zero] using graph_hasDerivAt h x y hxy 0

end QuantumNLS.Ext006StoneGeneratorR44a
#print axioms QuantumNLS.Ext006StoneGeneratorR44a.graph_hasDerivAt
#print axioms QuantumNLS.Ext006StoneGeneratorR44a.generator_iff

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006StoneGeneratorR44a." then
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
