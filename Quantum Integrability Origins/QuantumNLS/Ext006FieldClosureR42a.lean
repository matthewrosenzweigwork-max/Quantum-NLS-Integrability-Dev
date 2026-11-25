import QuantumNLS.Ext006ReorientationR42a

/-! Analytic bridge checkpoint: the actual smeared field is symmetric on its
constructed dense smooth domain and is closable. The closed graph below is
NOT asserted self-adjoint. No field exponential is postulated. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FieldClosureR42a
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Ext006IdentityCyclicR35a Ext006ClosedFieldGraphsR36a

/-- Symmetry of the actual unbounded sum a(h)+a*(h), on its common domain. -/
theorem field_symmetric (h : H) (v w : D) :
    inner ℂ v.1 (field h w).1 = inner ℂ (field h v).1 w.1 := by
  simpa only [B,Bstar,field,add_comm] using B_adjoint h h v w

/-- Maximal ket-tested weak field graph, with the actual field on test kets. -/
def FieldGraph (h : H) (x y : Fock) : Prop :=
  ∀ m : Occ, inner ℂ (ketD m).1 y = inner ℂ (field h (ketD m)).1 x

lemma fieldGraph_smooth (h : H) (v : D) : FieldGraph h v.1 (field h v).1 :=
  fun m => field_symmetric h (ketD m) v

lemma fieldGraph_unique (h : H) {x y z : Fock}
    (hy : FieldGraph h x y) (hz : FieldGraph h x z) : y = z :=
  ket_total (fun m => (hy m).trans (hz m).symm)

lemma fieldGraph_closed (h : H) : IsClosed {z : Fock × Fock | FieldGraph h z.1 z.2} := by
  have he : {z : Fock × Fock | FieldGraph h z.1 z.2} =
      ⋂ m : Occ, {z : Fock × Fock |
        inner ℂ (ketD m).1 z.2 = inner ℂ (field h (ketD m)).1 z.1} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,FieldGraph]
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner continuous_fst))

lemma fieldGraph_limit (h : H) {I : Type*} {l : Filter I} [NeBot l]
    {x y : I → Fock} {u v : Fock}
    (hx : Tendsto x l (𝓝 u)) (hy : Tendsto y l (𝓝 v))
    (hg : ∀ᶠ i in l, FieldGraph h (x i) (y i)) : FieldGraph h u v :=
  (fieldGraph_closed h).mem_of_tendsto (hx.prodMk_nhds hy) hg

/-- Closure of the literal graph of the field on the smooth domain. -/
def closedFieldGraph (h : H) : Set (Fock × Fock) :=
  closure {z | ∃ v : D, z = (v.1,(field h v).1)}

lemma closedFieldGraph_closed (h : H) : IsClosed (closedFieldGraph h) := isClosed_closure

lemma closedFieldGraph_subset_weak (h : H) :
    closedFieldGraph h ⊆ {z | FieldGraph h z.1 z.2} := by
  apply closure_minimal ?_ (fieldGraph_closed h)
  rintro z ⟨v,rfl⟩
  exact fieldGraph_smooth h v

/-- The closure is single-valued. This is closability, not self-adjointness. -/
theorem closedFieldGraph_unique (h : H) {x y z : Fock}
    (hy : (x,y) ∈ closedFieldGraph h) (hz : (x,z) ∈ closedFieldGraph h) : y = z :=
  fieldGraph_unique h (closedFieldGraph_subset_weak h hy) (closedFieldGraph_subset_weak h hz)

/-- Equivalent strong sequential/net criterion for the ACTUAL field graph. -/
theorem field_closable (h : H) {I : Type*} {l : Filter I} [NeBot l]
    (v : I → D) {y : Fock}
    (hv : Tendsto (fun i => (v i).1) l (𝓝 0))
    (hy : Tendsto (fun i => (field h (v i)).1) l (𝓝 y)) : y = 0 := by
  have hg := fieldGraph_limit h hv hy (Filter.Eventually.of_forall (fun i => fieldGraph_smooth h (v i)))
  apply ket_total
  intro m
  simpa only [inner_zero_right] using hg m

/-- The domain is dense because it contains every occupation ket; this does
not require a boundedness premise for the field itself. -/
theorem smooth_domain_dense : DenseRange (fun v : D => v.1) := by
  intro x
  have he : (Ext006SmoothOperatorsR34a.domain : Submodule ℂ Fock).topologicalClosure = ⊤ := by
    apply top_unique
    intro y _
    apply Ext006SmoothOperatorsR34a.domain.isClosed_topologicalClosure.mem_of_tendsto
      (lp.hasSum_single (by norm_num) y)
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro m _
    have hm : (lp.single 2 m (y m) : Fock) = y m • (ketD m).1 := by
      rw [ketD,← lp.single_smul]
      simp
    rw [hm]
    exact Submodule.smul_mem _ _ (Ext006SmoothOperatorsR34a.domain.le_topologicalClosure (ketD m).2)
  have hx : x ∈ Ext006SmoothOperatorsR34a.domain.topologicalClosure := by rw [he]; trivial
  change x ∈ closure (Ext006SmoothOperatorsR34a.domain : Set Fock) at hx
  have hr : Set.range (fun v : D => v.1) = (Ext006SmoothOperatorsR34a.domain : Set Fock) := by
    ext y
    constructor
    · rintro ⟨v,rfl⟩
      exact v.2
    · intro hy
      exact ⟨⟨y,hy⟩,rfl⟩
  rw [hr]
  exact hx

end QuantumNLS.Ext006FieldClosureR42a
#print axioms QuantumNLS.Ext006FieldClosureR42a.field_symmetric
#print axioms QuantumNLS.Ext006FieldClosureR42a.closedFieldGraph_unique
#print axioms QuantumNLS.Ext006FieldClosureR42a.field_closable
#print axioms QuantumNLS.Ext006FieldClosureR42a.smooth_domain_dense

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FieldClosureR42a." then
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
  Lean.logInfo m!"Round42a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
