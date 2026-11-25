import QuantumNLS.Ext005FiniteFormR32b
import QuantumNLS.Ext005Spectral

/-! Identify the abstract energy completion with the actual square-root
domain for the physical number-moment comparison operators. The root and
its maximal domain are the frozen concrete sector multipliers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory UniformSpace
namespace QuantumNLS.Ext005MomentDomainR33b
open Ext005OperatorFormR113 Ext005FiniteFormR32b Ext005Moments Ext005Spectral
open Ext025B3PhysicalSectors BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- The actual comparison operator, with positivity and self-adjointness proved. -/
def momentPositive (j : ℕ) : PositiveOperator (Fock L) where
  op := momentOperator (L := L) j
  selfAdjoint := momentOperator_selfAdjoint (L := L) j
  lower := momentOperator_lower (L := L) j

lemma core_mem_root (j : ℕ) (v : Core (momentPositive (L := L) j)) :
    coreVal (momentPositive (L := L) j) v ∈ (momentRoot (L := L) j).domain := operator_mem_root (L := L) j v

lemma core_root_mem_root (j : ℕ) (v : Core (momentPositive (L := L) j)) :
    momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩ ∈
      (momentRoot (L := L) j).domain :=
  (root_twice_domain (L := L) j _).mpr v.property

lemma root_symmetric (j : ℕ) (x y : (momentRoot (L := L) j).domain) :
    ⟪momentRoot (L := L) j x, (y : Fock L)⟫_ℂ =
      ⟪(x : Fock L), momentRoot (L := L) j y⟫_ℂ := by
  have h := (momentRoot (L := L) j).adjoint_isFormalAdjoint
    (momentRoot_selfAdjoint (L := L) j).dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp (momentRoot_selfAdjoint (L := L) j)] at h
  exact h x y

lemma core_root_twice (j : ℕ) (v : Core (momentPositive (L := L) j)) :
    momentRoot (L := L) j
      ⟨momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩,
        core_root_mem_root (L := L) j v⟩ =
      (momentPositive (L := L) j).op v := by
  exact root_twice (L := L) j v

/-- The concrete square-root action is an isometry on the energy core. -/
lemma core_root_norm (j : ℕ) (v : Core (momentPositive (L := L) j)) :
    ‖momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩‖ = ‖v‖ := by
  have hs := root_symmetric (L := L) j
    (⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩ : (momentRoot (L := L) j).domain)
    (⟨momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩,
      core_root_mem_root (L := L) j v⟩ : (momentRoot (L := L) j).domain)
  change ⟪momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩,
      momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩⟫_ℂ =
    ⟪coreVal (momentPositive (L := L) j) v, _⟫_ℂ at hs
  rw [core_root_twice (L := L) j v] at hs
  have h : ‖momentRoot (L := L) j
      ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩‖ ^ 2 = ‖v‖ ^ 2 := by
    calc
      _ = (⟪momentRoot (L := L) j
          ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩,
        momentRoot (L := L) j
          ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩⟫_ℂ).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (⟪coreVal (momentPositive (L := L) j) v, (momentPositive (L := L) j).op v⟫_ℂ).re :=
        congrArg Complex.re hs
      _ = ‖v‖ ^ 2 := (core_norm_sq (momentPositive (L := L) j) v).symm
  nlinarith [norm_nonneg v,
    norm_nonneg (momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩)]

def coreRoot (j : ℕ) : Core (momentPositive (L := L) j) →L[ℂ] Fock L :=
  LinearMap.mkContinuous
    { toFun := fun v => momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩
      map_add' := by
        intro v w
        change momentRoot (L := L) j (⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩ +
          ⟨coreVal (momentPositive (L := L) j) w, core_mem_root (L := L) j w⟩) = _
        exact LinearPMap.map_add (momentRoot (L := L) j) _ _
      map_smul' := by
        intro c v
        change momentRoot (L := L) j (c • ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩) = _
        exact LinearPMap.map_smul (momentRoot (L := L) j) c _ }
    1 (fun v => by
      change ‖momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v,
        core_mem_root (L := L) j v⟩‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact (core_root_norm (L := L) j v).le)

/-- Extend the actual core square root to the completed energy space. -/
def completedRoot (j : ℕ) : FormDomain (momentPositive (L := L) j) →L[ℂ] Fock L :=
  (coreRoot (L := L) j).extend (Completion.toComplL : Core (momentPositive (L := L) j) →L[ℂ]
    FormDomain (momentPositive (L := L) j))

lemma completedRoot_coe (j : ℕ) (v : Core (momentPositive (L := L) j)) :
    completedRoot (L := L) j (v : FormDomain (momentPositive (L := L) j)) =
      momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩ :=
  (coreRoot (L := L) j).extend_eq Completion.denseRange_coe (Completion.isUniformInducing_coe _) v

lemma completedRoot_norm (j : ℕ) (u : FormDomain (momentPositive (L := L) j)) :
    ‖completedRoot (L := L) j u‖ = ‖u‖ := by
  refine Completion.induction_on u (isClosed_eq (by fun_prop) continuous_norm) ?_
  intro v
  rw [completedRoot_coe, Completion.norm_coe, core_root_norm]

/-- Closedness of the actual self-adjoint root identifies the extension's graph. -/
lemma completedRoot_graph (j : ℕ) (u : FormDomain (momentPositive (L := L) j)) :
    (Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u, completedRoot (L := L) j u) ∈ (momentRoot (L := L) j).graph := by
  refine Completion.induction_on u ?_ ?_
  · exact (momentRoot_selfAdjoint (L := L) j).isClosed.preimage
      ((Ext005OperatorFormR113.inclusion (momentPositive (L := L) j)).continuous.prodMk (completedRoot (L := L) j).continuous)
  · intro v
    rw [inclusion_coe, completedRoot_coe]
    exact (momentRoot (L := L) j).mem_graph ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩

lemma inclusion_mem_root (j : ℕ) (u : FormDomain (momentPositive (L := L) j)) :
    Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u ∈ (momentRoot (L := L) j).domain :=
  LinearPMap.mem_domain_of_mem_graph (completedRoot_graph (L := L) j u)

/-- Exact norm agreement, including the actual maximal square-root domain. -/
theorem completedRoot_eq (j : ℕ) (u : FormDomain (momentPositive (L := L) j)) :
    momentRoot (L := L) j ⟨Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u, inclusion_mem_root (L := L) j u⟩ =
      completedRoot (L := L) j u := by
  obtain ⟨v, hv, he⟩ := (LinearPMap.mem_graph_iff _).mp (completedRoot_graph (L := L) j u)
  have hv' : v = ⟨Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u, inclusion_mem_root (L := L) j u⟩ := Subtype.ext hv
  simpa only [hv'] using he

/-- The form-domain range is exactly D(((Num+1)^j)^(1/2)), for the concrete
spectral multiplier, with no root-domain correspondence supplied as input. -/
theorem moment_form_domain_iff (j : ℕ) (x : Fock L) :
    (∃ u : FormDomain (momentPositive (L := L) j), Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u = x) ↔
      x ∈ momentDomain (L := L) j := by
  constructor
  · rintro ⟨u, rfl⟩
    exact inclusion_mem_root (L := L) j u
  · intro hx
    change x ∈ (momentRoot (L := L) j).domain at hx
    apply (form_domain_iff_finite (momentPositive (L := L) j) x).mpr
    refine ⟨‖momentRoot (L := L) j ⟨x, hx⟩‖, norm_nonneg _, fun v => ?_⟩
    have hs := root_symmetric (L := L) j
      (⟨x, hx⟩ : (momentRoot (L := L) j).domain)
      (⟨momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩,
        core_root_mem_root (L := L) j v⟩ : (momentRoot (L := L) j).domain)
    change ⟪momentRoot (L := L) j ⟨x, hx⟩,
      momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩⟫_ℂ =
        ⟪x, _⟫_ℂ at hs
    rw [core_root_twice (L := L) j v] at hs
    rw [← hs]
    simpa only [core_root_norm] using norm_inner_le_norm
      (momentRoot (L := L) j ⟨x, hx⟩)
      (momentRoot (L := L) j ⟨coreVal (momentPositive (L := L) j) v, core_mem_root (L := L) j v⟩)

theorem moment_form_norm_sq (j : ℕ) (u : FormDomain (momentPositive (L := L) j)) :
    ‖u‖ ^ 2 = ∑' N, momentWeight j N * ‖Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u N‖ ^ 2 := by
  rw [← completedRoot_norm (L := L) j u, ← completedRoot_eq (L := L) j u]
  exact momentRoot_norm_sq (L := L) j ⟨Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u, inclusion_mem_root (L := L) j u⟩

end QuantumNLS.Ext005MomentDomainR33b
#print axioms QuantumNLS.Ext005MomentDomainR33b.moment_form_domain_iff
#print axioms QuantumNLS.Ext005MomentDomainR33b.moment_form_norm_sq

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005MomentDomainR33b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005MomentDomainR33b." then
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
  Lean.logInfo m!"R33b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
