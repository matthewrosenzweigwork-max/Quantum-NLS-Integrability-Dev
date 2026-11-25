import QuantumNLS.Ext025B9Bridges

/-! R-2E4C2F4E, source-text/chapters/foundations/A06.tex:18–112.
Consumer-node assembly at the unconditional physical Bethe basis (UBB1).
A common-domain vector is represented by its unique closed graph lift;
the inclusion is injective and has exactly the printed intersection as range.
All real symbols are finite-valued, with no boundedness requirement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology Function MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.A06Domains
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels BoundedBetheTransfer
open Ext025B6GraphCore Ext025B9JointGraph Ext025B7JointResolution
variable {L : ℝ} [Fact (0 < L)] {N d : ℕ}

/-- The accepted, complete, normalized physical Bethe basis, for every c > 0. -/
abbrev bethe (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :=
  UnconditionalBetheBasis.physicalBasis L N hN c hc

/-- Finite linear combinations, in the constructed complete common graph carrier. -/
def finiteCombinations (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    Set (graphSpace b a) := {v | inclusion b a v ∈ Submodule.span ℂ (Set.range b)}

theorem finite_projection_mem (b : BetheBasis L N) (F : Finset (MArr N)) (x : HN L N) :
    projection b (F : Set (MArr N)) x ∈ Submodule.span ℂ (Set.range b) := by
  rw [projection_finite_sum]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨m,rfl⟩)

/-- Actual finite Bethe combinations are dense in the common graph Hilbert norm. -/
theorem common_core_dense (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    Dense (finiteCombinations b a) := by
  intro v
  obtain ⟨x,hx,rfl⟩ : ∃ x, ∃ hx : ∀ j, x ∈ (multiplier b (a j)).domain,
      lift b a x hx = v := by
    let x := inclusion b a v
    have hx := (inclusion_range b a ▸ (show x ∈ Set.range (inclusion b a) from ⟨v,rfl⟩))
    exact ⟨x,hx,inclusion_injective b a (inclusion_lift b a x hx)⟩
  exact mem_closure_of_tendsto (finite_core b a x hx) (.of_forall fun F =>
    finite_projection_mem b F x)

/-- A singleton family gives the individual operator core, including convergence
of both the input and the operator value in the ambient product norm. -/
theorem individual_core (b : BetheBasis L N) (a : MArr N → ℝ)
    (x : HN L N) (hx : x ∈ (multiplier b a).domain) :
    Tendsto (fun F : Finset (MArr N) =>
      (projection b (F : Set (MArr N)) x,
       multiplier b a ⟨projection b (F : Set (MArr N)) x,
         projection_mem b a (F : Set (MArr N)) x hx⟩)) atTop
      (𝓝 (x,multiplier b a ⟨x,hx⟩)) := by
  have h := ((pairMap (L := L) (N := N) (0 : Fin 1)).continuous.comp
    (graphSpace b (fun _ : Fin 1 => a)).subtypeL.continuous).continuousAt.tendsto.comp
      (finite_core b (fun _ : Fin 1 => a) x (fun _ => hx))
  exact h

/-- Literal printed theorem, assembled without a supplied completeness,
selfadjointness, conjugacy, core or spectral-resolution assumption. -/
structure Statement (b : BetheBasis L N) : Prop where
  domain_exact : ∀ a x, x ∈ (multiplier b a).domain ↔
    Summable (fun m => |a m|^2 * ‖⟪b m,x⟫_ℂ‖^2)
  series : ∀ a (x : (multiplier b a).domain),
    HasSum (fun m => ((a m : ℂ)*⟪b m,(x : HN L N)⟫_ℂ) • b m) (multiplier b a x)
  dense_domain : ∀ a, Dense ((multiplier b a).domain : Set (HN L N))
  selfadjoint : ∀ a, IsSelfAdjoint (multiplier b a)
  occupation_domain : ∀ a x, fockTransform b x ∈ (Ext025B9Occupation.occupationOperator a).domain ↔
    x ∈ (multiplier b a).domain
  occupation_value : ∀ a x (hx : x ∈ (multiplier b a).domain),
    Ext025B9Occupation.occupationOperator a
      ⟨fockTransform b x,(Ext025B9Occupation.domain_iff b a x).mpr hx⟩ =
      fockTransform b (multiplier b a ⟨x,hx⟩)
  common_domain : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) x,
    (∀ j, x ∈ (multiplier b (a j)).domain) ↔
      Summable (fun m => (1+∑ j, |a j m|^2)*‖⟪b m,x⟫_ℂ‖^2)
  hilbert_complete : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ),
    IsComplete (graphSpace b a : Set (GraphAmbient L N d))
  inclusion_one_to_one : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ), Injective (inclusion b a)
  inclusion_exact : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ),
    Set.range (inclusion b a) = {x | ∀ j, x ∈ (multiplier b (a j)).domain}
  graph_norm : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) x
    (hx : ∀ j, x ∈ (multiplier b (a j)).domain),
    ‖lift b a x hx‖^2 = ‖x‖^2+∑ j, ‖multiplier b (a j) ⟨x,hx j⟩‖^2
  graph_parseval : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) x
    (hx : ∀ j, x ∈ (multiplier b (a j)).domain),
    ‖lift b a x hx‖^2 = ∑' m, (1+∑ j, |a j m|^2)*‖⟪b m,x⟫_ℂ‖^2
  common_core : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ), Dense (finiteCombinations b a)
  operator_core : ∀ a x (hx : x ∈ (multiplier b a).domain),
    Tendsto (fun F : Finset (MArr N) => (projection b (F : Set (MArr N)) x,
      multiplier b a ⟨projection b (F : Set (MArr N)) x,
        projection_mem b a (F : Set (MArr N)) x hx⟩)) atTop
      (𝓝 (x,multiplier b a ⟨x,hx⟩))
  strong_commutation : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ)
    (j k : Fin d) (B C : Set ℝ),
    Commute ((BetheChargeResolution.resolution b (a j)).toFun B)
      ((BetheChargeResolution.resolution b (a k)).toFun C)
  pvm_total : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ), jointProjection b a Set.univ = 1
  pvm_inter : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) B C,
    jointProjection b a B * jointProjection b a C = jointProjection b a (B ∩ C)
  pvm_orthogonal : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) B,
    (jointProjection b a B).adjoint = jointProjection b a B
  pvm_additive : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) (B : ℕ → Set (Fin d → ℝ)),
    Pairwise (Disjoint on B) → ∀ x,
    HasSum (fun n => jointProjection b a (B n) x) (jointProjection b a (⋃ n, B n) x)
  pvm_series : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) B x,
    HasSum (fun m : tuple a ⁻¹' B => b.repr x m • b m) (jointProjection b a B x)
  scalar_measure : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) x B,
    jointMeasure b a x B = ENNReal.ofReal (‖jointProjection b a B x‖^2)
  coordinate_projection : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) (j : Fin d) C,
    jointProjection b a {t | t j ∈ C} = (BetheChargeResolution.resolution b (a j)).toFun C
  coordinate_domain : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) (j : Fin d) x,
    x ∈ (multiplier b (a j)).domain ↔
      (∫⁻ t, ENNReal.ofReal (|t j|^2) ∂jointMeasure b a x) ≠ ⊤
  coordinate_cutoff : ∀ (d : ℕ) (a : Fin d → MArr N → ℝ) (j : Fin d) x
    (hx : x ∈ (multiplier b (a j)).domain),
    Tendsto (fun n => Ext025B6SpectralLimits.boundedCutoff b (a j) n x) atTop
      (𝓝 (multiplier b (a j) ⟨x,hx⟩))

/-- Full R-2E4C2F4E on any specified complete Bethe basis. -/
theorem domains (b : BetheBasis L N) : Statement b where
  domain_exact := mem_domain b
  series := multiplier_expansion b
  dense_domain := fun a => by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]; exact domain_dense b a
  selfadjoint := BetheChargeResolution.multiplier_selfAdjoint b
  occupation_domain := Ext025B9Occupation.domain_iff b
  occupation_value := Ext025B9Occupation.conjugacy b
  common_domain := fun d a x => by
    have h := (summable_density_iff b a x).symm
    change (∀ j, x ∈ (multiplier b (a j)).domain) ↔
      Summable (fun m => density b a x m) at h
    simpa only [density_eq,HilbertBasis.repr_apply_apply] using h
  hilbert_complete := fun _ a => (graphSpace_closed b a).isComplete
  inclusion_one_to_one := fun _ => inclusion_injective b
  inclusion_exact := fun _ => inclusion_range b
  graph_norm := fun _ => norm_sq b
  graph_parseval := fun _ a x hx => by
    simpa only [HilbertBasis.repr_apply_apply] using norm_sq_density b a x hx
  common_core := fun _ => common_core_dense b
  operator_core := individual_core b
  strong_commutation := fun _ => Ext025B7JointResolution.strong_commutation b
  pvm_total := fun _ => jointProjection_univ b
  pvm_inter := fun _ => jointProjection_inter b
  pvm_orthogonal := fun _ => jointProjection_adjoint b
  pvm_additive := fun _ => jointProjection_additive b
  pvm_series := fun _ a B x => BetheChargeResolution.projection_hasSum b (tuple a ⁻¹' B) x
  scalar_measure := fun _ => jointMeasure_apply b
  coordinate_projection := fun _ => Ext025B7JointResolution.coordinate_projection b
  coordinate_domain := fun _ a j x => joint_domain_iff b a (fun t => t j) x
  coordinate_cutoff := fun _ a j x hx => Ext025B6SpectralLimits.cutoff_strong b (a j) x hx

/-- The literal consumer-node theorem at UBB1 / R-8E4D05E7, all N ≥ 1,
L > 0 and c > 0. No abstract-continuity or completeness premise. -/
theorem R_2E4C2F4E (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N)
    (c : ℝ) (hc : 0 < c) : Statement (bethe L N hN c hc) := domains _

end QuantumNLS.A06Domains

#print axioms QuantumNLS.A06Domains.R_2E4C2F4E
#print axioms QuantumNLS.A06Domains.common_core_dense
#print axioms QuantumNLS.A06Domains.individual_core
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.A06Domains" then
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
  Lean.logInfo m!"A06Domains audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
