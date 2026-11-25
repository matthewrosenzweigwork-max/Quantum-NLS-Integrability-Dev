import QuantumNLS.Prop001Dynamics

/-! PROP-001: construct the autonomous unit-sphere flow, its group law,
and its inverse maps from the source hypotheses and uniqueness. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
open scoped NNReal
namespace QuantumNLS.Prop001
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

structure ClassicalData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  A : Interactions H
  selfAdjoint : ∀ n, IsSelfAdjoint (A n)
  a : ℝ
  a_pos : 0 < a
  cubic : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖)
  exponential : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n))

abbrev Sphere (H : Type*) [NormedAddCommGroup H] := {u : H // ‖u‖ = 1}

def trajectory (D : ClassicalData H) (u : Sphere H) : ℝ → H :=
  (classical D.A D.selfAdjoint D.a_pos D.cubic D.exponential u.property).choose

theorem trajectory_spec (D : ClassicalData H) (u : Sphere H) :
    trajectory D u 0 = u.val ∧ ContDiff ℝ 1 (trajectory D u) ∧
      (∀ t, ‖trajectory D u t‖ = 1 ∧ HasDerivAt (trajectory D u)
        (Ext025A8.sourceHartreeField D.A (trajectory D u t)) t) ∧
      (∀ β : ℝ → H, β 0 = u.val →
        (∀ t, ‖β t‖ = 1 ∧ HasDerivAt β (Ext025A8.sourceHartreeField D.A (β t)) t) →
          β = trajectory D u) :=
  (classical D.A D.selfAdjoint D.a_pos D.cubic D.exponential u.property).choose_spec

def flow (D : ClassicalData H) (t : ℝ) (u : Sphere H) : Sphere H :=
  ⟨trajectory D u t, ((trajectory_spec D u).2.2.1 t).1⟩

theorem flow_zero (D : ClassicalData H) (u : Sphere H) : flow D 0 u = u :=
  Subtype.ext (trajectory_spec D u).1

theorem trajectory_shift (D : ClassicalData H) (u : Sphere H) (s : ℝ) :
    (fun t => trajectory D u (t + s)) = trajectory D (flow D s u) := by
  apply (trajectory_spec D (flow D s u)).2.2.2
  · simp only [zero_add, flow]
  · intro t
    refine ⟨((trajectory_spec D u).2.2.1 (t + s)).1, ?_⟩
    simpa only [one_smul, Function.comp_def, id_eq] using
      (((trajectory_spec D u).2.2.1 (t + s)).2.scomp t ((hasDerivAt_id t).add_const s))

theorem flow_add (D : ClassicalData H) (u : Sphere H) (t s : ℝ) :
    flow D t (flow D s u) = flow D (t + s) u := by
  apply Subtype.ext
  exact (congrFun (trajectory_shift D u s) t).symm

/-- Actual inverse maps on the unit sphere. Differentiability of these
maps in their initial state remains a separate GP-04 obligation. -/
def flowEquiv (D : ClassicalData H) (t : ℝ) : Sphere H ≃ Sphere H where
  toFun := flow D t
  invFun := flow D (-t)
  left_inv u := by rw [flow_add, neg_add_cancel, flow_zero]
  right_inv u := by rw [flow_add, add_neg_cancel, flow_zero]

theorem sphere_lipschitz (D : ClassicalData H) :
    ∃ K : ℝ≥0, LipschitzOnWith K (Ext025A8.sourceHartreeField D.A) {u : H | ‖u‖ = 1} := by
  let B := fun n => TensorPlacements.extendSymKernel (D.A n)
  obtain ⟨S, hS, hv, hd⟩ := Ext025A8.exponential_rank_margin D.a_pos
    (fun n => norm_nonneg (B n)) (Ext025A8.source_rank_summable D.A D.exponential)
  obtain ⟨M, K, _, hK⟩ := Ext025A8.hartreeField_ball_bounds B
    ((zero_lt_one.trans hS).le) hv hd
  refine ⟨K, hK.mono ?_⟩
  intro u hu
  rw [mem_closedBall_zero_iff, hu]
  exact hS.le

/-- A uniform quantitative initial-data estimate, for both signs of time.
The Lipschitz constant is derived from the actual source rank series. -/
theorem flow_initial_estimate (D : ClassicalData H) :
    ∃ K : ℝ≥0, ∀ (u v : Sphere H) (t : ℝ),
      dist (flow D t u) (flow D t v) ≤ dist u v * Real.exp (K * |t|) := by
  obtain ⟨K, hK⟩ := sphere_lipschitz D
  refine ⟨K, fun u v t => ?_⟩
  have hpos (α β : ℝ → H) (f : H → H)
      (hf : LipschitzOnWith K f {u : H | ‖u‖ = 1})
      (hα : ∀ s, ‖α s‖ = 1 ∧ HasDerivAt α (f (α s)) s)
      (hβ : ∀ s, ‖β s‖ = 1 ∧ HasDerivAt β (f (β s)) s)
      (b : ℝ) (hb : 0 ≤ b) :
      dist (α b) (β b) ≤ dist (α 0) (β 0) * Real.exp (K * b) := by
    have hcα : Continuous α := continuous_iff_continuousAt.mpr
      (fun s => (hα s).2.continuousAt)
    have hcβ : Continuous β := continuous_iff_continuousAt.mpr
      (fun s => (hβ s).2.continuousAt)
    have h := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => f) (s := fun _ => {u : H | ‖u‖ = 1})
      (a := 0) (b := b) (K := K)
      (fun _ _ => hf) hcα.continuousOn
      (fun s _ => (hα s).2.hasDerivWithinAt) (fun s _ => (hα s).1)
      hcβ.continuousOn (fun s _ => (hβ s).2.hasDerivWithinAt)
      (fun s _ => (hβ s).1) le_rfl b ⟨hb, le_rfl⟩
    simpa only [sub_zero] using h
  by_cases ht : 0 ≤ t
  · have h := hpos (trajectory D u) (trajectory D v) (Ext025A8.sourceHartreeField D.A)
      hK (trajectory_spec D u).2.2.1 (trajectory_spec D v).2.2.1 t ht
    simpa only [Subtype.dist_eq, flow, abs_of_nonneg ht,
      (trajectory_spec D u).1, (trajectory_spec D v).1] using h
  · have hrev (w : Sphere H) : ∀ s, ‖trajectory D w (-s)‖ = 1 ∧
        HasDerivAt (fun r => trajectory D w (-r))
          (-Ext025A8.sourceHartreeField D.A (trajectory D w (-s))) s := by
      intro s
      refine ⟨((trajectory_spec D w).2.2.1 (-s)).1, ?_⟩
      simpa only [neg_one_smul, Function.comp_def] using
        (((trajectory_spec D w).2.2.1 (-s)).2.scomp s (hasDerivAt_id s).neg)
    have h := hpos (fun s => trajectory D u (-s)) (fun s => trajectory D v (-s))
      (fun x => -Ext025A8.sourceHartreeField D.A x) hK.neg (hrev u) (hrev v)
      (-t) (by linarith)
    simpa only [Subtype.dist_eq, flow, neg_neg, neg_zero, abs_of_neg (lt_of_not_ge ht),
      (trajectory_spec D u).1, (trajectory_spec D v).1] using h

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.trajectory_spec
#print axioms QuantumNLS.Prop001.flow_zero
#print axioms QuantumNLS.Prop001.trajectory_shift
#print axioms QuantumNLS.Prop001.flow_add
#print axioms QuantumNLS.Prop001.flowEquiv
#print axioms QuantumNLS.Prop001.sphere_lipschitz
#print axioms QuantumNLS.Prop001.flow_initial_estimate
