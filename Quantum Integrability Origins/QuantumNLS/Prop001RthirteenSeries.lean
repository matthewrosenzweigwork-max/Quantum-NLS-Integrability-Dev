import QuantumNLS.Ext025A12Collision
import QuantumNLS.TraceNormTopology

/-! Source A2-infinite-collision: convergence in the existing trace norm.
The series is formed from the actual one-overlap placements and constructed
partial trace. No hierarchy equation or propagation estimate is a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace QuantumNLS.Prop001RthirteenSeries
open TraceClass TraceIdeal TensorCarrier Prop001 Ext025A12Collision
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Absolute trace bounds imply operator-norm summability. -/
theorem summable_of_trace_bound (F : ℕ → E →L[ℂ] E) (b : ℕ → ℝ)
    (hb : Summable b) (hpos : ∀ n, 0 ≤ b n)
    (hF : ∀ n, traceNorm (F n) ≤ ENNReal.ofReal (b n)) :
    Summable F := by
  apply Summable.of_norm_bounded hb
  intro n
  exact (ENNReal.ofReal_le_ofReal_iff (hpos n)).mp
    ((norm_le_traceNorm _).trans (hF n))

/-- Lower semicontinuity of the concrete trace norm passes the finite
triangle inequalities to the actual bounded-operator sum. -/
theorem traceNorm_tsum_le (F : ℕ → E →L[ℂ] E) (b : ℕ → ℝ)
    (hb : Summable b) (hpos : ∀ n, 0 ≤ b n)
    (hF : ∀ n, traceNorm (F n) ≤ ENNReal.ofReal (b n)) :
    traceNorm (∑' n, F n) ≤ ENNReal.ofReal (∑' n, b n) := by
  apply TraceNormTopology.traceNorm_le_of_tendsto (tsum_nonneg hpos)
    (summable_of_trace_bound F b hb hpos hF).hasSum
  apply Eventually.of_forall
  intro s
  calc
    traceNorm (∑ n ∈ s, F n) ≤ ∑ n ∈ s, traceNorm (F n) :=
      Fidelity.traceNorm_sum_le s F
    _ ≤ ∑ n ∈ s, ENNReal.ofReal (b n) := Finset.sum_le_sum (fun n _ => hF n)
    _ = ENNReal.ofReal (∑ n ∈ s, b n) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => hpos n)).symm
    _ ≤ ENNReal.ofReal (∑' n, b n) :=
      ENNReal.ofReal_le_ofReal (hb.sum_le_tsum s (fun n _ => hpos n))

/-- The infinite series converges in trace norm, with a literal tail bound. -/
theorem traceNorm_tail_le (F : ℕ → E →L[ℂ] E) (b : ℕ → ℝ)
    (hb : Summable b) (hpos : ∀ n, 0 ≤ b n)
    (hF : ∀ n, traceNorm (F n) ≤ ENNReal.ofReal (b n)) (m : ℕ) :
    traceNorm ((∑' n, F n) - ∑ n ∈ Finset.range m, F n) ≤
      ENNReal.ofReal (∑' n, b (n+m)) := by
  have hs := summable_of_trace_bound F b hb hpos hF
  rw [← hs.sum_add_tsum_nat_add m, add_sub_cancel_left]
  exact traceNorm_tsum_le (fun n => F (n+m)) (fun n => b (n+m))
    (summable_nat_add_iff m |>.mpr hb) (fun n => hpos (n+m)) (fun n => hF (n+m))

theorem traceNorm_series_tendsto (F : ℕ → E →L[ℂ] E) (b : ℕ → ℝ)
    (hb : Summable b) (hpos : ∀ n, 0 ≤ b n)
    (hF : ∀ n, traceNorm (F n) ≤ ENNReal.ofReal (b n)) :
    Tendsto (fun m => traceNorm ((∑' n, F n) - ∑ n ∈ Finset.range m, F n))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun m => ∑' n, b (n+m)) atTop (𝓝 0) := by
    have he (m : ℕ) : (∑' n, b (n+m)) = (∑' n, b n) - ∑ n ∈ Finset.range m, b n := by
      rw [← hb.sum_add_tsum_nat_add m, add_sub_cancel_left]
    simp_rw [he]
    have hs : Tendsto (fun _ : ℕ => ∑' n, b n) atTop (𝓝 (∑' n, b n)) := tendsto_const_nhds
    simpa only [sub_self] using hs.sub hb.hasSum.tendsto_sum_nat
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [Function.comp_def,ENNReal.ofReal_zero] using ht')
    (fun _ => bot_le) (traceNorm_tail_le F b hb hpos hF)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Hierarchy (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := ∀ k, RankOperator H k

/-- The full source collision series, at every positive output rank. -/
def collisionSeries (A : Interactions H) (Γ : Hierarchy H)
    (hΓ : ∀ k, IsTraceClass (Γ k)) (k : ℕ) : RankOperator H (k+1) :=
  ∑' n, sourceRankCollision k n (A n) (Γ ((k+1)+n)) (hΓ _)

theorem weighted_rank_summable (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3 * ‖A n‖)) :
    Summable (fun n => ((n+1 : ℕ) : ℝ)*‖A n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hcubic
  intro n
  gcongr
  have h : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  calc
    ((n+1 : ℕ) : ℝ) = ((n+1 : ℕ) : ℝ)*1*1 := by ring
    _ ≤ ((n+1 : ℕ) : ℝ)*((n+1 : ℕ) : ℝ)*((n+1 : ℕ) : ℝ) := by gcongr
    _ = _ := by ring

theorem source_collision_bound (A : Interactions H) (Γ : Hierarchy H)
    (hΓ : ∀ k, IsTraceClass (Γ k)) (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ k, traceNorm (Γ k) ≤ ENNReal.ofReal M) (k n : ℕ) :
    traceNorm (sourceRankCollision k n (A n) (Γ ((k+1)+n)) (hΓ _)) ≤
      ENNReal.ofReal ((2*((k+1 : ℕ) : ℝ)*M) * (((n+1 : ℕ) : ℝ)*‖A n‖)) := by
  refine (sourceRankCollision_bound k n (A n) _ (hΓ _)).trans ?_
  calc
    _ ≤ ENNReal.ofReal (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖A n‖)*ENNReal.ofReal M :=
      mul_le_mul_of_nonneg_left (hbound _) (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- The source series is trace class and converges in trace norm on every
uniformly trace-bounded hierarchy, including the actual hierarchies below. -/
theorem collisionSeries_converges (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3 * ‖A n‖))
    (Γ : Hierarchy H) (hΓ : ∀ k, IsTraceClass (Γ k))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ k, traceNorm (Γ k) ≤ ENNReal.ofReal M) (k : ℕ) :
    IsTraceClass (collisionSeries A Γ hΓ k) ∧
      traceNorm (collisionSeries A Γ hΓ k) ≤
        ENNReal.ofReal ((2*((k+1 : ℕ) : ℝ)*M) * ∑' n, ((n+1 : ℕ) : ℝ)*‖A n‖) ∧
      Tendsto (fun m => traceNorm (collisionSeries A Γ hΓ k - ∑ n ∈ Finset.range m,
        sourceRankCollision k n (A n) (Γ ((k+1)+n)) (hΓ _))) atTop (𝓝 0) := by
  let F := fun n => sourceRankCollision k n (A n) (Γ ((k+1)+n)) (hΓ _)
  let b := fun n => (2*((k+1 : ℕ) : ℝ)*M) * (((n+1 : ℕ) : ℝ)*‖A n‖)
  have hb : Summable b := (weighted_rank_summable A hcubic).mul_left _
  have hp : ∀ n, 0 ≤ b n := fun _ => by dsimp [b]; positivity
  have hf : ∀ n, traceNorm (F n) ≤ ENNReal.ofReal (b n) :=
    source_collision_bound A Γ hΓ M hM hbound k
  have ht := traceNorm_tsum_le F b hb hp hf
  refine ⟨lt_of_le_of_lt ht ENNReal.ofReal_lt_top, ?_,
    traceNorm_series_tendsto F b hb hp hf⟩
  simpa only [b, F, collisionSeries, tsum_mul_left] using ht

theorem coherent_isTraceClass (v : H) (hv : ‖v‖ = 1) (k : ℕ) :
    IsTraceClass (coherentProjector k v) := by
  rw [IsTraceClass, coherentProjector_traceNorm k v hv]
  exact ENNReal.one_lt_top

theorem extendedMarginal_traceNorm_le (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N : ℕ) (t : ℝ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (k : ℕ) :
    traceNorm (extendedMarginal A N k t ψ) ≤ 1 := by
  by_cases hk : k ≤ N
  · rw [extendedMarginal_of_le A N k hk, marginal_traceNorm A hA N k hk t ψ hψ]
  · rw [extendedMarginal, dite_eq_right hk, (traceNorm_eq_zero_iff _).mpr rfl]
    exact bot_le

theorem extendedMarginal_isTraceClass (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N : ℕ) (t : ℝ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (k : ℕ) :
    IsTraceClass (extendedMarginal A N k t ψ) :=
  (extendedMarginal_traceNorm_le A hA N t ψ hψ k).trans_lt ENNReal.one_lt_top

/-- Convergence on the actual product hierarchy; no product collision
identification is asserted by this summability result. -/
theorem product_collision_converges (D : ClassicalData H) (u : Sphere H) (t : ℝ) (k : ℕ) :
    let v := trajectory D u t
    let Γ := fun m => coherentProjector m v
    let ht := coherent_isTraceClass v ((trajectory_spec D u).2.2.1 t).1
    IsTraceClass (collisionSeries D.A Γ ht k) ∧
      Tendsto (fun m => traceNorm (collisionSeries D.A Γ ht k - ∑ n ∈ Finset.range m,
        sourceRankCollision k n (D.A n) (Γ ((k+1)+n)) (ht _))) atTop (𝓝 0) := by
  dsimp only
  have hv := ((trajectory_spec D u).2.2.1 t).1
  have h := collisionSeries_converges D.A D.cubic
    (fun m => coherentProjector m (trajectory D u t))
    (coherent_isTraceClass _ hv) 1 zero_le_one
    (fun m => by rw [coherentProjector_traceNorm m _ hv]; norm_num) k
  exact ⟨h.1,h.2.2⟩

theorem finite_collision_converges (D : ClassicalData H) (N : ℕ) (t : ℝ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (k : ℕ) :
    let Γ := fun m => extendedMarginal D.A N m t ψ
    let ht := extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ
    IsTraceClass (collisionSeries D.A Γ ht k) ∧
      Tendsto (fun m => traceNorm (collisionSeries D.A Γ ht k - ∑ n ∈ Finset.range m,
        sourceRankCollision k n (D.A n) (Γ ((k+1)+n)) (ht _))) atTop (𝓝 0) := by
  dsimp only
  have h := collisionSeries_converges D.A D.cubic
    (fun m => extendedMarginal D.A N m t ψ)
    (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) 1 zero_le_one
    (fun m => by simpa using extendedMarginal_traceNorm_le D.A D.selfAdjoint N t ψ hψ m) k
  exact ⟨h.1,h.2.2⟩

theorem error_collision_converges (D : ClassicalData H) (N : ℕ) (t : ℝ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (u : Sphere H) (k : ℕ) :
    let Γ := fun m => extendedMarginal D.A N m t ψ - coherentProjector m (trajectory D u t)
    let ht := fun m => Ext025A12Trace.finite_sub
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ m)
      (coherent_isTraceClass _ ((trajectory_spec D u).2.2.1 t).1 m)
    IsTraceClass (collisionSeries D.A Γ ht k) ∧
      Tendsto (fun m => traceNorm (collisionSeries D.A Γ ht k - ∑ n ∈ Finset.range m,
        sourceRankCollision k n (D.A n) (Γ ((k+1)+n)) (ht _))) atTop (𝓝 0) := by
  dsimp only
  have h := collisionSeries_converges D.A D.cubic
    (fun m => extendedMarginal D.A N m t ψ - coherentProjector m (trajectory D u t))
    (fun m => Ext025A12Trace.finite_sub
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ m)
      (coherent_isTraceClass _ ((trajectory_spec D u).2.2.1 t).1 m)) 2 (by norm_num)
    (fun m => by simpa using (extendedMarginal_error_le_two D.A D.selfAdjoint N m t ψ hψ
      (trajectory D u t) ((trajectory_spec D u).2.2.1 t).1)) k
  exact ⟨h.1,h.2.2⟩

end QuantumNLS.Prop001RthirteenSeries

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RthirteenSeries" then
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
  Lean.logInfo m!"Prop001RthirteenSeries audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

#print axioms QuantumNLS.Prop001RthirteenSeries.summable_of_trace_bound
#print axioms QuantumNLS.Prop001RthirteenSeries.traceNorm_tsum_le
#print axioms QuantumNLS.Prop001RthirteenSeries.traceNorm_tail_le
#print axioms QuantumNLS.Prop001RthirteenSeries.traceNorm_series_tendsto
#print axioms QuantumNLS.Prop001RthirteenSeries.Hierarchy
#print axioms QuantumNLS.Prop001RthirteenSeries.collisionSeries
#print axioms QuantumNLS.Prop001RthirteenSeries.weighted_rank_summable
#print axioms QuantumNLS.Prop001RthirteenSeries.source_collision_bound
#print axioms QuantumNLS.Prop001RthirteenSeries.collisionSeries_converges
#print axioms QuantumNLS.Prop001RthirteenSeries.coherent_isTraceClass
#print axioms QuantumNLS.Prop001RthirteenSeries.extendedMarginal_traceNorm_le
#print axioms QuantumNLS.Prop001RthirteenSeries.extendedMarginal_isTraceClass
#print axioms QuantumNLS.Prop001RthirteenSeries.product_collision_converges
#print axioms QuantumNLS.Prop001RthirteenSeries.finite_collision_converges
#print axioms QuantumNLS.Prop001RthirteenSeries.error_collision_converges
