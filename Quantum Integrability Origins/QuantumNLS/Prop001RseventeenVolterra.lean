import QuantumNLS.Prop001RseventeenContinuity
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RseventeenVolterra
open TraceClass TraceIdeal TensorCarrier Prop001 Prop001RthirteenSeries
  Ext025A12Trace Ext025A12Collision Prop001RfourteenTraceRegrouping
  Prop001RseventeenDuhamel Prop001RseventeenContinuity Prop001RsixteenDuhamel
  Prop001RfifteenRemainder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem splitTrace_sub (k n : ℕ) (S T : RankOperator H (k+n))
    (hS : IsTraceClass S) (hT : IsTraceClass T) :
    splitTrace k n (S-T) (finite_sub hS hT) = splitTrace k n S hS-splitTrace k n T hT := by
  have he : (⟨S-T,finite_sub hS hT⟩ : traceIdeal _) = ⟨S,hS⟩-⟨T,hT⟩ := rfl
  change (splitMap k n ⟨S-T,finite_sub hS hT⟩).val = _
  rw [he,map_sub]
  rfl

theorem sourceRankCollision_sub (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (S T : RankOperator H ((k+1)+n)) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    sourceRankCollision k n A (S-T) (finite_sub hS hT) =
      sourceRankCollision k n A S hS-sourceRankCollision k n A T hT := by
  have he (B : RankOperator H ((k+1)+n)) : B*(S-T)-(S-T)*B = (B*S-S*B)-(B*T-T*B) := by
    simp only [mul_sub,sub_mul]
    abel
  have hi (B : RankOperator H ((k+1)+n)) :
      splitTrace (k+1) n (B*(S-T)-(S-T)*B) (commutator_finite B (S-T) (finite_sub hS hT)) =
        splitTrace (k+1) n (B*S-S*B) (commutator_finite B S hS)-
          splitTrace (k+1) n (B*T-T*B) (commutator_finite B T hT) := by
    simpa only [he] using splitTrace_sub (k+1) n (B*S-S*B) (B*T-T*B)
      (commutator_finite B S hS) (commutator_finite B T hT)
  simp only [sourceRankCollision,rankCollision,hi,Finset.sum_sub_distrib,smul_sub]

/-- The nonnegative scalar collision sum on the actual error hierarchy. -/
def collisionMajorant (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n,(2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*error D N ψ u ((k+1)+n) t

def scalarBound (D : ClassicalData H) (k n : ℕ) : ℝ :=
  (4*((k+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)*‖D.A n‖)

theorem scalarBound_summable (D : ClassicalData H) (k : ℕ) :
    Summable (scalarBound D k) := (weighted_rank_summable D.A D.cubic).mul_left _

theorem collision_scalar_term_bound (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (k n : ℕ) (t : ℝ) :
    ‖(2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*error D N ψ u ((k+1)+n) t‖ ≤
      scalarBound D k n := by
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (error_nonneg D N ψ u _ t))]
  calc
    _ ≤ (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*2 :=
      mul_le_mul_of_nonneg_left (error_le_two D N ψ hψ u _ t) (by positivity)
    _ = _ := by unfold scalarBound;ring

theorem collisionMajorant_continuous (D : ClassicalData H) (N : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ) :
    Continuous (collisionMajorant D N ψ u k) := by
  apply continuous_tsum (fun n => continuous_const.mul (error_continuous D N ψ hψ u _))
    (scalarBound_summable D k)
  exact collision_scalar_term_bound D N ψ hψ u k

theorem collisionMajorant_integrable (D : ClassicalData H) (N : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (collisionMajorant D N ψ u k) volume a b :=
  (collisionMajorant_continuous D N ψ hψ u k).intervalIntegrable a b

theorem collision_terms_summable (D : ClassicalData H) (Γ : Hierarchy H)
    (hΓ : ∀ j,IsTraceClass (Γ j)) (hbound : ∀ j,traceNorm (Γ j) ≤ 1) (k : ℕ) :
    Summable (fun n => sourceRankCollision k n (D.A n) (Γ ((k+1)+n)) (hΓ _)) := by
  apply summable_of_trace_bound _
    (fun n => (2*((k+1 : ℕ) : ℝ)*1)*(((n+1 : ℕ) : ℝ)*‖D.A n‖))
    ((weighted_rank_summable D.A D.cubic).mul_left _) (fun _ => by positivity)
  exact source_collision_bound D.A Γ hΓ 1 zero_le_one
    (fun j => by simpa only [ENNReal.ofReal_one] using hbound j) k

/-- Linearity of the actual convergent collision series on trace-one bounded hierarchies. -/
theorem collisionSeries_sub (D : ClassicalData H) (Γ Λ : Hierarchy H)
    (hΓ : ∀ j,IsTraceClass (Γ j)) (hΛ : ∀ j,IsTraceClass (Λ j))
    (hboundΓ : ∀ j,traceNorm (Γ j) ≤ 1) (hboundΛ : ∀ j,traceNorm (Λ j) ≤ 1) (k : ℕ) :
    collisionSeries D.A (fun j => Γ j-Λ j) (fun j => finite_sub (hΓ j) (hΛ j)) k =
      collisionSeries D.A Γ hΓ k-collisionSeries D.A Λ hΛ k := by
  unfold collisionSeries
  rw [← (collision_terms_summable D Γ hΓ hboundΓ k).tsum_sub
    (collision_terms_summable D Λ hΛ hboundΛ k)]
  exact tsum_congr (fun n => sourceRankCollision_sub k n (D.A n) _ _ (hΓ _) (hΛ _))

theorem traceNorm_error_eq (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (j : ℕ) (t : ℝ) :
    traceNorm (extendedMarginal D.A N j t ψ-coherentProjector j (trajectory D u t)) =
      ENNReal.ofReal (error D N ψ u j t) := by
  exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (extendedMarginal_error_le_two D.A D.selfAdjoint N j t ψ hψ
      (trajectory D u t) ((trajectory_spec D u).2.2.1 t).1))).symm

/-- The exact scalar collision majorant bounds the actual collision of the error. -/
theorem error_collision_bound (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ) (t : ℝ) :
    traceNorm (collisionSeries D.A
      (fun j => extendedMarginal D.A N j t ψ-coherentProjector j (trajectory D u t))
      (fun j => finite_sub (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ j)
        (coherent_isTraceClass _ ((trajectory_spec D u).2.2.1 t).1 j)) k) ≤
      ENNReal.ofReal (collisionMajorant D N ψ u k t) := by
  apply traceNorm_tsum_le _
    (fun n => (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*error D N ψ u ((k+1)+n) t)
    (Summable.of_norm_bounded (scalarBound_summable D k)
      (fun n => collision_scalar_term_bound D N ψ hψ u k n t))
    (fun n => mul_nonneg (by positivity) (error_nonneg D N ψ u _ t))
  intro n
  exact (sourceRankCollision_bound k n (D.A n) _ _).trans_eq (by
    rw [traceNorm_error_eq D N ψ hψ u _ t,← ENNReal.ofReal_mul (by positivity)])

theorem error_velocity_bound (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (u : Sphere H) (t : ℝ) :
    traceNorm (finiteVelocity D k m ψ hψ t-productVelocity D u k t) ≤
      ENNReal.ofReal (collisionMajorant D ((k+1)+m) ψ u k t+
        errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)) := by
  have hi := collisionSeries_sub D
    (fun j => extendedMarginal D.A ((k+1)+m) j t ψ)
    (fun j => coherentProjector j (trajectory D u t))
    (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ)
    (coherent_isTraceClass _ ((trajectory_spec D u).2.2.1 t).1)
    (extendedMarginal_traceNorm_le D.A D.selfAdjoint ((k+1)+m) t ψ hψ)
    (fun j => by rw [coherentProjector_traceNorm j _ ((trajectory_spec D u).2.2.1 t).1]) k
  unfold finiteVelocity productVelocity
  rw [← smul_sub]
  have he (B C R : RankOperator H (k+1)) : (B+R)-C=(B-C)+R := by abel
  rw [he,← hi,traceNorm_smul]
  simp only [norm_neg,Complex.norm_I,ENNReal.ofReal_one,one_mul]
  refine (traceNorm_add_le _ _).trans ((add_le_add
    (error_collision_bound D ((k+1)+m) ψ hψ u k t)
    (Prop001RsixteenSeries.finiteCorrection_bound_positive D k m ψ hψ t)).trans_eq ?_)
  exact (ENNReal.ofReal_add (tsum_nonneg (fun n => mul_nonneg (by positivity)
    (error_nonneg D _ ψ u _ t)))
    (div_nonneg (mul_nonneg (errorSum_nonneg D.A) (sq_nonneg _)) (by positivity))).symm

/-- The actual scalar one-step inequality; all measurability and integrability
needed for its integral have been proved above. -/
theorem error_Volterra (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (u : Sphere H)
    {a b : ℝ} (hab : a ≤ b) :
    error D ((k+1)+m) ψ u (k+1) b ≤ error D ((k+1)+m) ψ u (k+1) a+
      ∫ t in a..b, (collisionMajorant D ((k+1)+m) ψ u k t+
        errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)) := by
  let F := fun t => extendedMarginal D.A ((k+1)+m) (k+1) t ψ-
    coherentProjector (k+1) (trajectory D u t)
  let V := fun t => finiteVelocity D k m ψ hψ t-productVelocity D u k t
  let g := fun t => collisionMajorant D ((k+1)+m) ψ u k t+
    errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)
  have hg : Continuous g := (collisionMajorant_continuous D _ ψ hψ u k).add continuous_const
  have hp (t : ℝ) : 0 ≤ g t := add_nonneg
    (tsum_nonneg (fun n => mul_nonneg (by positivity) (error_nonneg D _ ψ u _ t)))
    (div_nonneg (mul_nonneg (errorSum_nonneg D.A) (sq_nonneg _)) (by positivity))
  have hD : F b-F a = ∫ t in a..b,V t := by
    dsimp only [F,V]
    rw [intervalIntegral.integral_sub (finiteVelocity_integrable D k m ψ hψ a b)
      (productVelocity_integrable D u k a b),← finite_marginal_Duhamel D k m ψ hψ a b,
      ← product_Duhamel D u k a b]
    simp only [extendedMarginal_of_le D.A ((k+1)+m) (k+1) (by omega)]
    abel
  rw [intervalIntegral.integral_of_le hab] at hD
  have h := traceNorm_integral_le (volume.restrict (Set.Ioc a b)) V g
    ((finiteVelocity_integrable D k m ψ hψ a b).sub (productVelocity_integrable D u k a b)).1
    (hg.intervalIntegrable a b).1 (Filter.Eventually.of_forall hp)
    (Filter.Eventually.of_forall (fun t => error_velocity_bound D k m ψ hψ u t))
  rw [← hD,← intervalIntegral.integral_of_le hab] at h
  have hi : 0 ≤ ∫ t in a..b,g t := intervalIntegral.integral_nonneg hab (fun t _ => hp t)
  have he : F a+(F b-F a)=F b := by abel
  have htri := traceNorm_add_le (F a) (F b-F a)
  rw [he] at htri
  have hfa : traceNorm (F a) = ENNReal.ofReal (error D ((k+1)+m) ψ u (k+1) a) :=
    traceNorm_error_eq D _ ψ hψ u _ a
  have hfb : traceNorm (F b) = ENNReal.ofReal (error D ((k+1)+m) ψ u (k+1) b) :=
    traceNorm_error_eq D _ ψ hψ u _ b
  have htotal := htri.trans (add_le_add (le_refl (traceNorm (F a))) h)
  rw [hfa,hfb,← ENNReal.ofReal_add (error_nonneg D _ ψ u _ a) hi] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (error_nonneg D _ ψ u _ a) hi)).mp htotal

/-- Above N the scalar error is exactly one, by the source zero convention. -/
theorem error_above (D : ClassicalData H) (N j : ℕ) (hj : N < j)
    (ψ : SymSector ℂ H N) (u : Sphere H) (t : ℝ) : error D N ψ u j t = 1 := by
  unfold error
  rw [extendedMarginal_of_gt D.A N j hj,zero_sub,TraceNormTopology.traceNorm_neg,
    coherentProjector_traceNorm j _ ((trajectory_spec D u).2.2.1 t).1,ENNReal.toReal_one]

/-- One-step scalar estimate at every positive rank, with the above-N boundary
proved directly, ready for unbounded interaction-rank substitutions. -/
theorem error_Volterra_all (D : ClassicalData H) (N k : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H)
    {a b : ℝ} (hab : a ≤ b) :
    error D N ψ u (k+1) b ≤ error D N ψ u (k+1) a+
      ∫ t in a..b, (collisionMajorant D N ψ u k t+errorSum D.A*((k+1 : ℕ) : ℝ)^2/N) := by
  by_cases hk : k+1 ≤ N
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hk
    simpa only [Nat.cast_add,Nat.cast_one] using error_Volterra D k m ψ hψ u hab
  · rw [error_above D N (k+1) (by omega) ψ u b,error_above D N (k+1) (by omega) ψ u a]
    apply le_add_of_nonneg_right
    apply intervalIntegral.integral_nonneg hab
    intro t _
    exact add_nonneg (tsum_nonneg (fun n => mul_nonneg (by positivity)
      (error_nonneg D N ψ u _ t)))
      (div_nonneg (mul_nonneg (errorSum_nonneg D.A) (sq_nonneg _)) (by positivity))

end QuantumNLS.Prop001RseventeenVolterra

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RseventeenVolterra" then
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
  Lean.logInfo m!"Prop001RseventeenVolterra audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."





#print axioms QuantumNLS.Prop001RseventeenVolterra.splitTrace_sub
#print axioms QuantumNLS.Prop001RseventeenVolterra.sourceRankCollision_sub
#print axioms QuantumNLS.Prop001RseventeenVolterra.collisionMajorant
#print axioms QuantumNLS.Prop001RseventeenVolterra.scalarBound
#print axioms QuantumNLS.Prop001RseventeenVolterra.scalarBound_summable
#print axioms QuantumNLS.Prop001RseventeenVolterra.collision_scalar_term_bound
#print axioms QuantumNLS.Prop001RseventeenVolterra.collisionMajorant_continuous
#print axioms QuantumNLS.Prop001RseventeenVolterra.collisionMajorant_integrable

#print axioms QuantumNLS.Prop001RseventeenVolterra.collision_terms_summable

#print axioms QuantumNLS.Prop001RseventeenVolterra.collisionSeries_sub

#print axioms QuantumNLS.Prop001RseventeenVolterra.traceNorm_error_eq

#print axioms QuantumNLS.Prop001RseventeenVolterra.error_collision_bound

#print axioms QuantumNLS.Prop001RseventeenVolterra.error_velocity_bound
#print axioms QuantumNLS.Prop001RseventeenVolterra.error_Volterra

#print axioms QuantumNLS.Prop001RseventeenVolterra.error_above
#print axioms QuantumNLS.Prop001RseventeenVolterra.error_Volterra_all
