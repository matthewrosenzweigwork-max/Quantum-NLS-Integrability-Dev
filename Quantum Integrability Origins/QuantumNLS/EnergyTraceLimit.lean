import QuantumNLS.EnergyTracePassage

/-! Uniform gentle-limit assembly, with the source order: fix a spectral
window using compactness, then send the sequence index to infinity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.EnergyTraceLimit
open TraceClass TraceIdeal BetheChargeResolution Ext025B6PVM
open Ext025B7SpectralCompression Ext025B7GentleCompression EnergyTracePassage
variable {E ι T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem rankOne_conjugate (X : E →L[ℂ] E) (g : E) :
    X*InnerProductSpace.rankOne ℂ g g*X.adjoint =
      InnerProductSpace.rankOne ℂ (X g) (X g) := by
  ext x
  simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul,
    ContinuousLinearMap.adjoint_inner_right]

theorem rankOne_tail (P : ProjectionMeasure E) (s : Set ℝ) (hs : MeasurableSet s) (g : E) :
    tail (P.toFun s) (InnerProductSpace.rankOne ℂ g g) = ‖g-P.toFun s g‖^2 := by
  have hq : (1-P.toFun s).adjoint = 1-P.toFun s := by
    simp only [map_sub,ContinuousLinearMap.adjoint_one,P.selfAdjoint s hs]
  have hc := rankOne_conjugate (1-P.toFun s) g
  simp only [hq] at hc
  unfold tail total
  rw [hc,Fidelity.posTrace_rankOne_self,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

/-- Uniform complementary traces of the limiting pure sandwich, on the
actual compact image of the form vectors. -/
theorem compact_tails (P : ProjectionMeasure E) (hpos : P.toFun (Set.Ici 1) = 1)
    (g : T → E) (hg : IsCompact (Set.range g)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ t,
      tail (P.toFun (Set.Icc 1 (m : ℝ))) (InnerProductSpace.rankOne ℂ (g t) (g t)) ≤ ε := by
  have hu := exhaustion_uniform_compact P (fun n : ℕ => Set.Iic (n : ℝ))
    (fun _ => measurableSet_Iic)
    (fun i j hij => Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hij))
    (show (⋃ n : ℕ, Set.Iic (n : ℝ)) = Set.univ by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨n,hn⟩ := exists_nat_ge x
      exact Set.mem_iUnion.mpr ⟨n,hn⟩) (Set.range g) hg
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu (Real.sqrt ε) (Real.sqrt_pos.mpr hε)] with m hm
  intro t
  rw [rankOne_tail P _ measurableSet_Icc,positive_windows_eq P hpos]
  have hh := hm ⟨g t,Set.mem_range_self t⟩
  change dist (g t) (P.toFun (Set.Iic (m : ℝ)) (g t)) < Real.sqrt ε at hh
  rw [dist_eq_norm] at hh
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg ε)).mpr hh.le).trans_eq
    (Real.sq_sqrt hε.le)


/-- Scalar choice used for both gentle errors. -/
theorem gentle_small (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (u d : ℝ) (_hu : 0 ≤ u) (hd : 0 ≤ d) (hub : u ≤ C)
    (hdb : d ≤ (ε/(6*(C+1)))^2) : 2*Real.sqrt (u*d) ≤ ε/3 := by
  have hden : 0 < 6*(C+1) := by positivity
  have ha : 0 < ε/(6*(C+1)) := div_pos hε hden
  have hs : Real.sqrt C ≤ C+1 := by
    nlinarith only [Real.sq_sqrt hC,Real.sqrt_nonneg C,sq_nonneg (Real.sqrt C-1)]
  have he := div_mul_cancel₀ ε (ne_of_gt hden)
  calc
    _ ≤ 2*Real.sqrt (C*((ε/(6*(C+1)))^2)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (mul_le_mul hub hdb hd hC)) (by norm_num)
    _ = 2*(Real.sqrt C*(ε/(6*(C+1)))) := by
      rw [Real.sqrt_mul hC,Real.sqrt_sq ha.le]
    _ ≤ 2*((C+1)*(ε/(6*(C+1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs ha.le) (by norm_num)
    _ = ε/3 := by nlinarith only [he]


/-- Uniform convergence of positive trace-class sandwiches from uniform
compressed convergence, total trace convergence, and compact pure limit.
These are separate, source-level analytic inputs, not the target limit. -/
theorem uniform_gentle_limit (b : HilbertBasis ι ℂ E) (P : ProjectionMeasure E)
    (hpos : P.toFun (Set.Ici 1) = 1)
    (B : ℕ → T → E →L[ℂ] E) (g : T → E)
    (hB : ∀ n t, (B n t).IsPositive ∧ IsTraceClass (B n t))
    (hg : IsCompact (Set.range g))
    (ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |total (B n t)-‖g t‖^2| ≤ ε)
    (hc : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (P.toFun (Set.Icc 1 (m : ℝ))*
        (B n t-InnerProductSpace.rankOne ℂ (g t) (g t))*P.toFun (Set.Icc 1 (m : ℝ))) ≤
          ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (B n t-InnerProductSpace.rankOne ℂ (g t) (g t)) ≤ ENNReal.ofReal ε := by
  have hD (t : T) : (InnerProductSpace.rankOne ℂ (g t) (g t)).IsPositive ∧
      IsTraceClass (InnerProductSpace.rankOne ℂ (g t) (g t)) := by
    refine ⟨InnerProductSpace.isPositive_rankOne_self _,?_⟩
    rw [IsTraceClass,traceNorm_of_isPositive (InnerProductSpace.isPositive_rankOne_self _),
      Fidelity.posTrace_rankOne_self]
    exact ENNReal.ofReal_lt_top
  have htr (t : T) : total (InnerProductSpace.rankOne ℂ (g t) (g t)) = ‖g t‖^2 := by
    rw [total,Fidelity.posTrace_rankOne_self,ENNReal.toReal_ofReal (sq_nonneg _)]
  obtain ⟨R,hR,hRg⟩ := hg.isBounded.exists_pos_norm_le
  let C := R^2+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCg (t : T) : ‖g t‖^2 ≤ R^2 := by
    have hh := hRg (g t) (Set.mem_range_self t)
    exact (sq_le_sq₀ (norm_nonneg (g t)) hR.le).mpr hh
  intro ε hε
  let δ := (ε/(6*(C+1)))^2
  have hδ : 0 < δ := sq_pos_of_pos (div_pos hε (by positivity))
  obtain ⟨m,hm⟩ := (compact_tails P hpos g hg (δ/3) (by positivity)).exists
  let Q := P.toFun (Set.Icc 1 (m : ℝ))
  let D := fun t => InnerProductSpace.rankOne ℂ (g t) (g t)
  filter_upwards [ht 1 zero_lt_one,ht (δ/3) (by positivity),
    hc m (min (δ/3) (ε/3)) (lt_min (by positivity) (by positivity))] with n hn htN hcN
  intro t
  have hbt : total (B n t) ≤ C := by
    have hh := le_abs_self (total (B n t)-‖g t‖^2)
    have hx := hn t
    dsimp [C]
    linarith only [hx,hh,hCg t]
  have hdt : total (D t) ≤ C := by dsimp [D]; rw [htr]; dsimp [C]; linarith only [hCg t]
  have hcomp : traceNorm (Q*(B n t-D t)*Q) ≤ ENNReal.ofReal (min (δ/3) (ε/3)) := hcN t
  have hcompr : (traceNorm (Q*(B n t-D t)*Q)).toReal ≤ δ/3 :=
    (ENNReal.toReal_le_of_le_ofReal (le_min (by positivity) (by positivity)) hcomp).trans (min_le_left _ _)
  have htailD : tail Q (D t) ≤ δ/3 := hm t
  have htailB : tail Q (B n t) ≤ δ := by
    have hh := tail_difference b P (Set.Icc 1 (m : ℝ)) measurableSet_Icc (B n t) (D t)
      (hB n t).1 (hD t).1 (hB n t).2 (hD t).2
    have hx := htN t
    rw [← htr t] at hx
    have hy := le_abs_self (tail Q (B n t)-tail Q (D t))
    change |tail Q (B n t)-tail Q (D t)| ≤
      |total (B n t)-total (D t)|+_ at hh
    linarith only [hh,hx,hy,hcompr,htailD]
  have hQ : IsStarProjection Q := projection P (Set.Icc 1 (m : ℝ)) measurableSet_Icc
  have hgB := positive_trace_gentle b (B n t) Q (hB n t).1 (hB n t).2
    hQ
  have hgD := positive_trace_gentle b (D t) Q (hD t).1 (hD t).2
    hQ
  have heB : traceNorm (B n t-Q*B n t*Q) ≤ ENNReal.ofReal (ε/3) :=
    hgB.trans (ENNReal.ofReal_le_ofReal
      (gentle_small C ε hC hε _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hbt htailB))
  have heD : traceNorm (D t-Q*D t*Q) ≤ ENNReal.ofReal (ε/3) :=
    hgD.trans (ENNReal.ofReal_le_ofReal
      (gentle_small C ε hC hε _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hdt
        (htailD.trans (by linarith))))
  have hneg : traceNorm (Q*D t*Q-D t) = traceNorm (D t-Q*D t*Q) := by
    rw [show Q*D t*Q-D t = (-1 : ℂ) • (D t-Q*D t*Q) by
      rw [neg_one_smul]; abel,traceNorm_smul]
    simp
  have hid : B n t-D t = (B n t-Q*B n t*Q)+Q*(B n t-D t)*Q+(Q*D t*Q-D t) := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ traceNorm (B n t-Q*B n t*Q)+traceNorm (Q*(B n t-D t)*Q)+
        traceNorm (Q*D t*Q-D t) :=
      (traceNorm_add_le ((B n t-Q*B n t*Q)+Q*(B n t-D t)*Q) (Q*D t*Q-D t)).trans
        (add_le_add (traceNorm_add_le (B n t-Q*B n t*Q) (Q*(B n t-D t)*Q))
          (le_refl (traceNorm (Q*D t*Q-D t))))
    _ ≤ ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3) := by
      rw [hneg]
      exact add_le_add (add_le_add heB (hcomp.trans
        (ENNReal.ofReal_le_ofReal (min_le_right _ _)))) heD
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
end QuantumNLS.EnergyTraceLimit

#print axioms QuantumNLS.EnergyTraceLimit.rankOne_tail
#print axioms QuantumNLS.EnergyTraceLimit.compact_tails
#print axioms QuantumNLS.EnergyTraceLimit.gentle_small
#print axioms QuantumNLS.EnergyTraceLimit.uniform_gentle_limit
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyTraceLimit" then
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
  Lean.logInfo m!"EnergyTraceLimit audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
