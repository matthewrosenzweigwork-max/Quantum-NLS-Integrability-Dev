import QuantumNLS.Ext006SeriesIdentificationR43a
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Strong continuity of the whole-space field exponential. All uniform
bounds follow from the actual finite-particle factorial estimates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ExponentialContinuityR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006ExponentialInnerR43a Ext006BoundedExponentialR43a
open Ext006SeriesIdentificationR43a

lemma term_uniform_bound {N : ℕ} (h : H) (R : ℝ) (v : D)
    (hv : ParticleBound N v.1) {t : ℝ} (ht : |t| ≤ R) (n : ℕ) :
    ‖exponentialTerm h t v n‖ ≤
      Real.sqrt (squareMajorant N (4*‖h‖^2*R^2) n)*‖v.1‖ := by
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have hm : squareMajorant N (4*‖h‖^2*|t|^2) n ≤
      squareMajorant N (4*‖h‖^2*R^2) n := by
    unfold squareMajorant
    gcongr
  have hb := (exponentialTerm_norm_sq_le h t v hv n).trans
    (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  have hs := Real.sq_sqrt (squareMajorant_nonneg N
    (show 0 ≤ 4*‖h‖^2*R^2 by positivity) n)
  have hn : 0 ≤ Real.sqrt (squareMajorant N (4*‖h‖^2*R^2) n)*‖v.1‖ := by positivity
  nlinarith [norm_nonneg (exponentialTerm h t v n)]

lemma exponential_continuous {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    Continuous (fun t : ℝ => exponential h t v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let R : ℝ := |t|+1
  have hsum : Summable (fun n => Real.sqrt (squareMajorant N (4*‖h‖^2*R^2) n)*‖v.1‖) :=
    (summable_sqrt_majorant N (by positivity)).mul_right _
  have hc : ContinuousOn (fun t : ℝ => exponential h t v) (Metric.closedBall 0 R) := by
    have hterms (n : ℕ) : ContinuousOn (fun s : ℝ => exponentialTerm h s v n) (Metric.closedBall 0 R) := by
      unfold exponentialTerm
      fun_prop
    refine continuousOn_tsum hterms hsum ?_
    intro n s hs
    apply term_uniform_bound h R v hv _
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hs
  apply hc.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,R] using (lt_add_one |t|)

/-- Strong continuity on EVERY vector, obtained by density and the proved
isometry bound; there is no assumed strong-continuity interface. -/
theorem unitary_strong_continuous (h : H) (x : Fock) :
    Continuous (fun t : ℝ => unitary h t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨y,⟨v,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp (core_dense x) (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := v.2
  have hc : Continuous (fun s : ℝ => unitary h s (inclusion v)) := by
    have he : (fun s : ℝ => unitary h s (inclusion v)) =
        (fun s : ℝ => exponential h s v.1) := funext (fun s => unitary_core h s v)
    rw [he]
    exact exponential_continuous h v.1 hN
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc.continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,fun s hs => ?_⟩
  have hm := hclose hs
  calc
    dist (unitary h s x) (unitary h t x) ≤
        dist (unitary h s x) (unitary h s (inclusion v)) +
        dist (unitary h s (inclusion v)) (unitary h t (inclusion v)) +
        dist (unitary h t (inclusion v)) (unitary h t x) := dist_triangle4 _ _ _ _
    _ = dist x (inclusion v) +
        dist (unitary h s (inclusion v)) (unitary h t (inclusion v)) + dist x (inclusion v) := by
      rw [(unitary h s).isometry.dist_eq,(unitary h t).isometry.dist_eq,dist_comm (inclusion v) x]
    _ < ε := by linarith

end QuantumNLS.Ext006ExponentialContinuityR43a
#print axioms QuantumNLS.Ext006ExponentialContinuityR43a.unitary_strong_continuous

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ExponentialContinuityR43a." then
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
