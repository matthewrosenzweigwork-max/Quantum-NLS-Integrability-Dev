import QuantumNLS.Ext025B7LocalPath
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! GP-15/16, LOCAL-017: build the source radial perturbation primitive
beta_z = integral_0^1 t (Omega_(tz)-omega)(z,.) dt in the full real dual.
Continuity is derived from the original two-form's continuity and quadratic
bound on its ball. No continuity of beta is supplied as a premise.
The angular derivative and common analytic/Taylor bounds remain separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Topology Metric
namespace QuantumNLS.Ext025B10LocalBeta
open Ext025B7LocalPath
abbrev Covector : Type := (Ext025B7LocalPath.H →L[ℝ] ℝ)
abbrev TwoForm : Type := (Ext025B7LocalPath.H →L[ℝ] Covector)

/-- Delta is the source two-form Omega - omega, with its original normalization. -/
def beta (Δ : H → TwoForm) (z : H) : H →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, t • (Δ (t • z) z)

theorem scale_mem {R : ℝ} {z : H} (hz : z ∈ ball 0 R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • z ∈ ball 0 R := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz

theorem radial_continuous {R : ℝ} (Δ : H → TwoForm)
    (hΔ : ContinuousOn Δ (ball 0 R)) (z : H) (hz : z ∈ ball 0 R) :
    ContinuousOn (fun t : ℝ => t • (Δ (t • z) z)) (Set.Icc 0 1) := by
  have hs : ContinuousOn (fun t : ℝ => t • z) (Set.Icc 0 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have hd : ContinuousOn (fun t : ℝ => Δ (t • z)) (Set.Icc 0 1) :=
    hΔ.comp hs (fun t ht => scale_mem hz ht)
  have he : ContinuousOn (fun t : ℝ => Δ (t • z) z) (Set.Icc 0 1) :=
    hd.clm_apply (continuousOn_const (c := z))
  exact continuousOn_id.smul he

/-- The source's quadratic form bound supplies a common integrable bound,
independent of points in the Hilbert ball and of finite coordinate supports. -/
theorem radial_bound {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (Δ : H → TwoForm) (hb : ∀ z ∈ ball (0 : H) R, ‖Δ z‖ ≤ C*‖z‖^2)
    (z : H) (hz : z ∈ ball 0 R) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ‖t • (Δ (t • z) z)‖ ≤ C*R^3 := by
  have hzR : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
  have htz : ‖t • z‖ ≤ R := (mem_ball_zero_iff.mp (scale_mem hz ht)).le
  calc
    _ = t*‖Δ (t • z) z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    _ ≤ 1*(C*R^2*R) := by
      apply mul_le_mul ht.2 _ (norm_nonneg _) (by positivity)
      exact ((Δ (t • z)).le_opNorm z).trans
        (mul_le_mul ((hb _ (scale_mem hz ht)).trans (by gcongr)) hzR (norm_nonneg _) (by positivity))
    _ = C*R^3 := by ring

/-- Continuity of the actual radial primitive in full dual norm on its ball. -/
theorem beta_continuousOn {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (Δ : H → TwoForm) (hΔ : ContinuousOn Δ (ball 0 R))
    (hb : ∀ z ∈ ball (0 : H) R, ‖Δ z‖ ≤ C*‖z‖^2) :
    ContinuousOn (beta Δ) (ball 0 R) := by
  intro z hz
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun _ => C*R^3)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Set.uIoc_of_le zero_le_one] using
      ((radial_continuous Δ hΔ x hx).mono
        Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact .of_forall fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact radial_bound hR hC Δ hb x hx t ⟨ht.1.le,ht.2⟩
  · exact intervalIntegrable_const
  · exact .of_forall fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hs : ContinuousOn (fun x : H => t • x) (ball 0 R) :=
        (continuous_const_smul t).continuousOn
      have hd : ContinuousOn (fun x : H => Δ (t • x)) (ball 0 R) :=
        hΔ.comp hs (fun x hx => scale_mem hx ⟨ht.1.le,ht.2⟩)
      have he : ContinuousOn (fun x : H => Δ (t • x) x) (ball 0 R) :=
        hd.clm_apply continuousOn_id
      exact ((continuousOn_const (c := t)).smul he) z hz

/-- This removes the old independent beta-continuity hypothesis from the
literal LOCAL-017 path evaluation, using the source's own two-form bounds. -/
theorem path_continuous {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (Δ : H → TwoForm) (hΔ : ContinuousOn Δ (ball 0 R))
    (hb : ∀ z ∈ ball (0 : H) R, ‖Δ z‖ ≤ C*‖z‖^2)
    (z : H) (hz : z ∈ ball 0 R) : Continuous (pathIntegrand (beta Δ) z) := by
  have hrot : Continuous (fun p : PathParameter => rotation p z) :=
    rotation_continuous.comp (continuous_id.prodMk continuous_const)
  have hmem : ∀ p : PathParameter, rotation p z ∈ ball 0 R := by
    intro p
    simpa only [mem_ball_zero_iff,rotation_norm] using hz
  exact ((beta_continuousOn hR hC Δ hΔ hb).comp_continuous hrot hmem).clm_apply
    (velocity_continuous.comp (continuous_fst.prodMk hrot))

/-- Bind Delta literally to the source Omega - omega, rather than a
separate covector with a supplied continuity conclusion. -/
def sourceBeta (Ω : H → TwoForm) (ω : TwoForm) := beta (fun z => Ω z-ω)

theorem source_path_continuous {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (Ω : H → TwoForm) (ω : TwoForm)
    (hΔ : ContinuousOn (fun z => Ω z-ω) (ball 0 R))
    (hb : ∀ z ∈ ball (0 : H) R, ‖Ω z-ω‖ ≤ C*‖z‖^2)
    (z : H) (hz : z ∈ ball 0 R) :
    Continuous (pathIntegrand (sourceBeta Ω ω) z) :=
  path_continuous hR hC (fun z => Ω z-ω) hΔ hb z hz

end QuantumNLS.Ext025B10LocalBeta

#print axioms QuantumNLS.Ext025B10LocalBeta.beta
#print axioms QuantumNLS.Ext025B10LocalBeta.beta_continuousOn
#print axioms QuantumNLS.Ext025B10LocalBeta.path_continuous
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B10LocalBeta" then
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
  Lean.logInfo m!"Ext025B10LocalBeta audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
