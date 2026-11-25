import QuantumNLS.Ext025A4BanachComplexification
import QuantumNLS.Ext025A4CompactAssembly

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal
namespace QuantumNLS.Ext025A4SourcePaths
open QuantumNLS.Ext025A4BanachComplexification
open QuantumNLS.Ext025A4AnalyticIntegral
universe u v
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {ι : Type*}

/-- Compactness and the source operator bound give one actual velocity
bound, including an empty parameter family, without a supplied majorant. -/
theorem reference_velocity_bound (g : V → W) (L : ι → W →L[ℝ] V)
    (B : ℝ) (φ : ι → ℝ → V → V) (S : Set V) (u : V)
    (hS : IsCompact S) (hg : AnalyticOnNhd ℝ g S) (hL : ∀ i, ‖L i‖ ≤ B)
    (hm : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, φ i t u ∈ S) :
    ∃ M ≥ (0 : ℝ), ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      ‖L i (g (φ i t u))‖ ≤ M := by
  obtain ⟨C,hC⟩ := (hS.image_of_continuousOn hg.continuousOn).isBounded.subset_closedBall (0 : W)
  let M := max B 0 * max C 0
  refine ⟨M, mul_nonneg (le_max_right _ _) (le_max_right _ _), fun i t ht => ?_⟩
  have hc : ‖g (φ i t u)‖ ≤ C := by
    simpa only [mem_closedBall, dist_zero_right] using hC ⟨φ i t u,hm i t ht,rfl⟩
  exact ((L i).le_opNorm _).trans
    (mul_le_mul ((hL i).trans (le_max_left _ _)) (hc.trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _))

/-- A real source trajectory has a common Lipschitz bound on [0,1]. -/
theorem reference_dist {g : V → W} {L : ι → W →L[ℝ] V}
    {φ : ι → ℝ → V → V} {u : V} {M : ℝ}
    (hd : ∀ i x t, HasDerivAt (fun s => φ i s x) (L i (g (φ i t x))) t)
    (hb : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ‖L i (g (φ i t u))‖ ≤ M)
    (i : ι) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (φ i t u) (φ i s u) ≤ M * |t-s| := by
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hd i u z).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hb i z hz) hs ht

/-- The source's actual normalized trajectory, embedded in the general
Banach complexification. -/
def referencePath (φ : ι → ℝ → V → V) (u : V)
    (hd : ∀ i x t, DifferentiableAt ℝ (fun s => φ i s x) t)
    (i : ι) (s d : ℝ) : Path (Cx V) :=
  ⟨fun t => Cx.ι (φ i (s+d*(t : ℝ)) u),
    (Cx.ιL.continuous.comp (continuous_iff_continuousAt.mpr
      (fun t => (hd i u t).continuousAt))).comp
      (continuous_const.add (continuous_const.mul continuous_subtype_val))⟩

/-- Displacement control of the actual reference path follows from its
source ODE, rather than being an extra trajectory premise. -/
theorem referencePath_ball {g : V → W} {L : ι → W →L[ℝ] V}
    {φ : ι → ℝ → V → V} {u : V} {M s d r : ℝ}
    (hd : ∀ i x t, HasDerivAt (fun s => φ i s x) (L i (g (φ i t x))) t)
    (hb : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ‖L i (g (φ i t u))‖ ≤ M)
    (hM : 0 ≤ M) (hs : 0 ≤ s) (hd0 : 0 ≤ d) (hsd : s+d ≤ 1) (hr : d*M ≤ r)
    (i : ι) : referencePath φ u (fun i x t => (hd i x t).differentiableAt) i s d ∈
      closedBall (ContinuousMap.const Time (Cx.ι (φ i s u))) r := by
  have hr0 : 0 ≤ r := (mul_nonneg hd0 hM).trans hr
  rw [mem_closedBall, dist_eq_norm]
  apply (ContinuousMap.norm_le _ hr0).mpr
  intro t
  change ‖Cx.ι (φ i (s+d*(t : ℝ)) u) - Cx.ι (φ i s u)‖ ≤ r
  rw [← Cx.ι_sub, Cx.norm_ι, ← dist_eq_norm]
  have hst : s+d*(t : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [t.2.1,t.2.2]
  have hbound := reference_dist hd hb i ⟨hs,by linarith⟩ hst
  have ha : |s+d*(t : ℝ)-s| = d*(t : ℝ) := by
    rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hd0 t.2.1)]
  rw [ha] at hbound
  apply hbound.trans
  calc M * (d * (t : ℝ)) = (d*M) * (t : ℝ) := by ring
    _ ≤ (d*M) * 1 := mul_le_mul_of_nonneg_left t.2.2 (mul_nonneg hd0 hM)
    _ ≤ r := by simpa only [mul_one] using hr

/-- FTC proves the literal complex Picard fixed-point identity for the
actual source path wherever the local field chart agrees along it. -/
theorem referencePath_fixedPoint {g : V → W} {L : ι → W →L[ℝ] V}
    {φ : ι → ℝ → V → V} {u : V} {s d : ℝ}
    (hd : ∀ i x t, HasDerivAt (fun s => φ i s x) (L i (g (φ i t x))) t)
    (i : ι) (G : Cx V → Cx V) (hc : Continuous G)
    (he : ∀ t : Time, G (Cx.ι (φ i (s+d*(t : ℝ)) u)) =
      Cx.ι (L i (g (φ i (s+d*(t : ℝ)) u)))) :
    picard G hc d (Cx.ι (φ i s u),referencePath φ u (fun i x t => (hd i x t).differentiableAt) i s d) =
      referencePath φ u (fun i x t => (hd i x t).differentiableAt) i s d := by
  let v := referencePath φ u (fun i x t => (hd i x t).differentiableAt) i s d
  let α : ℝ → Cx V := fun t => Cx.ι (φ i (s+d*t) u)
  have hα : Continuous α := Cx.ιL.continuous.comp
    ((continuous_iff_continuousAt.mpr (fun t => (hd i u t).continuousAt)).comp
      (continuous_const.add (continuous_const.mul continuous_id)))
  have hαd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt α (d • G (α t)) t := by
    have hh := (hd i u (s+d*t)).scomp t (((hasDerivAt_id t).const_mul d).const_add s)
    have hhh := (Cx.ιL : V →L[ℝ] Cx V).hasFDerivAt.comp_hasDerivAt t hh
    simpa only [mul_one, map_smul, Cx.ιL_apply, Function.comp_def, id_eq, ← he ⟨t,ht⟩] using hhh
  apply ContinuousMap.ext
  intro t
  have hint : d • (∫ z in (0 : ℝ)..(t : ℝ), G (α z)) = α t - α 0 := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z hz => hαd z ((uIcc_subset_Icc (by constructor <;> norm_num) t.2) hz))
      (((hc.comp hα).const_smul d).intervalIntegrable _ _)
  have hext (z : ℝ) (hz : z ∈ uIcc (0 : ℝ) (t : ℝ)) :
      extend (QuantumNLS.Ext025A4AnalyticPath.superposition G hc v) z = G (α z) := by
    have hz' := (uIcc_subset_Icc (by constructor <;> norm_num) t.2) hz
    change G (Cx.ι (φ i (s+d*(projIcc 0 1 zero_le_one z)) u)) = G (α z)
    rw [projIcc_of_mem _ hz']
  change Cx.ι (φ i s u) + (d : ℂ) • (∫ z in (0 : ℝ)..(t : ℝ), _) = α t
  rw [intervalIntegral.integral_congr hext, Cx.ofReal_smul, hint]
  have h0 : α 0 = Cx.ι (φ i s u) := by simp [α]
  rw [h0]
  abel

end QuantumNLS.Ext025A4SourcePaths

#print axioms QuantumNLS.Ext025A4SourcePaths.reference_velocity_bound
#print axioms QuantumNLS.Ext025A4SourcePaths.reference_dist
#print axioms QuantumNLS.Ext025A4SourcePaths.referencePath
#print axioms QuantumNLS.Ext025A4SourcePaths.referencePath_ball
#print axioms QuantumNLS.Ext025A4SourcePaths.referencePath_fixedPoint

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4SourcePaths" then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
