import QuantumNLS.Ext025A4CompactAssembly
import QuantumNLS.Ext025A2ODE

/-! Round 93. Source instantiation of local complex Picard branches.
All earlier modules are read-only. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal
namespace QuantumNLS.Ext025A4RealFlow
open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear
open QuantumNLS.Ext025A4AnalyticIntegral

universe u
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The projection needed to restrict a constructed complex branch. -/
def reL : Cx F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := Cx.re
      map_add' := Cx.re_add
      map_smul' := fun c z => by
        change Cx.re (c • z) = c • Cx.re z
        rw [← ofReal_smul' c z, Cx.re_smul]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero] }
    1 (fun z => by simpa using norm_re_le z)

/-- A local analytic field supplies a clipped continuous complex extension,
with differential Lipschitz and field Lipschitz bounds on smaller balls. -/
theorem local_field_data {f : F → F} {a : F} (ha : AnalyticAt ℝ f a) :
    ∃ R > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∃ K : ℝ≥0, ∃ Λ ≥ (0 : ℝ),
      ∃ G : Cx F → Cx F, Continuous G ∧
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧
      (∀ x ∈ ball (Cx.ι a) R, ∀ y ∈ ball (Cx.ι a) R,
        ‖fderiv ℂ G x - fderiv ℂ G y‖ ≤ Λ * ‖x-y‖) ∧
      (∀ z ∈ closedBall (Cx.ι a) (R/2), ‖G z‖ ≤ M) ∧
      LipschitzOnWith K G (closedBall (Cx.ι a) (R/2)) ∧
      ∀ x ∈ closedBall a (R/2), G (Cx.ι x) = Cx.ι (f x) := by
  obtain ⟨R₀, hR₀, M, G, hd, _, hb, he⟩ :=
    QuantumNLS.Ext025A4HilbertCharts.local_field_extension ha
  obtain ⟨D, hD, Λ, hΛ, hLip⟩ :=
    QuantumNLS.HolomorphicCauchyC1.fderiv_lipschitz_near isOpen_ball hd (mem_ball_self hR₀)
  obtain ⟨d, hd0, hdsub, K, hK, hfd⟩ :=
    QuantumNLS.HolomorphicCauchyC1.exists_uniform_fderiv_bound isOpen_ball hd (mem_ball_self hR₀)
  let R := min (R₀/2) (min (D/4) (d/2))
  have hR : 0 < R := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hRR : R < R₀ := (min_le_left _ _).trans_lt (half_lt_self hR₀)
  have hRD : R ≤ D/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hRd : R < d := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hd0)
  obtain ⟨G', hc, he', hd'⟩ :=
    QuantumNLS.Ext025A4LocalExtension.holomorphic_continuous_extension hR hRR hd
  have hfe (z : Cx F) (hz : z ∈ ball (Cx.ι a) R) : fderiv ℂ G' z = fderiv ℂ G z :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) (Filter.mem_of_superset (isOpen_ball.mem_nhds hz)
      (fun w hw => he' (ball_subset_closedBall hw)))
  have hsub : closedBall (Cx.ι a) (R/2) ⊆ ball (Cx.ι a) R :=
    closedBall_subset_ball (half_lt_self hR)
  have hMG : 0 ≤ M := (norm_nonneg _).trans (hb _ (mem_ball_self hR₀))
  refine ⟨R, hR, M, hMG, ⟨K,hK⟩, Λ, hΛ, G', hc, hd', ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hfe x hx, hfe y hy]
    exact hLip x (ball_subset_ball hRD hx) y (ball_subset_ball hRD hy)
  · intro z hz
    rw [he' (closedBall_subset_closedBall (half_le_self hR.le) hz)]
    exact hb z (ball_subset_ball hRR.le (hsub hz))
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    apply (convex_closedBall (Cx.ι a) (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (((hd'.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
      (fun z hz => ?_) hy hx
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro v
    change ‖fderiv ℂ G' z v‖ ≤ K * ‖v‖
    rw [hfe z (hsub hz)]
    exact hfd z (ball_subset_ball hRd.le (hsub hz)) v
  · intro x hx
    have hh : Cx.ι x ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall, dist_eq_norm, ← ι_sub, Cx.norm_ι] using hx
    rw [he' (closedBall_subset_closedBall (half_le_self hR.le) hh)]
    exact he x (ball_subset_ball hRR.le ((closedBall_subset_ball (half_lt_self hR)) hx))

end QuantumNLS.Ext025A4RealFlow

#print axioms QuantumNLS.Ext025A4RealFlow.reL
#print axioms QuantumNLS.Ext025A4RealFlow.local_field_data

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4RealFlow" then
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
