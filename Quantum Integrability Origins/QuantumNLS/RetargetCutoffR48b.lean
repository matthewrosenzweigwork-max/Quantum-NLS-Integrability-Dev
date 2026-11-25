import QuantumNLS.RetargetSeedPrepR48b
import QuantumNLS.TerraMultiRound87Classical

/-! Uniform phase cutoff by a finite cover of the compact chart image. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Topology

namespace QuantumNLS.RetargetCutoffR48b
open PhysicalTensor CountRotations DynSeedInputR47b HighAngleRotations
open RetargetAnglesR48b (labels mem_labels)
open D01LocalPrimitive (K)
variable {L κ : ℝ} [Fact (0 < L)]

theorem coor_dist (θ : AngleTorus) (z w : K) :
    dist (coordinateRotation θ z) (coordinateRotation θ w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm]
  exact ActionTorus.norm_rotate_sub θ⁻¹ z w

theorem coordinate_cutoff {S : Set K} (hS : IsCompact S) (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J, J₀ ≤ J → ∀ z ∈ S, ∀ θ : AngleTorus,
      dist (coordinateRotation (truncate (labels J) θ) z) (coordinateRotation θ z) < ε := by
  let P (J : ℕ) (z : K) := ∀ θ : AngleTorus,
    dist (coordinateRotation (truncate (labels J) θ) z) (coordinateRotation θ z) < ε
  apply R52CFCompact.uniform_of_local hS P
  intro x hx
  have hη : 0 < ε / 4 := by positivity
  obtain ⟨F, hF⟩ := TerraMultiRound87Classical.finite_coordinates_control x (ε/4) hη
  refine ⟨Metric.ball x (ε/4), Metric.ball_mem_nhds x hη, F.sup Int.natAbs, ?_⟩
  intro J hJ z hz θ
  have hg (a : ℤ) (ha : a ∈ F) : (truncate (labels J) θ)⁻¹ a = θ⁻¹ a := by
    have hJ' : a.natAbs ≤ J := (Finset.le_sup ha).trans hJ
    have hmem : a ∈ labels J := by
      apply (mem_labels J a).2
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hJ'
    change (truncate (labels J) θ a)⁻¹ = (θ a)⁻¹
    rw [truncate, ite_eq_left hmem]
  have hmid : dist (coordinateRotation (truncate (labels J) θ) x) (coordinateRotation θ x) < ε/4 := by
    rw [dist_eq_norm]
    exact hF x (fun _ => rfl) _ _ hg
  have hz' : dist z x < ε / 4 := hz
  let V := coordinateRotation (truncate (labels J) θ)
  let W := coordinateRotation θ
  have h₁ := dist_triangle (V z) (V x) (W z)
  have h₂ := dist_triangle (V x) (W x) (W z)
  change dist (V z) (W z) < ε
  rw [show dist (V z) (V x) = dist z x from coor_dist _ _ _] at h₁
  rw [show dist (W x) (W z) = dist x z from coor_dist _ _ _, dist_comm x z] at h₂
  linarith

theorem uniform_classical_cutoff (hκ : 0 < κ) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ (θ : AngleTorus) (u : L2T L), u ∈ closure (R52CFCompact.profileClass L R) →
      dist (physicalAngle hκ (truncate (labels J) θ) u) (physicalAngle hκ θ u) < ε := by
  let C := Def021ChartR41b.chart L κ hκ
  let U := closure (R52CFCompact.profileClass L R)
  let O : Set (L2T L) := (RetargetCompactR48b.orbit (L := L) hκ R : Set (L2T L))
  have hΦ : Continuous C.Φ := continuous_iff_continuousAt.mpr fun v => (C.analytic v).continuousAt
  have hΨ : Continuous C.Ψ := continuous_iff_continuousAt.mpr fun y => (C.inverse_analytic y).continuousAt
  have hO : IsCompact (C.Φ '' O) := (RetargetCompactR48b.orbit_compact (L := L) hκ R).image hΦ
  obtain ⟨δ, hδ, hD⟩ := Metric.uniformContinuousOn_iff.mp
    (hO.uniformContinuousOn_of_continuous hΨ.continuousOn) ε hε
  have hU : IsCompact (C.Φ '' U) := (RetargetCompactR48b.root01_profile_compact (L := L) R).image hΦ
  obtain ⟨J₀, hJ₀⟩ := coordinate_cutoff hU δ hδ
  filter_upwards [eventually_ge_atTop J₀] with J hJ
  intro θ u hu
  have hmem (φ : AngleTorus) : coordinateRotation φ (C.Φ u) ∈ C.Φ '' O := by
    refine ⟨physicalAngle hκ φ u, ⟨u, hu, ?_⟩, C.right_inverse _⟩
    exact DynSeedClassicalR47b.angle_mem_torus hκ u u (fun _ => rfl) φ
  exact hD _ (hmem _) _ (hmem _) (hJ₀ J hJ _ ⟨u,hu,rfl⟩ θ)

end QuantumNLS.RetargetCutoffR48b

#print axioms QuantumNLS.RetargetCutoffR48b.uniform_classical_cutoff

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetCutoffR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetCutoffR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
