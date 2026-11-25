import QuantumNLS.L1TraceGeometry
import QuantumNLS.L2DiscriminantRegularity
import QuantumNLS.RootDensityFormula

/-! Unconditional open-band and bounded-gap geometry for the actual
arbitrary-L2 discriminant. These are spatial statements; no identification
of the canonical quantum measure with a spectral density is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.PhysicalL2BandGeometry

/-- `Δ` at the zeros `±(2j+1)π/L` of the free trace tends to `0`. -/
theorem tendsto_small (L : ℝ) (d : ℝ → ℝ) (hL : 0 < L)
    (hasym : Tendsto (fun t => d t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun j : ℕ => d ((2 * (j : ℝ) + 1) * Real.pi / L)) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => d (-((2 * (j : ℝ) + 1) * Real.pi / L))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have hcos : ∀ j : ℕ, Real.cos ((2 * (j : ℝ) + 1) * Real.pi / L * L / 2) = 0 := by
    intro j
    have : (2 * (j : ℝ) + 1) * Real.pi / L * L / 2 = (j : ℝ) * Real.pi + Real.pi / 2 := by
      field_simp
    rw [this, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]; simp
  constructor
  · have h1 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop (cocompact ℝ) := by
      rw [cocompact_eq_atBot_atTop]; exact h0.mono_right le_sup_right
    have := hasym.comp h1
    refine this.congr (fun j => ?_)
    simp [Function.comp, hcos j]
  · have h1 : Tendsto (fun j : ℕ => -((2 * (j : ℝ) + 1) * Real.pi / L)) atTop (cocompact ℝ) := by
      rw [cocompact_eq_atBot_atTop]; exact (tendsto_neg_atTop_atBot.comp h0).mono_right le_sup_left
    have := hasym.comp h1
    refine this.congr (fun j => ?_)
    have e : Real.cos (-((2 * (j : ℝ) + 1) * Real.pi / L) * L / 2) = 0 := by
      rw [neg_mul, neg_div, Real.cos_neg]
      exact hcos j
    simp only [Function.comp, e]
    ring

theorem exists_small_pos (L : ℝ) (d : ℝ → ℝ) (hL : 0 < L)
    (hasym : Tendsto (fun t => d t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) (R : ℝ) :
    ∃ p : ℝ, R ≤ p ∧ |d p| < 2 := by
  obtain ⟨h1, -⟩ := tendsto_small L d hL hasym
  have h0 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have h2 : ∀ᶠ j : ℕ in atTop, |d ((2 * (j : ℝ) + 1) * Real.pi / L)| < 2 :=
    ((tendsto_order.1 (by simpa using h1.abs)).2 2 (by norm_num))
  obtain ⟨j, hj1, hj2⟩ := ((h0.eventually_ge_atTop R).and h2).exists
  exact ⟨_, hj1, hj2⟩

theorem exists_small_neg (L : ℝ) (d : ℝ → ℝ) (hL : 0 < L)
    (hasym : Tendsto (fun t => d t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) (R : ℝ) :
    ∃ p : ℝ, p ≤ R ∧ |d p| < 2 := by
  obtain ⟨-, h1⟩ := tendsto_small L d hL hasym
  have h0 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have h2 : ∀ᶠ j : ℕ in atTop, |d (-((2 * (j : ℝ) + 1) * Real.pi / L))| < 2 :=
    ((tendsto_order.1 (by simpa using h1.abs)).2 2 (by norm_num))
  obtain ⟨j, hj1, hj2⟩ := ((h0.eventually_ge_atTop (-R)).and h2).exists
  exact ⟨_, by linarith, hj2⟩

variable {L κ : ℝ} [Fact (0 < L)]

/-- Real-axis actual physical discriminant. -/
def d (u : PhysicalTensor.L2T L) (t : ℝ) : ℝ :=
  (L2SpatialTransfer.discriminant κ u (t : ℂ)).re

theorem continuous_d (u : PhysicalTensor.L2T L) : Continuous (d (κ := κ) u) :=
  Complex.continuous_re.comp
    ((L2DiscriminantRegularity.continuous_discriminant κ u).comp Complex.continuous_ofReal)

/-- There are points in actual open bands arbitrarily far in both directions. -/
theorem unbounded_bands (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (R : ℝ) :
    (∃ p : ℝ, R ≤ p ∧ |d (κ := κ) u p| < 2) ∧
    (∃ p : ℝ, p ≤ R ∧ |d (κ := κ) u p| < 2) := by
  have ha := L1TraceGeometry.L2_trace_asymptotic hκ u
  exact ⟨exists_small_pos L (d (κ := κ) u) Fact.out ha R,
    exists_small_neg L (d (κ := κ) u) Fact.out ha R⟩

/-- Every physical open gap component is bounded and meets |Δ|=2 at both endpoints. -/
theorem bounded_gap_component (hκ : 0 < κ) (u : PhysicalTensor.L2T L) {x : ℝ}
    (hx : 2 < |d (κ := κ) u x|) :
    ∃ a b : ℝ, a < x ∧ x < b ∧
      connectedComponentIn {t | 2 < |d (κ := κ) u t|} x = Ioo a b ∧
      |d (κ := κ) u a| = 2 ∧ |d (κ := κ) u b| = 2 := by
  apply RootDensity.connectedComponentIn_eq_Ioo (continuous_d u)
  · intro R
    obtain ⟨p, hp, hb⟩ := (unbounded_bands hκ u R).1
    exact ⟨p, hp, hb.le⟩
  · intro R
    obtain ⟨p, hp, hb⟩ := (unbounded_bands hκ u R).2
    exact ⟨p, hp, hb.le⟩
  · exact hx

/-- The spatial arcosh height is continuous on the real axis for every L2 input. -/
theorem continuous_spatial_height (u : PhysicalTensor.L2T L) :
    Continuous (fun t => RootDensity.hfun |d (κ := κ) u t|) :=
  RootDensity.continuous_hfun.comp (continuous_d u).abs

/-- Its uniform bound is available for arbitrary L2 representatives. -/
theorem spatial_height_le (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (t : ℝ) :
    RootDensity.rootDensity κ (d (κ := κ) u) t ≤
      (∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile u s‖) / (Real.pi * Real.sqrt κ) :=
  RootDensity.rootDensity_le hκ
    (intervalIntegral.integral_nonneg (Fact.out : 0 < L).le (fun _s _ => norm_nonneg _))
    (L1TraceGeometry.L2_abs_trace_le hκ u) t

end QuantumNLS.PhysicalL2BandGeometry

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalL2BandGeometry.tendsto_small
#print axioms QuantumNLS.PhysicalL2BandGeometry.exists_small_pos
#print axioms QuantumNLS.PhysicalL2BandGeometry.exists_small_neg
#print axioms QuantumNLS.PhysicalL2BandGeometry.d
#print axioms QuantumNLS.PhysicalL2BandGeometry.continuous_d
#print axioms QuantumNLS.PhysicalL2BandGeometry.unbounded_bands
#print axioms QuantumNLS.PhysicalL2BandGeometry.bounded_gap_component
#print axioms QuantumNLS.PhysicalL2BandGeometry.continuous_spatial_height
#print axioms QuantumNLS.PhysicalL2BandGeometry.spatial_height_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalL2BandGeometry." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
