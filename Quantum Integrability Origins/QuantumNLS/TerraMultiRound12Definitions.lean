import QuantumNLS.HierarchyFlow
import QuantumNLS.QuantumFourierSpecification
import QuantumNLS.PhysicalProductPreparation
import QuantumNLS.Occupation
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Definition-level bindings for DEF-033, parts of DEF-044, and DEF-035.
DEF-024 is already provided by `HierarchyFlow`. No existence of a chart,
hierarchy flow, or limiting law is asserted here. -/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal

namespace QuantumNLS.TerraMultiRound12Definitions

open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform
  QuantumNLS.BetheSpectralCharges QuantumNLS.Occupation

/-- DEF-033: the real multiplier on an active coordinate, using the existing
fixed-order Hamiltonian flow. Existence is a separate theorem. -/
def IsActiveFrequency {L κ : ℝ} {R : Finset ℕ}
    (F : QuantumNLS.HierarchyFlow.HamFlows L κ R)
    (w : (ℝ → ℂ) → ℤ → ℂ) (action : (ℝ → ℂ) → ℤ → ℝ)
    (r : ℕ) (n : ℤ) (u : ℝ → ℂ) (ω : ℝ) : Prop :=
  0 < action u n ∧ ∀ t : ℝ,
    w (F.Φ r t u) n = Complex.exp (-((t * ω : ℝ) : ℂ) * Complex.I) * w u n

/-- DEF-033 bound to the repository's physical L² chart, indexed action data,
and smooth-profile embedding. No existence of the multiplier is asserted. -/
def IsPhysicalActiveFrequency {L κ : ℝ} [Fact (0 < L)] {R : Finset ℕ}
    (F : QuantumNLS.HierarchyFlow.HamFlows L κ R)
    (D : QuantumNLS.IndexedMassProperness.IndexedMassData L κ)
    (w : QuantumNLS.QuantumFourierSpecification.PhysicalField L →
      QuantumNLS.QuantumFourierSpecification.Coordinates)
    (r : ℕ) (hr : r ∈ R) (n : ℤ) (u : ℝ → ℂ)
    (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L u) (ω : ℝ) : Prop :=
  0 < D.seq (QuantumNLS.PhysicalProductPreparation.smoothClass hu) n ∧ ∀ t : ℝ,
    w (QuantumNLS.PhysicalProductPreparation.smoothClass ((F.ham r hr u hu).2.2 t).1) n =
      Complex.exp (-((t * ω : ℝ) : ℂ) * Complex.I) *
        w (QuantumNLS.PhysicalProductPreparation.smoothClass hu) n

/-- The existing transfer shift, transported to the Bethe array indexing. -/
def shifted {N : ℕ} (a b : ℤ) (m : MArr N)
    (h : DonorOK a (marrArr N m).1) : MArr N :=
  (marrArr N).symm (shiftArr a b (marrArr N m) h)

/-- DEF-033: receiver-minus-donor charge eigenvalue difference. -/
def adjacentDifference (L κ : ℝ) (N r : ℕ) (a b : ℤ) (m : MArr N)
    (h : DonorOK a (marrArr N m).1) : ℝ :=
  eigenvalue L N (κ / N) r (shifted a b m h) - eigenvalue L N (κ / N) r m

/-- The target of the adjacent difference at positive-action endpoints. -/
def frequencyTarget (ω : ℤ → ℝ) (a b : ℤ) : ℝ := ω b - ω a

/-- Each limit must choose a value on the missing-donor sector. -/
def extendedDifference (L κ : ℝ) (N r : ℕ) (a b : ℤ)
    (missing : MArr N → ℝ) (m : MArr N) : ℝ :=
  if h : DonorOK a (marrArr N m).1 then adjacentDifference L κ N r a b m h else missing m

theorem extendedDifference_occupied (L κ : ℝ) (N r : ℕ) (a b : ℤ)
    (missing : MArr N → ℝ) (m : MArr N) (h : DonorOK a (marrArr N m).1) :
    extendedDifference L κ N r a b missing m = adjacentDifference L κ N r a b m h := by
  simp [extendedDifference, h]

theorem extendedDifference_missing (L κ : ℝ) (N r : ℕ) (a b : ℤ)
    (missing : MArr N → ℝ) (m : MArr N) (h : ¬ DonorOK a (marrArr N m).1) :
    extendedDifference L κ N r a b missing m = missing m := by
  simp [extendedDifference, h]

/-- Convergence in the original product Born law on every array, including the
explicitly prescribed missing-donor sector. This is a predicate, not a limit claim. -/
def BornDifferenceConverges {L : ℝ} [Fact (0 < L)] (κ : ℝ)
    (basis : ∀ N, BetheBasis L N) (u : QuantumNLS.PhysicalTensor.L2T L)
    (r : ℕ) (a b : ℤ) (ω : ℤ → ℝ) (missing : ∀ N, MArr N → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ =>
    ∑' m : MArr N, if ε < |extendedDifference L κ N r a b (missing N) m - frequencyTarget ω a b|
      then ENNReal.ofReal (bornLaw (basis N) u m) else 0) atTop (𝓝 0)

/-- DEF-044's reflected hierarchy coordinate, on the actual coordinate carrier. -/
def reflected (w : QuantumNLS.QuantumFourierSpecification.Coordinates) (j : ℤ) : ℂ :=
  (Real.sqrt 2 : ℂ) * w (-j)

/-- The reflected normalization gives the second action formula. -/
theorem reflected_action (w : QuantumNLS.QuantumFourierSpecification.Coordinates) (n : ℤ) :
    ‖reflected w (-n)‖ ^ 2 / 2 = ‖w n‖ ^ 2 := by
  simp only [reflected, neg_neg, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- DEF-044's literal exact-action requirement for a proposed chart and actions. -/
def ExactAction {L : ℝ} [Fact (0 < L)]
    (w : QuantumNLS.QuantumFourierSpecification.PhysicalField L →
      QuantumNLS.QuantumFourierSpecification.Coordinates)
    (action : QuantumNLS.QuantumFourierSpecification.PhysicalField L → ℤ → ℝ) : Prop :=
  ∀ u n, action u n = ‖w u n‖ ^ 2 ∧ action u n = ‖reflected (w u) (-n)‖ ^ 2 / 2

/-- The same requirement using the existing indexed action data. -/
def IndexedExactAction {L κ : ℝ} [Fact (0 < L)]
    (D : QuantumNLS.IndexedMassProperness.IndexedMassData L κ)
    (w : QuantumNLS.QuantumFourierSpecification.PhysicalField L →
      QuantumNLS.QuantumFourierSpecification.Coordinates) : Prop :=
  ExactAction w D.seq

/-- The existing chart specification supplies both action formulas. -/
theorem indexedExactAction_of_specification {L κ : ℝ} [Fact (0 < L)]
    (D : QuantumNLS.IndexedMassProperness.IndexedMassData L κ)
    (w : QuantumNLS.QuantumFourierSpecification.PhysicalField L →
      QuantumNLS.QuantumFourierSpecification.Coordinates)
    (h : QuantumNLS.QuantumFourierSpecification.Specification D w) : IndexedExactAction D w := by
  intro u n
  have ha := (QuantumNLS.QuantumFourierSpecification.exact_action D w h u n).symm
  exact ⟨ha, ha.trans (reflected_action (w u) n).symm⟩

/-- The scalar and full-mass measure depend only on the indexed actions.
The candidate scalar and measure must be supplied by their constructions. -/
def ActionDeterminesScalarAndMeasure {L κ : ℝ} [Fact (0 < L)]
    (D : QuantumNLS.IndexedMassProperness.IndexedMassData L κ)
    (scalar : QuantumNLS.QuantumFourierSpecification.PhysicalField L → ℂ → ℂ)
    (M : QuantumNLS.QuantumFourierSpecification.PhysicalField L → Measure ℝ) : Prop :=
  ∀ u v, (∀ n, D.seq u n = D.seq v n) → scalar u = scalar v ∧ M u = M v

/-- DEF-035, with possibly different probability spaces per particle number:
the tail expectations use the extended nonnegative integral so that infinite
moments are not silently converted to zero. -/
def UniformPowerTail {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ≥0∞) (p : ℝ) : Prop :=
  Tendsto (fun R : ℝ => ⨆ n, ∫⁻ x, (if ENNReal.ofReal R < (X n x) ^ p then (X n x) ^ p else 0) ∂(μ n))
    atTop (𝓝 0)

/-- Uniform tail tightness of real fluctuations; no limiting distribution is specified. -/
def UniformlyTightFluctuations {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ n, μ n {x | K < |Y n x|} ≤ ε

/-- A common-probability-space version of the moment implication, applied to
the powered random variables themselves. -/
theorem moment_convergence_common_space {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (G : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hui : UniformIntegrable G 1 μ) (hprob : TendstoInMeasure μ G atTop g) :
    Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hg : Integrable g μ := hui.integrable_of_tendstoInMeasure hprob
  apply tendsto_integral_of_L1' g
  · exact Filter.Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hui.memLp n))
  · exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      (fun n => (hui.memLp n).aestronglyMeasurable)
      (memLp_one_iff_integrable.mpr hg) hui.unifIntegrable hprob

/-- For natural moments, convergence in probability of the original random
variables implies convergence of their powers; Vitali then gives the moments. -/
theorem natural_moment_convergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (p : ℕ)
    (hui : UniformIntegrable (fun n x => X n x ^ p) 1 μ)
    (hprob : TendstoInMeasure μ X atTop Y) :
    Tendsto (fun n => ∫ x, X n x ^ p ∂μ) atTop (𝓝 (∫ x, Y x ^ p ∂μ)) := by
  apply moment_convergence_common_space μ _ _ hui
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hui.memLp n).aestronglyMeasurable)).2
  intro ns hns
  obtain ⟨ns', hns', h⟩ := (hprob.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  filter_upwards [h] with x hx
  exact ((continuous_id.pow p).tendsto (Y x)).comp hx

#print axioms indexedExactAction_of_specification
#print axioms reflected_action
#print axioms natural_moment_convergence
#print axioms moment_convergence_common_space
#print axioms extendedDifference_occupied
#print axioms extendedDifference_missing

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.TerraMultiRound12Definitions." then
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
  Lean.logInfo m!"TerraMultiRound12Definitions audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

end QuantumNLS.TerraMultiRound12Definitions
