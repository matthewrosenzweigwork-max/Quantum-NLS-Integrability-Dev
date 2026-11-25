import QuantumNLS.TerraMultiRound12Physical
import QuantumNLS.ChartFrequencies
import QuantumNLS.EmpiricalRapidity

/-! DEF-033: receiver minus donor, original Born law, and the active real
frequency convention. Earlier frozen definition modules are imported read-only.
No adjacent asymptotic limit is asserted by this definition. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal
namespace QuantumNLS.Def033CoreR24m
open QuantumNLS.BetheLabels QuantumNLS.Occupation
open QuantumNLS.BetheSpectralCharges QuantumNLS.BetheCoefficientTransform
open QuantumNLS.TerraMultiRound12Definitions

/-- The signed real-time character in the source convention. -/
def phase (t ω : ℝ) : ℂ := Complex.exp (-((t * ω : ℝ) : ℂ) * Complex.I)

/-- Active frequency is meaningful only on a nonzero coordinate. -/
def ActiveFrequency (z : ℝ → ℂ) (z₀ : ℂ) (ω : ℝ) : Prop :=
  z₀ ≠ 0 ∧ ∀ t, z t = phase t ω * z₀

/-- Equality for all real times fixes a real active frequency, with no 2π ambiguity. -/
theorem activeFrequency_unique {z : ℝ → ℂ} {z₀ : ℂ} {a b : ℝ}
    (ha : ActiveFrequency z z₀ a) (hb : ActiveFrequency z z₀ b) : a = b := by
  apply QuantumNLS.ChartFrequencies.freq_eq_of_char_eq ha.1
  intro t
  simpa only [phase, mul_comm (-Complex.I), neg_mul, mul_neg] using (ha.2 t).symm.trans (hb.2 t)

/-- Positive action supplies precisely the nonzero-coordinate requirement. -/
theorem nonzero_of_action {z : ℂ} {a : ℝ} (h : ‖z‖ ^ 2 = a) (ha : 0 < a) : z ≠ 0 := by
  intro hz
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  linarith

/-- The target orientation is receiver minus donor. -/
def target (ω : ℤ → ℝ) (a b : ℤ) : ℝ := ω b - ω a

theorem target_eq (ω : ℤ → ℝ) (a b : ℤ) : target ω a b = frequencyTarget ω a b := rfl

theorem target_reverse (ω : ℤ → ℝ) (a b : ℤ) : target ω b a = -target ω a b := by
  unfold target; ring

theorem target_self (ω : ℤ → ℝ) (a : ℤ) : target ω a a = 0 := sub_self _

/-- The diagonal-quantum phase ratio has this same receiver-minus-donor sign. -/
theorem phase_difference (t receiver donor : ℝ) :
    phase t receiver / phase t donor = phase t (receiver - donor) := by
  rw [phase, phase, phase, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- Physical original product Born measure, at positive particle number N+1.
No conditioning, packet replacement, or discarded missing-donor sector occurs. -/
def originalBorn {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (N : ℕ) : Measure (MArr (N + 1)) :=
  QuantumNLS.EmpiricalRapidity.bornMeasure
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) u hu

instance originalBorn_probability {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    IsProbabilityMeasure (originalBorn hκ u hu N) := by unfold originalBorn; infer_instance

/-- Exact original-law singleton weights, fixing the Born law convention. -/
theorem originalBorn_singleton {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (N : ℕ) (m : MArr (N + 1)) :
    originalBorn hκ u hu N {m} = ENNReal.ofReal (bornLaw
      (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) u m) :=
  QuantumNLS.EmpiricalRapidity.bornMeasure_singleton _ u hu m

/-- The actual adjacent quantum difference, already defined in the frozen module. -/
abbrev difference := adjacentDifference

/-- Every total random variable must explicitly choose the missing-donor value. -/
abbrev withMissing := extendedDifference

/-- A limit statement in the original marginals. A deterministic target requires
no identification of the varying occupation spaces. This definition does not prove a limit. -/
def DifferenceLimit {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
    (r : ℕ) (a b : ℤ) (ω : ℤ → ℝ) (missing : ∀ N, MArr (N + 1) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => originalBorn hκ u hu N
    {m | ε < |withMissing L κ (N + 1) r a b (missing N) m - target ω a b|}) atTop (𝓝 0)

/-- Original-measure formulation equals the earlier frozen Born-weight formulation. -/
theorem differenceLimit_iff_frozen {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
    (r : ℕ) (a b : ℤ) (ω : ℤ → ℝ) (missing : ∀ N, MArr (N + 1) → ℝ) :
    DifferenceLimit hκ u hu r a b ω missing ↔
      QuantumNLS.TerraMultiRound12Physical.PhysicalBornDifferenceConverges κ hκ u r a b ω missing := by
  unfold DifferenceLimit QuantumNLS.TerraMultiRound12Physical.PhysicalBornDifferenceConverges
  simp only [originalBorn, QuantumNLS.EmpiricalRapidity.bornMeasure, PMF.toMeasure_apply_eq_tsum,
    Set.indicator_apply, Set.mem_ofPred_eq, bornPMF_apply, target, frequencyTarget, withMissing]
  rfl

/-- Under an occupied donor, the missing-sector convention does not affect the difference. -/
theorem withMissing_occupied (L κ : ℝ) (N r : ℕ) (a b : ℤ)
    (missing : MArr N → ℝ) (m : MArr N) (h : DonorOK a (marrArr N m).1) :
    withMissing L κ N r a b missing m =
      eigenvalue L N (κ / N) r (shifted a b m h) - eigenvalue L N (κ / N) r m :=
  extendedDifference_occupied L κ N r a b missing m h

theorem withMissing_empty (L κ : ℝ) (N r : ℕ) (a b : ℤ)
    (missing : MArr N → ℝ) (m : MArr N) (h : ¬ DonorOK a (marrArr N m).1) :
    withMissing L κ N r a b missing m = missing m :=
  extendedDifference_missing L κ N r a b missing m h

#print axioms differenceLimit_iff_frozen
#print axioms activeFrequency_unique
#print axioms nonzero_of_action
#print axioms phase_difference
#print axioms originalBorn_singleton
#print axioms withMissing_occupied
#print axioms withMissing_empty
end QuantumNLS.Def033CoreR24m
