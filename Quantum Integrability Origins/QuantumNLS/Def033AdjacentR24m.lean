import QuantumNLS.Def033CoreR24m
import QuantumNLS.SmoothScalarMomentsFormal

/-! Finite adjacent-difference sanity and the missing-donor convention.
Changing that convention preserves probability limits only when the probability
of the missing sector tends to zero. No analogous moment claim is made. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal
namespace QuantumNLS.Def033AdjacentR24m
open QuantumNLS.Def033CoreR24m QuantumNLS.TerraMultiRound12Definitions
open QuantumNLS.BetheLabels QuantumNLS.BetheSpectralCharges QuantumNLS.Occupation
open QuantumNLS.BetheCoefficientTransform

/-- The frozen real Hamiltonian is the literal physical Riccati charge on
smooth data, for every order. Reality is PROVED by the frozen all-order formal
identity, not assumed in place of the physical charge. -/
theorem hamiltonian_is_physical {L κ : ℝ} (hκ : 0 < κ) {u : ℝ → ℂ}
    (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L u) (r : ℕ) :
    ((QuantumNLS.HierarchyFlow.hamiltonian L κ r u : ℝ) : ℂ) =
      QuantumNLS.ClassicalCharges.charge L κ u (r + 1) := by
  apply Complex.ext
  · rfl
  · exact (QuantumNLS.SmoothScalarMomentsFormal.charge_real hκ hu (r + 1)).symm

theorem shifted_self {N : ℕ} (a : ℤ) (m : MArr N) (h : DonorOK a (marrArr N m).1) :
    shifted a a m h = m := by
  apply (marrArr N).injective
  rw [shifted, Equiv.apply_symm_apply]
  apply Subtype.ext
  exact QuantumNLS.Occupation.shift_self h

theorem difference_self (L κ : ℝ) (N r : ℕ) (a : ℤ) (m : MArr N)
    (h : DonorOK a (marrArr N m).1) : difference L κ N r a a m h = 0 := by
  change eigenvalue L N (κ / N) r (shifted a a m h) - eigenvalue L N (κ / N) r m = 0
  rw [shifted_self, sub_self]

/-- Event comparison in the ORIGINAL Born law, with every missing donor retained. -/
theorem event_change_missing {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
    (N r : ℕ) (a b : ℤ) (missing other : MArr (N + 1) → ℝ) (c ε : ℝ) :
    originalBorn hκ u hu N {m | ε < |withMissing L κ (N + 1) r a b missing m - c|} ≤
      originalBorn hκ u hu N {m | ε < |withMissing L κ (N + 1) r a b other m - c|} +
      originalBorn hκ u hu N {m | ¬ DonorOK a (marrArr (N + 1) m).1} := by
  apply le_trans (measure_mono (t :=
    {m | ε < |withMissing L κ (N + 1) r a b other m - c|} ∪
    {m | ¬ DonorOK a (marrArr (N + 1) m).1}) ?_) (measure_union_le _ _)
  intro m hm
  by_cases hd : DonorOK a (marrArr (N + 1) m).1
  · left
    change ε < |withMissing L κ (N + 1) r a b other m - c|
    change ε < |withMissing L κ (N + 1) r a b missing m - c| at hm
    simpa only [withMissing, extendedDifference, hd, ↓reduceDIte] using hm
  · exact Or.inr hd

/-- Probability limits do not depend on a specified missing-sector extension
when that ORIGINAL marginal sector probability tends to zero. -/
theorem limit_change_missing {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
    (r : ℕ) (a b : ℤ) (ω : ℤ → ℝ) (missing other : ∀ N, MArr (N + 1) → ℝ)
    (hother : DifferenceLimit hκ u hu r a b ω other)
    (hmissing : Tendsto (fun N => originalBorn hκ u hu N
      {m | ¬ DonorOK a (marrArr (N + 1) m).1}) atTop (𝓝 0)) :
    DifferenceLimit hκ u hu r a b ω missing := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun N => originalBorn hκ u hu N
      {m | ε < |withMissing L κ (N + 1) r a b (other N) m - target ω a b|} +
      originalBorn hκ u hu N {m | ¬ DonorOK a (marrArr (N + 1) m).1})
    tendsto_const_nhds
  · simpa only [add_zero] using (hother ε hε).add hmissing
  · exact fun _ => bot_le
  · exact fun N => event_change_missing hκ u hu N r a b (missing N) (other N) (target ω a b) ε

#print axioms hamiltonian_is_physical
#print axioms shifted_self
#print axioms difference_self
#print axioms event_change_missing
#print axioms limit_change_missing
end QuantumNLS.Def033AdjacentR24m
