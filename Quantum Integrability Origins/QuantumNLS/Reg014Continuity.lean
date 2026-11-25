import QuantumNLS.Reg014Moments
import QuantumNLS.FullMassLimit

/-! REG-014 support: continuity of `u ↦ D_{r,u}(Y)` on `H^{r-1}` for every fixed `Y > 0`.
The exact divided-difference recursion expresses `D` through the lower moment corrections
(continuous polynomials, accepted REG-004/REG-007) and the regularized zeroth moments, which are
weakly continuous in the field by the accepted continuity of the measure map. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.Reg014Continuity
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61FiniteDivision
open QuantumNLS.TerraMultiRound62EqualMass QuantumNLS.TerraMultiRound63Division
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.Reg014Moments
open scoped BoundedContinuousFunction

variable {L : ℝ} [Fact (0 < L)]

/-- The retained polynomial corrections are continuous on `H^{r-1}`. -/
theorem retainedR_continuous (κ : ℝ) (r : ℕ) (hr : 2 ≤ r) (j : ℕ) :
    Continuous (fun u : Hk L (r - 1) => retainedR (L := L) r hr κ u j) := by
  by_cases h1 : j = 1
  · have : (fun u : Hk L (r - 1) => retainedR (L := L) r hr κ u j) =
        fun u => R1field (L := L) κ (H02.mono (L := L)
          (show ((1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ r - 1 by omega)) u) := by
      funext u
      unfold retainedR
      simp only [h1, ↓reduceIte]
    rw [this]
    exact (R1field_continuous (L := L) κ).comp (H02.mono (L := L) _).continuous
  · by_cases hj : 2 ≤ j ∧ j ≤ r
    · have : (fun u : Hk L (r - 1) => retainedR (L := L) r hr κ u j) =
          fun u => Rfield (L := L) j hj.1 κ (H02.mono (L := L)
            (show ((j - 1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) by
              exact_mod_cast (show j - 1 ≤ r - 1 by omega)) u) := by
        funext u
        unfold retainedR
        simp only [h1, ↓reduceIte, hj, and_self, ↓reduceDIte]
      rw [this]
      exact (Rfield_continuous (L := L) j hj.1 κ).comp (H02.mono (L := L) _).continuous
    · have : (fun u : Hk L (r - 1) => retainedR (L := L) r hr κ u j) = fun _ => 0 := by
        funext u
        unfold retainedR
        simp only [h1, ↓reduceIte, hj, ↓reduceDIte]
      rw [this]
      exact continuous_const

/-- The inclusion `H^k → L²` is continuous. -/
theorem val_continuous (k : ℕ) : Continuous (fun u : Hk L k => u.val) :=
  (H02.toL2 (L := L) (s := (k : ℝ)) (Nat.cast_nonneg k)).continuous

/-- Weak continuity of the measure map, tested against a bounded continuous function. -/
theorem integral_Mmeas_continuous (κ : ℝ) (hκ : 0 ≤ κ) (f : ℝ →ᵇ ℝ) :
    Continuous (fun w : L2T L => ∫ t, f t ∂(QuantumNLS.FullMass.Mmeas κ w)) := by
  have h1 : Continuous (fun w : L2T L => QuantumNLS.FullMass.Mfin κ w) :=
    (QuantumNLS.FullMassLimit.continuous_Mfin (L := L)).comp
      (continuous_const.prodMk continuous_id :
        Continuous (fun w : L2T L => ((⟨κ, hκ⟩ : {κ : ℝ // 0 ≤ κ}), w)))
  exact (MeasureTheory.FiniteMeasure.continuous_integral_boundedContinuousFunction f).comp h1

/-- The regularized zeroth kernel as a bounded continuous function. -/
def kernelBCF (Y : ℝ) (hY : 0 < Y) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun t => kernel 0 Y t, by
      unfold kernel
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro t
      positivity⟩ 1 (by
    intro x y
    have h0 : ∀ t, 0 ≤ kernel 0 Y t := fun t => kernel_nonneg 0 Y t
    have h1 : ∀ t, kernel 0 Y t ≤ 1 := by
      intro t
      unfold kernel
      rw [div_le_one (by positivity)]
      simp only [mul_zero, pow_zero, mul_one]
      nlinarith [sq_nonneg t]
    show dist (kernel 0 Y x) (kernel 0 Y y) ≤ 1
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [h0 x, h1 y], by linarith [h0 y, h1 x]⟩)

theorem kernelBCF_apply (Y : ℝ) (hY : 0 < Y) (t : ℝ) : kernelBCF Y hY t = kernel 0 Y t := rfl

/-- The regularized zeroth moments of the physical and free measures are continuous in `u`. -/
theorem zeroth_continuous (κ : ℝ) (hκ : 0 < κ) {Y : ℝ} (hY : 0 < Y) (k : ℕ) :
    Continuous (fun u : Hk L k =>
      (∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u.val)) -
        (∫ t, kernel 0 Y t ∂(freeMeasure L u.val))) := by
  have h1 : Continuous (fun u : Hk L k =>
      ∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u.val)) := by
    have := (integral_Mmeas_continuous (L := L) κ hκ.le (kernelBCF Y hY)).comp (val_continuous (L := L) k)
    convert this using 2 with u
    rw [PhysicalL2Normalization.measure_eq_Mmeas]
    rfl
  have h2 : Continuous (fun u : Hk L k =>
      ∫ t, kernel 0 Y t ∂(freeMeasure L u.val)) := by
    have := (integral_Mmeas_continuous (L := L) 0 le_rfl (kernelBCF Y hY)).comp (val_continuous (L := L) k)
    convert this using 2 with u
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    rfl
  exact h1.sub h2

/-- The exact closed formula for `D_{r,u}(Y)`. -/
theorem Dfun_formula (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) (u : Hk L (r - 1)) {Y : ℝ}
    (hY : 0 < Y) :
    Dfun κ hκ r u.val Y = (-(Y ^ 2)) ^ r *
      (((∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u.val)) -
        (∫ t, kernel 0 Y t ∂(freeMeasure L u.val))) -
        ∑ j ∈ Finset.range r, (-(Y ^ 2))⁻¹ ^ j *
          (if j = 0 then 0 else retainedR (L := L) r hr κ u j)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hu := representative_hsq (L := L) (n + 1 - 1) u
  simp only [Nat.add_sub_cancel] at hu
  rw [Dfun_eq_divided κ hκ n hn u.val hY hu]
  have hq : Y ^ 2 ≠ 0 := by positivity
  have hrec := recursive_division (Y ^ 2) hq
    (fun m => (∫ t : ℝ, t ^ (2 * m) ∂(PhysicalQuantumMeasure.measure hκ u.val)) -
      ∫ t : ℝ, t ^ (2 * m) ∂(freeMeasure L u.val))
    (dividedDifference (PhysicalQuantumMeasure.measure hκ u.val) (freeMeasure L u.val) Y)
    (fun m => by simp only [dividedDifference]; ring) n
  rw [hrec]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  by_cases h0 : j = 0
  · subst h0
    rw [physical_free_mass hκ u.val]
    simp
  · simp only [h0, ↓reduceIte]
    rw [moment_diff κ hκ (n + 1) hr u j (by omega) (by omega)]

/-- **Fixed-`Y` continuity.** -/
theorem Dfun_continuous (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun u : Hk L (r - 1) => Dfun κ hκ r u.val Y) := by
  have hform : (fun u : Hk L (r - 1) => Dfun κ hκ r u.val Y) = fun u => (-(Y ^ 2)) ^ r *
      (((∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u.val)) -
        (∫ t, kernel 0 Y t ∂(freeMeasure L u.val))) -
        ∑ j ∈ Finset.range r, (-(Y ^ 2))⁻¹ ^ j *
          (if j = 0 then 0 else retainedR (L := L) r hr κ u j)) :=
    funext (fun u => Dfun_formula κ hκ r hr u hY)
  rw [hform]
  refine continuous_const.mul ((zeroth_continuous κ hκ hY (r - 1)).sub ?_)
  refine continuous_finsetSum _ (fun j _ => continuous_const.mul ?_)
  by_cases h0 : j = 0
  · simp only [h0, ↓reduceIte]
    exact continuous_const
  · simp only [h0, ↓reduceIte]
    exact retainedR_continuous κ r hr j

#print axioms retainedR_continuous
#print axioms zeroth_continuous
#print axioms Dfun_formula
#print axioms Dfun_continuous
end QuantumNLS.Reg014Continuity
