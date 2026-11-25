import NlsGge.Analysis.FullCoverFourier

/-!
# Period-one weighted pair norms in the doubled Fourier convention

The source potential is a pair of actual period-one `L²` classes.  The
natural double cover realizes each component on `AddCircle 2`, whose Haar
Fourier basis is `exp (π i k x)` and whose Haar measure is the normalized
measure `(1/2) ∫₀²`.  Frequencies are enumerated by the bijection
`(m, even) ↦ 2m`, `(m, odd) ↦ 2m+1`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Atomic.KST001

open NlsGge.Pilot NlsGge.Analysis

/-- An actual pair of period-one scalar fields.  Periodicity is built into the
`AddCircle 1` carrier, rather than carried as a representative-level premise. -/
abbrev PeriodicPair := PhysicalL2 × PhysicalL2

/-- The period-two Fourier coefficient of a period-one pair, componentwise. -/
def periodTwoPairCoeff (φ : PeriodicPair) (k : ℤ) : ℂ × ℂ :=
  (fourierCoeff (naturalPhysicalCoverL2 φ.1) k,
   fourierCoeff (naturalPhysicalCoverL2 φ.2) k)

/-- The source weight lower bound and evenness on the integer spectral labels. -/
structure EvenWeight (ω : ℤ → ℝ) : Prop where
  one_le : ∀ k, 1 ≤ ω k
  even : ∀ k, ω (-k) = ω k

/-- Every integer frequency has a unique form `2*m` or `2*m+1`. -/
def integerEvenOddEquiv : ℤ ≃ ℤ × Bool where
  toFun k := (k / 2, decide (k % 2 = 1))
  invFun p := 2 * p.1 + if p.2 then 1 else 0
  left_inv k := by
    dsimp
    have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hmod with hmod | hmod
    · simp [hmod]
      omega
    · simp [hmod]
      omega
  right_inv p := by
    rcases p with ⟨m, b⟩
    cases b
    · simp
    · simp
      omega

/-- The weighted contribution of one period-two Fourier mode of a pair. -/
def weightedPairMode (ω : ℤ → ℝ) (k : ℤ) (c : ℂ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((ω k) ^ 2) *
    (ENNReal.ofReal (‖c.1‖ ^ 2) + ENNReal.ofReal (‖c.2‖ ^ 2))

/-- Weighted square norm over the complete integer period-two spectrum. -/
def weightedNormSq₂ (ω : ℤ → ℝ) (φ : PeriodicPair) : ℝ≥0∞ :=
  ∑' k : ℤ, weightedPairMode ω k (periodTwoPairCoeff φ k)

/-- The weighted square norm on the even period-two modes, indexed by their
period-one labels. -/
def weightedEvenFourierNormSq (ω : ℤ → ℝ) (φ : PeriodicPair) : ℝ≥0∞ :=
  ∑' m : ℤ,
    weightedPairMode ω (2 * m) (physicalFourier φ.1 m, physicalFourier φ.2 m)

/-- The even period-two coefficients are exactly the original period-one
Fourier coefficients; the normalized double-cover map preserves Haar mass. -/
theorem periodOne_pair_even_coeff (φ : PeriodicPair) (m : ℤ) :
    periodTwoPairCoeff φ (2 * m) = (physicalFourier φ.1 m, physicalFourier φ.2 m) := by
  apply Prod.ext
  · exact naturalPhysicalCoverL2_fourier_even φ.1 m
  · exact naturalPhysicalCoverL2_fourier_even φ.2 m

/-- Coefficients of a period-one pair vanish at odd period-two frequencies. -/
theorem periodOne_pair_odd_coeff_zero (φ : PeriodicPair) (k : ℤ)
    (hk : k % 2 ≠ 0) : periodTwoPairCoeff φ k = (0, 0) := by
  apply Prod.ext
  · exact naturalPhysicalCoverL2_fourier_odd φ.1 k hk
  · exact naturalPhysicalCoverL2_fourier_odd φ.2 k hk

/-- Reindexing the full period-two Fourier norm by the unique even and odd
frequency labels. -/
theorem weightedNormSq₂_eq_evenOddSplit (ω : ℤ → ℝ) (φ : PeriodicPair) :
    weightedNormSq₂ ω φ =
      ∑' m : ℤ,
        (weightedPairMode ω (2 * m) (periodTwoPairCoeff φ (2 * m)) +
          weightedPairMode ω (2 * m + 1) (periodTwoPairCoeff φ (2 * m + 1))) := by
  unfold weightedNormSq₂
  calc
    (∑' k : ℤ, weightedPairMode ω k (periodTwoPairCoeff φ k)) =
        ∑' p : ℤ × Bool,
          weightedPairMode ω (integerEvenOddEquiv.symm p)
            (periodTwoPairCoeff φ (integerEvenOddEquiv.symm p)) :=
      by
        simpa using (Equiv.tsum_eq integerEvenOddEquiv
        (fun p : ℤ × Bool => weightedPairMode ω (integerEvenOddEquiv.symm p)
          (periodTwoPairCoeff φ (integerEvenOddEquiv.symm p))))
    _ = ∑' m : ℤ, ∑' b : Bool,
          weightedPairMode ω (integerEvenOddEquiv.symm (m, b))
            (periodTwoPairCoeff φ (integerEvenOddEquiv.symm (m, b))) := by
      rw [ENNReal.tsum_prod']
    _ = _ := by
      apply tsum_congr
      intro m
      simp [integerEvenOddEquiv, weightedPairMode, add_comm]

/-- The odd-mode contribution to the doubled weighted norm is zero. -/
theorem periodOne_pair_odd_weightedMode_zero (ω : ℤ → ℝ)
    (φ : PeriodicPair) (m : ℤ) :
    weightedPairMode ω (2 * m + 1) (periodTwoPairCoeff φ (2 * m + 1)) = 0 := by
  have hk : (2 * m + 1) % 2 ≠ 0 := by omega
  rw [periodOne_pair_odd_coeff_zero φ (2 * m + 1) hk]
  simp [weightedPairMode]

/-- The weighted period-two norm of a period-one pair is exactly its even-mode
Fourier norm.  Its odd coefficients vanish by the actual natural-cover parity
theorem. -/
theorem periodOne_weightedPair_norm (ω : ℤ → ℝ) (φ : PeriodicPair)
    (_hω : EvenWeight ω) :
    weightedNormSq₂ ω φ = weightedEvenFourierNormSq ω φ := by
  rw [weightedNormSq₂_eq_evenOddSplit]
  unfold weightedEvenFourierNormSq
  apply tsum_congr
  intro m
  rw [periodOne_pair_odd_weightedMode_zero ω φ m, add_zero]
  rw [periodOne_pair_even_coeff]

/-- Weighted square-summation over reflected indices is invariant for any pair
sequence when the weight is even. -/
theorem weightedEvenSequenceNormSq_reflect (ω : ℤ → ℝ)
    (hω : EvenWeight ω) (a : ℤ → ℂ × ℂ) :
    (∑' m : ℤ, weightedPairMode ω (2 * m) (a (-m))) =
      ∑' m : ℤ, weightedPairMode ω (2 * m) (a m) := by
  calc
    (∑' m : ℤ, weightedPairMode ω (2 * m) (a (-m))) =
        ∑' m : ℤ, weightedPairMode ω (-(2 * (-m))) (a (-m)) := by
          apply tsum_congr
          intro m
          have hidx : -(2 * (-m)) = 2 * m := by ring
          rw [hidx]
    _ = ∑' m : ℤ, weightedPairMode ω (-(2 * m)) (a m) := by
          change (∑' m : ℤ,
            (fun j => weightedPairMode ω (-(2 * j)) (a j)) (-m)) = _
          exact Equiv.tsum_eq (Equiv.neg ℤ)
            (fun m : ℤ => weightedPairMode ω (-(2 * m)) (a m))
    _ = ∑' m : ℤ, weightedPairMode ω (2 * m) (a m) := by
          apply tsum_congr
          intro m
          unfold weightedPairMode
          rw [hω.even (2 * m)]

/-- Reflection invariance for the actual even Fourier coefficients of a
period-one pair. -/
theorem weightedEvenFourierNormSq_reflect (ω : ℤ → ℝ)
    (hω : EvenWeight ω) (φ : PeriodicPair) :
    (∑' m : ℤ,
      weightedPairMode ω (2 * m) (periodTwoPairCoeff φ (-(2 * m)))) =
      weightedEvenFourierNormSq ω φ := by
  calc
    (∑' m : ℤ,
      weightedPairMode ω (2 * m) (periodTwoPairCoeff φ (-(2 * m)))) =
        ∑' m : ℤ,
          weightedPairMode ω (2 * m)
            ((fun j => periodTwoPairCoeff φ (2 * j)) (-m)) := by
              apply tsum_congr
              intro m
              have hidx : -(2 * m) = 2 * (-m) := by ring
              rw [hidx]
    _ = ∑' m : ℤ,
          weightedPairMode ω (2 * m) (periodTwoPairCoeff φ (2 * m)) :=
      weightedEvenSequenceNormSq_reflect ω hω
        (fun m => periodTwoPairCoeff φ (2 * m))
    _ = weightedEvenFourierNormSq ω φ := by
      unfold weightedEvenFourierNormSq
      apply tsum_congr
      intro m
      rw [periodOne_pair_even_coeff]

end NlsGge.Atomic.KST001
