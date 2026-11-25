import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Measure.CountableSupport
import NlsGge.Weights.UniformSymbolBound38

/-! # S03 (v2 `A:lem:remainderconvergence`), part 1: the Gaussian reference layer

Claim packet `blueprint/claims/S03.md`, sub-claims S03.01 and S03.02; v2 lines 313-336 and 372.

Everything here is Birkhoff-free (no `B`); it concerns `γ_W = fullWeightSequenceGaussian c`, the
countable product of proper complex Gaussians with density `(a_n/π) e^{-a_n |z|²}` (real-component
variance `1/(2 a_n)`), `a_n = W(2πn) = fullWeightRate c n`, every integer coordinate (zero mode
included) retained.

Weights: `1 ≤ c_j ≤ 2` of v2 `eq:weight` is read in the larger class `0 < lower ≤ c_j ≤ upper`
(v2 l.80: "all full-weight arguments below also apply with `1,2` replaced by arbitrary fixed bounds
`0 < c_- ≤ c_+`").
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure
open scoped ENNReal

/-- The tail weight `a_n ⟨n⟩^{-3/2}` of v2 `eq:tailsum`. -/
def tailWeight38 (c : ℕ → ℝ) (n : ℤ) : ℝ := fullWeightRate c n * japaneseBracket n ^ (-(3 / 2) : ℝ)

/-- The Sobolev weight `⟨n⟩^{2m}` of `h^m` (v2 `A:eq:Gaussianregularity`). -/
def sobolevWeight38 (m : ℕ) (n : ℤ) : ℝ := japaneseBracket n ^ (2 * (m : ℝ))

theorem tailWeight38_nonneg (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (n : ℤ) :
    0 ≤ tailWeight38 c n :=
  mul_nonneg (fullWeightRate_pos lower upper c hlower hbound hupper n).le
    (Real.rpow_nonneg (japaneseBracket_pos n).le _)

theorem sobolevWeight38_nonneg (m : ℕ) (n : ℤ) : 0 ≤ sobolevWeight38 m n :=
  Real.rpow_nonneg (japaneseBracket_pos n).le _

theorem summable_tailWeight_div38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    Summable (fun n : ℤ => tailWeight38 c n / fullWeightRate c n) := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  refine (summable_japaneseBracket_rpow_neg (3 / 2) (by norm_num)).congr (fun n => ?_)
  unfold tailWeight38
  rw [mul_div_cancel_left₀ _ (hq n).ne']
  simp only [Real.rpow_eq_pow]

/-! ### S03.01 -/

/-- **S03.01 / v2 `A:eq:Gaussianregularity`.** For every `m`, `∑ ⟨n⟩^{2m}/a_n < ∞`, the nonnegative
extended-real weighted energy has finite `γ_W`-integral, and the expectation of the (real) energy
is `∑_n ⟨n⟩^{2m}/a_n`. The expectation is stated for the real part of the extended energy only
after finiteness. -/
theorem gaussian_sobolev_expectation38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) :
    Summable (fun n : ℤ => sobolevWeight38 m n / fullWeightRate c n) ∧
    (∫⁻ z, sequenceEnergy (sobolevWeight38 m) z ∂(fullWeightSequenceGaussian c)) ≠ ⊤ ∧
    Integrable (fun z => (sequenceEnergy (sobolevWeight38 m) z).toReal)
      (fullWeightSequenceGaussian c) ∧
    (∫ z, (sequenceEnergy (sobolevWeight38 m) z).toReal ∂(fullWeightSequenceGaussian c)) =
      ∑' n : ℤ, sobolevWeight38 m n / fullWeightRate c n := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  have hsum : Summable (fun n : ℤ => sobolevWeight38 m n / fullWeightRate c n) :=
    summable_fullWeightRate_invSobolev lower upper c hlower hbound hupper m
  exact ⟨hsum,
    lintegral_sequenceEnergy_ne_top (fullWeightRate c) (sobolevWeight38 m) hq
      (sobolevWeight38_nonneg m) hsum,
    integrable_sequenceEnergy_toReal (fullWeightRate c) (sobolevWeight38 m) hq
      (sobolevWeight38_nonneg m) hsum,
    integral_sequenceEnergy_toReal (fullWeightRate c) (sobolevWeight38 m) hq
      (sobolevWeight38_nonneg m) hsum⟩

/-- **S03.01 / v2 `A:eq:tailsum`.** `E_{γ_W} ∑ a_n|z_n|²⟨n⟩^{-3/2} = ∑ ⟨n⟩^{-3/2} < ∞`
(nonnegative extended-real sum first; finiteness before the real value). -/
theorem gaussian_tail_expectation38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    Summable (fun n : ℤ => japaneseBracket n ^ (-(3 / 2) : ℝ)) ∧
    (∫⁻ z, sequenceEnergy (tailWeight38 c) z ∂(fullWeightSequenceGaussian c)) ≠ ⊤ ∧
    Integrable (fun z => (sequenceEnergy (tailWeight38 c) z).toReal)
      (fullWeightSequenceGaussian c) ∧
    (∫ z, (sequenceEnergy (tailWeight38 c) z).toReal ∂(fullWeightSequenceGaussian c)) =
      ∑' n : ℤ, japaneseBracket n ^ (-(3 / 2) : ℝ) := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  have hw := tailWeight38_nonneg lower upper c hlower hbound hupper
  have hsum := summable_tailWeight_div38 lower upper c hlower hbound hupper
  have hdiv : ∀ n : ℤ, tailWeight38 c n / fullWeightRate c n =
      japaneseBracket n ^ (-(3 / 2) : ℝ) := fun n => by
    unfold tailWeight38; rw [mul_div_cancel_left₀ _ (hq n).ne']
  refine ⟨(summable_japaneseBracket_rpow_neg (3 / 2) (by norm_num)).congr (fun n => by
      simp only [Real.rpow_eq_pow]),
    lintegral_sequenceEnergy_ne_top (fullWeightRate c) (tailWeight38 c) hq hw hsum,
    integrable_sequenceEnergy_toReal (fullWeightRate c) (tailWeight38 c) hq hw hsum, ?_⟩
  exact (integral_sequenceEnergy_toReal (fullWeightRate c) (tailWeight38 c) hq hw hsum).trans
    (tsum_congr hdiv)

/-! ### S03.02 -/

/-- The probability-one set of v2's proof: `z ∈ ⋂_m h^m` and the series of `A:eq:tailsum` is finite.
It is defined before, and independently of, any exhaustion. -/
def Omega038 (c : ℕ → ℝ) : Set (ℤ → ℂ) :=
  {z | (∀ m : ℕ, SobolevSquareSummable (m : ℝ) z) ∧
    Summable (fun n : ℤ => tailWeight38 c n * ‖z n‖ ^ 2)}

theorem measurableSet_Omega038 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    MeasurableSet (Omega038 c) := by
  have h1 : MeasurableSet {z : ℤ → ℂ | ∀ m : ℕ, SobolevSquareSummable (m : ℝ) z} := by
    have : {z : ℤ → ℂ | ∀ m : ℕ, SobolevSquareSummable (m : ℝ) z} =
        ⋂ m : ℕ, {z : ℤ → ℂ | Summable (fun n : ℤ => sobolevWeight38 m n * ‖z n‖ ^ 2)} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_iInter, SobolevSquareSummable, sobolevWeight38,
        Real.rpow_eq_pow]
    rw [this]
    exact MeasurableSet.iInter fun m =>
      measurableSet_sequenceSummable _ (sobolevWeight38_nonneg m)
  exact h1.inter (measurableSet_sequenceSummable _
    (tailWeight38_nonneg lower upper c hlower hbound hupper))

/-- **S03.02.** Full smooth sequence support and almost-sure summability of
`a_n|z_n|²⟨n⟩^{-3/2}`: `γ_W(Ω₀ᶜ) = 0`, with `Ω₀` measurable. -/
theorem ae_mem_Omega038 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ z ∂(fullWeightSequenceGaussian c), z ∈ Omega038 c := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  have h1 : ∀ᵐ z ∂(fullWeightSequenceGaussian c), ∀ m : ℕ, SobolevSquareSummable (m : ℝ) z :=
    ae_fullWeightSequenceGaussian_allSobolev lower upper c hlower hbound hupper
  have h2 : ∀ᵐ z ∂(fullWeightSequenceGaussian c),
      Summable (fun n : ℤ => tailWeight38 c n * ‖z n‖ ^ 2) :=
    ae_sequenceSummable (fullWeightRate c) (tailWeight38 c) hq
      (tailWeight38_nonneg lower upper c hlower hbound hupper)
      (summable_tailWeight_div38 lower upper c hlower hbound hupper)
  filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩

theorem fullWeightSequenceGaussian_Omega038_compl (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    fullWeightSequenceGaussian c (Omega038 c)ᶜ = 0 :=
  ae_iff.1 (ae_mem_Omega038 lower upper c hlower hbound hupper)

end NlsGge.Birkhoff
end
