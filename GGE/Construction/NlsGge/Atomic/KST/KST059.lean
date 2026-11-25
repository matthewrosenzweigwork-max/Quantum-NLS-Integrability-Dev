import NlsGge.Atomic.KST.KST058
import NlsGge.Atomic.KST.KST002
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.Sobolev.PeriodicBridge

namespace NlsGge.Atomic.KST059

open NlsGge.Atomic.KST001 NlsGge.Atomic.KST NlsGge.Pilot
open Filter
open scoped ENNReal Topology

noncomputable def weightedGapEnergy (ω : ℤ → ℝ) (γ : ℤ → ℂ) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2)

noncomputable def combinedEnergyTerm (φ : PeriodicPair) (ω : ℤ → ℝ)
    (γ : ℤ → ℂ) (n : ℤ) : ℝ :=
  ‖physicalFourier φ.1 n‖ ^ 2 + ‖physicalFourier φ.2 n‖ ^ 2 +
    ω (2 * n) ^ 2 * ‖γ n‖ ^ 2

noncomputable def combinedSequence (φ : PeriodicPair) (ω : ℤ → ℝ)
    (γ : ℤ → ℂ) (n : ℤ) : ℂ :=
  (Real.sqrt (combinedEnergyTerm φ ω γ n) : ℂ)

noncomputable def actualGapSequence (φ : PeriodicPair) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamPlus φ n - NlsGge.GK38.lamMinus φ n

def SlowUnboundedWeight (w : ℤ → ℝ) : Prop :=
  SlowWeight w 2 ∧ w 0 = 1 ∧
    Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop ∧
    ∀ k : ℤ, k ≠ 0 → w k ≤ 2 * w 1 * (k.natAbs : ℝ)

theorem combinedEnergyTerm_nonneg
    (φ : PeriodicPair) (ω : ℤ → ℝ) (γ : ℤ → ℂ) (n : ℤ) :
    0 ≤ combinedEnergyTerm φ ω γ n := by
  unfold combinedEnergyTerm
  positivity

theorem combinedSequence_norm_sq
    (φ : PeriodicPair) (ω : ℤ → ℝ) (γ : ℤ → ℂ) (n : ℤ) :
    ‖combinedSequence φ ω γ n‖ ^ 2 = combinedEnergyTerm φ ω γ n := by
  unfold combinedSequence
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (combinedEnergyTerm_nonneg φ ω γ n)]

theorem summable_field_sq (u : PhysicalL2) :
    Summable (fun n : ℤ => ‖physicalFourier u n‖ ^ 2) := by
  have hm : Memℓp (physicalFourier u) 2 := by
    have e : (physicalFourierL2 u : ℤ → ℂ) = physicalFourier u :=
      funext (physicalFourierL2_apply u)
    rw [← e]
    exact (physicalFourierL2 u).2
  have hs := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).1 hm
  simpa [Real.rpow_two] using hs

theorem summable_weighted_gap (ω : ℤ → ℝ) (γ : ℤ → ℂ)
    (hγ : weightedGapEnergy ω γ < ⊤) :
    Summable (fun n : ℤ => ω (2 * n) ^ 2 * ‖γ n‖ ^ 2) := by
  have hne : ∑' n : ℤ, ENNReal.ofReal (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2) ≠ ⊤ := by
    unfold weightedGapEnergy at hγ
    exact hγ.ne
  have h := ENNReal.summable_toReal hne
  have e : (fun n : ℤ => (ENNReal.ofReal (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2)).toReal) =
      fun n : ℤ => ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 := by
    funext n
    exact ENNReal.toReal_ofReal (by positivity)
  rw [e] at h
  exact h

theorem combinedSequence_memℓp
    (φ : PeriodicPair) (ω : ℤ → ℝ) (γ : ℤ → ℂ)
    (hγ : weightedGapEnergy ω γ < ⊤) :
    Memℓp (combinedSequence φ ω γ) 2 := by
  apply memℓp_gen
  have e : ∀ n : ℤ, ‖combinedSequence φ ω γ n‖ ^ (2 : ℝ≥0∞).toReal =
      combinedEnergyTerm φ ω γ n := by
    intro n
    rw [ENNReal.toReal_ofNat, Real.rpow_two, combinedSequence_norm_sq]
  simp only [e]
  exact ((summable_field_sq φ.1).add (summable_field_sq φ.2)).add
    (summable_weighted_gap ω γ hγ)

theorem one_common_weight_producer
    (φ : PeriodicPair) (ω : ℤ → ℝ) (γ : ℤ → ℂ)
    (hγ : weightedGapEnergy ω γ < ⊤) :
    ∃ c : ℕ → ℝ,
      SlowUnboundedWeight (dyadicAuxiliaryWeight c) ∧
      Summable (fun n : ℤ =>
        combinedEnergyTerm φ ω γ n * dyadicAuxiliaryWeight c n ^ 2) := by
  obtain ⟨c, -, -, -, -, hslow, hzero, htop, hsum, hbound⟩ :=
    auxiliaryWeight_exists (combinedSequence_memℓp φ ω γ hγ)
  refine ⟨c, ⟨hslow, hzero, htop, hbound⟩, ?_⟩
  have e : ∀ n : ℤ, ‖combinedSequence φ ω γ n‖ ^ 2 * dyadicAuxiliaryWeight c n ^ 2 =
      combinedEnergyTerm φ ω γ n * dyadicAuxiliaryWeight c n ^ 2 := by
    intro n
    rw [combinedSequence_norm_sq]
  simpa only [e] using hsum

theorem common_weight_components
    (φ : PeriodicPair) (ω w : ℤ → ℝ) (γ : ℤ → ℂ)
    (hs : Summable (fun n : ℤ => combinedEnergyTerm φ ω γ n * w n ^ 2)) :
    Summable (fun n : ℤ => ‖physicalFourier φ.1 n‖ ^ 2 * w n ^ 2) ∧
    Summable (fun n : ℤ => ‖physicalFourier φ.2 n‖ ^ 2 * w n ^ 2) ∧
    Summable (fun n : ℤ => ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2) := by
  refine ⟨Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs,
    Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs,
    Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs⟩
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold combinedEnergyTerm
    have h2 := sq_nonneg ‖physicalFourier φ.2 n‖
    have h3 : 0 ≤ ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 := by positivity
    linarith
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold combinedEnergyTerm
    have h1 := sq_nonneg ‖physicalFourier φ.1 n‖
    have h3 : 0 ≤ ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 := by positivity
    linarith
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold combinedEnergyTerm
    have h1 := sq_nonneg ‖physicalFourier φ.1 n‖
    have h2 := sq_nonneg ‖physicalFourier φ.2 n‖
    linarith

theorem doubled_weight_sq_le
    (w : ℤ → ℝ) (hw : SlowWeight w 2) (n : ℤ) :
    w (2 * n) ^ 2 ≤ 4 * w n ^ 2 := by
  have h1 : 0 ≤ w (2 * n) := le_trans zero_le_one (hw.one_le _)
  have h2 : w (2 * n) ≤ 2 * w n := hw.doubling n
  have h3 : 0 ≤ w n := le_trans zero_le_one (hw.one_le n)
  nlinarith [h1, h2, h3]


theorem weighted_field_finite
    (φ : PeriodicPair) (w : ℤ → ℝ) (hw : SlowWeight w 2)
    (h₁ : Summable (fun n : ℤ => ‖physicalFourier φ.1 n‖ ^ 2 * w n ^ 2))
    (h₂ : Summable (fun n : ℤ => ‖physicalFourier φ.2 n‖ ^ 2 * w n ^ 2)) :
    weightedNormSq₂ w φ < ⊤ := by
  have hinj : Function.Injective (fun m : ℤ => 2 * m) := fun a b h => by
    simp only at h
    omega
  set F : ℤ → ℝ≥0∞ := fun k => weightedPairMode w k (periodTwoPairCoeff φ k) with hF
  have hsupp : Function.support F ⊆ Set.range (fun m : ℤ => 2 * m) := by
    intro k hk
    by_contra hne
    apply hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hne ⟨k / 2, by simp only; omega⟩
    simp only [hF, periodOne_pair_odd_coeff_zero φ k hodd, weightedPairMode]
    simp
  have key := hinj.tsum_eq hsupp
  unfold weightedNormSq₂
  rw [← key]
  have hterm : ∀ c : ℤ, F (2 * c) ≤ ENNReal.ofReal
      (4 * (‖physicalFourier φ.1 c‖ ^ 2 * w c ^ 2) +
        4 * (‖physicalFourier φ.2 c‖ ^ 2 * w c ^ 2)) := by
    intro c
    simp only [hF]
    unfold weightedPairMode
    rw [periodOne_pair_even_coeff φ c]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hAB : (0 : ℝ) ≤ ‖physicalFourier φ.1 c‖ ^ 2 + ‖physicalFourier φ.2 c‖ ^ 2 := by
      positivity
    have hm := mul_le_mul_of_nonneg_right (doubled_weight_sq_le w hw c) hAB
    nlinarith [hm]
  have hsum : Summable (fun c : ℤ =>
      4 * (‖physicalFourier φ.1 c‖ ^ 2 * w c ^ 2) +
        4 * (‖physicalFourier φ.2 c‖ ^ 2 * w c ^ 2)) :=
    (h₁.mul_left 4).add (h₂.mul_left 4)
  calc ∑' c : ℤ, F (2 * c)
      ≤ ∑' c : ℤ, ENNReal.ofReal
          (4 * (‖physicalFourier φ.1 c‖ ^ 2 * w c ^ 2) +
            4 * (‖physicalFourier φ.2 c‖ ^ 2 * w c ^ 2)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' c : ℤ,
          (4 * (‖physicalFourier φ.1 c‖ ^ 2 * w c ^ 2) +
            4 * (‖physicalFourier φ.2 c‖ ^ 2 * w c ^ 2))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun c => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem weighted_gaps_finite
    (ω w : ℤ → ℝ) (γ : ℤ → ℂ) (hw : SlowWeight w 2)
    (hγ : Summable
      (fun n : ℤ => ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2)) :
    weightedGapEnergy (fun k => w k * ω k) γ < ⊤ := by
  unfold weightedGapEnergy
  have hterm : ∀ n : ℤ, ENNReal.ofReal ((w (2 * n) * ω (2 * n)) ^ 2 * ‖γ n‖ ^ 2) ≤
      ENNReal.ofReal (4 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2)) := by
    intro n
    apply ENNReal.ofReal_le_ofReal
    have hn := mul_le_mul_of_nonneg_right (doubled_weight_sq_le w hw n)
      (by positivity : (0 : ℝ) ≤ ω (2 * n) ^ 2 * ‖γ n‖ ^ 2)
    calc (w (2 * n) * ω (2 * n)) ^ 2 * ‖γ n‖ ^ 2
        = w (2 * n) ^ 2 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2) := by ring
      _ ≤ 4 * w n ^ 2 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2) := hn
      _ = 4 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2) := by ring
  have hsum : Summable (fun n : ℤ => 4 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2)) :=
    hγ.mul_left 4
  calc ∑' n : ℤ, ENNReal.ofReal ((w (2 * n) * ω (2 * n)) ^ 2 * ‖γ n‖ ^ 2)
      ≤ ∑' n : ℤ, ENNReal.ofReal (4 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : ℤ, 4 * (ω (2 * n) ^ 2 * ‖γ n‖ ^ 2 * w n ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem exists_common_auxiliary_weight
    (φ : PeriodicPair) (ω : ℤ → ℝ) (hω : EvenWeight ω)
    (γ : ℤ → ℂ) (hγ : weightedGapEnergy ω γ < ⊤) :
    ∃ c : ℕ → ℝ,
      let w := dyadicAuxiliaryWeight c
      SlowUnboundedWeight w ∧
      weightedNormSq₂ w φ < ⊤ ∧
      weightedGapEnergy (fun k => w k * ω k) γ < ⊤ := by
  obtain ⟨c, hc, hs⟩ := one_common_weight_producer φ ω γ hγ
  refine ⟨c, hc, ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := common_weight_components φ ω (dyadicAuxiliaryWeight c) γ hs
  exact ⟨weighted_field_finite φ _ hc.1 h₁ h₂, weighted_gaps_finite ω _ γ hc.1 h₃⟩

theorem exists_common_auxiliary_weight_actual
    (φ : PeriodicPair) (ω : ℤ → ℝ) (hω : EvenWeight ω)
    (hγ : weightedGapEnergy ω (actualGapSequence φ) < ⊤) :
    ∃ c : ℕ → ℝ,
      let w := dyadicAuxiliaryWeight c
      SlowUnboundedWeight w ∧
      weightedNormSq₂ w φ < ⊤ ∧
      weightedGapEnergy (fun k => w k * ω k) (actualGapSequence φ) < ⊤ := by
  obtain ⟨c, hc, hs⟩ := one_common_weight_producer φ ω (actualGapSequence φ) hγ
  refine ⟨c, hc, ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := common_weight_components φ ω (dyadicAuxiliaryWeight c) (actualGapSequence φ) hs
  exact ⟨weighted_field_finite φ _ hc.1 h₁ h₂, weighted_gaps_finite ω _ (actualGapSequence φ) hc.1 h₃⟩

theorem common_weight_physical_realization
    (φ : PeriodicPair) (w : ℤ → ℝ)
    (hw : SlowUnboundedWeight w) (hφ : weightedNormSq₂ w φ < ⊤) :
    let hEven : EvenWeight w := ⟨hw.1.one_le, hw.1.even⟩
    letI : Fact (∀ m : ℤ, 0 <
        NlsGge.Atomic.KST002.periodOneWeight w m ^ 2) :=
      ⟨fun m => sq_pos_of_pos
        (lt_of_lt_of_le zero_lt_one (hw.1.one_le (2 * m)))⟩
    ∃ x : NlsGge.Atomic.KST002.WeightedPairHilbert
        (NlsGge.Atomic.KST002.periodOneWeight w),
      NlsGge.Atomic.KST002.periodOnePhysicalPair w hEven x = φ := by
  intro hEven
  exact NlsGge.Atomic.KST002.periodOnePhysicalPair_exists_of_finite_energy w hEven φ hφ

end NlsGge.Atomic.KST059
