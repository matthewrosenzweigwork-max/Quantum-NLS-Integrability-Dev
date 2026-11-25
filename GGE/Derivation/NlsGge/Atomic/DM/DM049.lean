import NlsGge.Atomic.DM.DM048

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.DM049

open NlsGge.Atomic.DM047
open NlsGge.Atomic.DM048
open NlsGge.Pilot
open Filter
open scoped Topology

/-- The imported genuine PiLp weighted-pair carrier instantiated from an explicit positive amplitude weight. -/
abbrev WeightedPairHilbertOfPositive (w : ℤ → ℝ) (hw : ∀ k, 0 < w k) :=
  @WeightedPairHilbert w ⟨fun k => sq_pos_of_pos (hw k)⟩

/-- Raw coefficients of a positive-weight pair, with the required squared-weight fact derived from positivity. -/
def weightedPairCoefficientsOfPositive (w : ℤ → ℝ) (hw : ∀ k, 0 < w k)
    (x : WeightedPairHilbertOfPositive w hw) : Bool → ℤ → ℂ :=
  @weightedPairCoefficients w ⟨fun k => sq_pos_of_pos (hw k)⟩ x

/-- The actual PiLp Hilbert norm on `WeightedPairHilbertOfPositive`. -/
def weightedPairNormOfPositive (w : ℤ → ℝ) (hw : ∀ k, 0 < w k)
    (x : WeightedPairHilbertOfPositive w hw) : ℝ := by
  letI : Fact (∀ k : ℤ, 0 < w k ^ 2) := ⟨fun k => sq_pos_of_pos (hw k)⟩
  exact ‖x‖

private theorem weightedPairNormOfPositive_eq_sqrt (w : ℤ → ℝ) (hw : ∀ k, 0 < w k)
    (x : WeightedPairHilbertOfPositive w hw) :
    weightedPairNormOfPositive w hw x = Real.sqrt (weightedPairNormOfPositive w hw x ^ 2) := by
  letI : Fact (∀ k : ℤ, 0 < w k ^ 2) := ⟨fun k => sq_pos_of_pos (hw k)⟩
  change ‖x‖ = Real.sqrt (‖x‖ ^ 2)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

private theorem pairComparisonSq (w v : ℤ → ℝ) (C : ℝ)
    (hw : ∀ k, 0 < w k) (hv : ∀ k, 0 < v k)
    (hC : 0 ≤ C) (hcmp : ∀ k, v k ≤ C * w k) :
    ∀ k, v k ^ 2 ≤ C ^ 2 * w k ^ 2 := by
  intro k
  have hnonneg : 0 ≤ C * w k := mul_nonneg hC (hw k).le
  have hs := (sq_le_sq₀ (hv k).le hnonneg).2 (hcmp k)
  simpa [mul_pow] using hs

/-- A coefficient-preserving map between genuine weighted Dirac-pair Hilbert
spaces, built from the project's scalar weighted comparison in both slots. -/
private def pairWeightedComparison (w v : ℤ → ℝ) (C : ℝ)
    (hw : ∀ k, 0 < w k) (hv : ∀ k, 0 < v k)
    (hC : 0 ≤ C) (hcmp : ∀ k, v k ≤ C * w k)
    (x : WeightedPairHilbertOfPositive w hw) : WeightedPairHilbertOfPositive v hv := by
  letI : Fact (∀ k : ℤ, 0 < w k ^ 2) := ⟨fun k => sq_pos_of_pos (hw k)⟩
  letI : Fact (∀ k : ℤ, 0 < v k ^ 2) := ⟨fun k => sq_pos_of_pos (hv k)⟩
  exact WithLp.toLp 2 (fun b =>
    weightedComparison (fun k => w k ^ 2) (fun k => v k ^ 2) (C ^ 2)
      (sq_nonneg C) (pairComparisonSq w v C hw hv hC hcmp) (x b))

private theorem pairWeightedComparison_coefficients (w v : ℤ → ℝ) (C : ℝ)
    (hw : ∀ k, 0 < w k) (hv : ∀ k, 0 < v k)
    (hC : 0 ≤ C) (hcmp : ∀ k, v k ≤ C * w k)
    (x : WeightedPairHilbertOfPositive w hw) :
    weightedPairCoefficientsOfPositive v hv (pairWeightedComparison w v C hw hv hC hcmp x) =
      weightedPairCoefficientsOfPositive w hw x := by
  letI : Fact (∀ k : ℤ, 0 < w k ^ 2) := ⟨fun k => sq_pos_of_pos (hw k)⟩
  letI : Fact (∀ k : ℤ, 0 < v k ^ 2) := ⟨fun k => sq_pos_of_pos (hv k)⟩
  funext b
  funext k
  change ((weightedComparison (fun k => w k ^ 2) (fun k => v k ^ 2)
      (C ^ 2) (sq_nonneg C) (pairComparisonSq w v C hw hv hC hcmp) (x b) : ℤ → ℂ) k) =
    (x b : ℤ → ℂ) k
  exact weightedComparison_apply _ _ (C ^ 2) (sq_nonneg C)
    (pairComparisonSq w v C hw hv hC hcmp) (x b) k

private theorem pairWeightedComparison_norm_le (w v : ℤ → ℝ) (C : ℝ)
    (hw : ∀ k, 0 < w k) (hv : ∀ k, 0 < v k)
    (hC : 0 ≤ C) (hcmp : ∀ k, v k ≤ C * w k)
    (x : WeightedPairHilbertOfPositive w hw) :
    weightedPairNormOfPositive v hv (pairWeightedComparison w v C hw hv hC hcmp x) ≤
      C * weightedPairNormOfPositive w hw x := by
  letI : Fact (∀ k : ℤ, 0 < w k ^ 2) := ⟨fun k => sq_pos_of_pos (hw k)⟩
  letI : Fact (∀ k : ℤ, 0 < v k ^ 2) := ⟨fun k => sq_pos_of_pos (hv k)⟩
  change ‖pairWeightedComparison w v C hw hv hC hcmp x‖ ≤ C * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  calc
    _ = ∑ b : Bool, ‖pairWeightedComparison w v C hw hv hC hcmp x b‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 _ _
    _ ≤ ∑ b : Bool, (C * ‖x b‖) ^ 2 := Finset.sum_le_sum (fun b _ => by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr
      have hn := weightedComparison_norm_le (fun k => w k ^ 2) (fun k => v k ^ 2)
        (C ^ 2) (sq_nonneg C) (fun k => by
          exact pairComparisonSq w v C hw hv hC hcmp k) (x b)
      have hcomponent :
          ‖weightedComparison (fun k => w k ^ 2) (fun k => v k ^ 2)
            (C ^ 2) (sq_nonneg C)
            (pairComparisonSq w v C hw hv hC hcmp) (x b)‖ ≤ C * ‖x b‖ := by
        simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hC] using hn
      simpa [pairWeightedComparison] using hcomponent)
    _ = C ^ 2 * ∑ b : Bool, ‖x b‖ ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ = (C * ‖x‖) ^ 2 := by rw [← PiLp.norm_sq_eq_of_L2 _ x]; ring

/-- The subexponential profile forces the repaired cutoff to equal the full
factorized weight outside a finite set of integer modes. -/
theorem repairedCutoff_eq_factorized_off_finite (Ω₁ Ω₂ : ℤ → ℝ)
    (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hsubexp : Tendsto (fun n : ℕ+ => logProfile Ω₂ n / (n : ℝ))
      atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℤ, N < k.natAbs →
      repairedCutoffWeight Ω₁ Ω₂ ε k = factorizedWeight Ω₁ Ω₂ k := by
  obtain ⟨N₀, hN⟩ := eventually_atTop.1
    (hsubexp.eventually (Iio_mem_nhds hε))
  let N : ℕ := N₀
  refine ⟨N, ?_⟩
  intro k hk
  have hkpos : 0 < k.natAbs := by omega
  let n : ℕ+ := ⟨k.natAbs, hkpos⟩
  have hnN : N ≤ (n : ℕ) := by exact_mod_cast Nat.le_of_lt hk
  have hprof := hN n hnN
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast n.property
  have hlog : Real.log (Ω₂ ((n : ℕ) : ℤ)) < ε * (n : ℝ) := by
    have hdiv := (div_lt_iff₀ hnreal).mp hprof
    simpa [logProfile] using hdiv
  have hexp := (Real.log_lt_iff_lt_exp (hΩ₂pos ((n : ℕ) : ℤ))).mp hlog
  have habs : Ω₂ k = Ω₂ ((k.natAbs : ℕ) : ℤ) := by
    cases k with
    | ofNat m => simp
    | negSucc m =>
        have hm : (Int.negSucc m : ℤ) = -((m + 1 : ℕ) : ℤ) := by omega
        have hnabs : (Int.negSucc m).natAbs = m + 1 := rfl
        change Ω₂ (Int.negSucc m) = Ω₂ ((Int.negSucc m).natAbs : ℤ)
        rw [hnabs, hm, hΩ₂even]
  have hcut : secondaryCutoff Ω₂ ε k = Ω₂ k := by
    unfold secondaryCutoff
    rw [habs]
    apply min_eq_right
    simpa [n] using le_of_lt hexp
  rw [repairedCutoffWeight, hcut, factorizedWeight]

/-- Finite modification equivalence for a positive weighted Dirac pair.  The
comparison constant is obtained from the maximum of both weight ratios on the
finite exceptional interval. -/
theorem repairedCutoff_pair_equivalent (Ω₁ Ω₂ : ℤ → ℝ)
    (hΩ₁pos : ∀ k, 0 < Ω₁ k) (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hsubexp : Tendsto (fun n : ℕ+ => logProfile Ω₂ n / (n : ℝ))
      atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
          (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)),
        ∃ z : WeightedPairHilbertOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
            (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos),
          weightedPairCoefficientsOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
              (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos) z =
            weightedPairCoefficientsOfPositive (factorizedWeight Ω₁ Ω₂)
              (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) y ∧
          weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
              (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos) z ≤
            C * weightedPairNormOfPositive (factorizedWeight Ω₁ Ω₂)
              (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) y) ∧
      (∀ z : WeightedPairHilbertOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
          (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos),
        ∃ y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
            (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)),
          weightedPairCoefficientsOfPositive (factorizedWeight Ω₁ Ω₂)
              (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) y =
            weightedPairCoefficientsOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
              (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos) z ∧
          weightedPairNormOfPositive (factorizedWeight Ω₁ Ω₂)
              (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) y ≤
            C * weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
              (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos) z) := by
  classical
  obtain ⟨N, htail⟩ := repairedCutoff_eq_factorized_off_finite Ω₁ Ω₂
    hΩ₂pos hΩ₂even hsubexp hε
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hSne : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  let w : ℤ → ℝ := factorizedWeight Ω₁ Ω₂
  let v : ℤ → ℝ := repairedCutoffWeight Ω₁ Ω₂ ε
  have hw : ∀ k, 0 < w k := fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)
  have hv : ∀ k, 0 < v k := repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos
  let ratio : ℤ → ℝ := fun k => max (v k / w k) (w k / v k)
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image S ratio hSne
  let C : ℝ := max 1 (ratio k₀)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCnonneg : 0 ≤ C := hC.le
  have hCone : 1 ≤ C := le_max_left _ _
  have hcmpV (k : ℤ) : v k ≤ C * w k := by
    by_cases hout : N < k.natAbs
    · have heq := htail k hout
      simp [v, w, heq]
      nlinarith [mul_nonneg (show 0 ≤ C - 1 by linarith) (hw k).le, hCone]
    · have hin : k ∈ S := by
        change k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
        rw [Finset.mem_Icc]
        omega
      have hr : v k / w k ≤ C :=
        le_trans (le_trans (le_max_left _ _) (hmax k hin)) (le_max_right _ _)
      exact (div_le_iff₀ (hw k)).mp hr
  have hcmpW (k : ℤ) : w k ≤ C * v k := by
    by_cases hout : N < k.natAbs
    · have heq := htail k hout
      simp [v, w, heq]
      nlinarith [mul_nonneg (show 0 ≤ C - 1 by linarith) (hv k).le, hCone]
    · have hin : k ∈ S := by
        change k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
        rw [Finset.mem_Icc]
        omega
      have hr : w k / v k ≤ C :=
        le_trans (le_trans (le_max_right _ _) (hmax k hin)) (le_max_right _ _)
      exact (div_le_iff₀ (hv k)).mp hr
  refine ⟨C, hC, ?_, ?_⟩
  · intro y
    let z := pairWeightedComparison w v C hw hv hCnonneg hcmpV y
    refine ⟨z, pairWeightedComparison_coefficients w v C hw hv hCnonneg hcmpV y, ?_⟩
    simpa [z] using pairWeightedComparison_norm_le w v C hw hv hCnonneg hcmpV y
  · intro z
    let y := pairWeightedComparison v w C hv hw hCnonneg hcmpW z
    refine ⟨y, pairWeightedComparison_coefficients v w C hv hw hCnonneg hcmpW z, ?_⟩
    simpa [y] using pairWeightedComparison_norm_le v w C hv hw hCnonneg hcmpW z

/-- The coefficient-preserving C=1 map from the full pair weight to the repaired cutoff pair weight. -/
def weightedPairToRepairedCutoff (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hΩ₁pos : ∀ k, 0 < Ω₁ k) (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))) :
    WeightedPairHilbertOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
      (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos) :=
  pairWeightedComparison (factorizedWeight Ω₁ Ω₂)
    (repairedCutoffWeight Ω₁ Ω₂ ε) 1
    (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))
    (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
    (by norm_num)
    (fun k => by
      have hup := repairedCutoff_upper Ω₁ Ω₂ ε (fun j => (hΩ₁pos j).le) k
      simpa [factorizedWeight] using hup)
    y

private theorem weightedPairToRepairedCutoff_coefficients (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hΩ₁pos : ∀ k, 0 < Ω₁ k) (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))) :
    weightedPairCoefficientsOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
      (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
      (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y) =
    weightedPairCoefficientsOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) y := by
  unfold weightedPairToRepairedCutoff
  exact pairWeightedComparison_coefficients (factorizedWeight Ω₁ Ω₂)
    (repairedCutoffWeight Ω₁ Ω₂ ε) 1
    (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))
    (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos) (by norm_num)
    (fun k => by
      have hup := repairedCutoff_upper Ω₁ Ω₂ ε (fun j => (hΩ₁pos j).le) k
      simpa [factorizedWeight] using hup) y

/-- The coefficient-preserving C=1 map from the full pair weight to the Ω₁ pair weight. -/
def weightedPairToBaseWeight (Ω₁ Ω₂ : ℤ → ℝ)
    (hΩ₁pos : ∀ k, 0 < Ω₁ k) (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (hΩ₂zero : Ω₂ 0 = 1) (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ)))
    (y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))) :
    WeightedPairHilbertOfPositive Ω₁ hΩ₁pos :=
  pairWeightedComparison (factorizedWeight Ω₁ Ω₂) Ω₁ 1
    (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) hΩ₁pos
    (by norm_num)
    (fun k => by
      have hΩ₂ge := secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k
      unfold factorizedWeight
      calc
        Ω₁ k = 1 * Ω₁ k := by ring
        _ ≤ Ω₂ k * Ω₁ k := mul_le_mul_of_nonneg_right hΩ₂ge (hΩ₁pos k).le
        _ = Ω₁ k * Ω₂ k := by ring
        _ = 1 * (Ω₁ k * Ω₂ k) := by ring)
    y

private theorem weightedPairToBaseWeight_coefficients (Ω₁ Ω₂ : ℤ → ℝ)
    (hΩ₁pos : ∀ k, 0 < Ω₁ k) (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (hΩ₂zero : Ω₂ 0 = 1) (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ)))
    (y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))) :
    weightedPairCoefficientsOfPositive Ω₁ hΩ₁pos
      (weightedPairToBaseWeight Ω₁ Ω₂ hΩ₁pos hΩ₂pos hΩ₂zero hΩ₂even hΩ₂mono y) =
    weightedPairCoefficientsOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) y := by
  unfold weightedPairToBaseWeight
  exact pairWeightedComparison_coefficients (factorizedWeight Ω₁ Ω₂) Ω₁ 1
    (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k)) hΩ₁pos (by norm_num)
    (fun k => by
      have hΩ₂ge := secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k
      unfold factorizedWeight
      calc
        Ω₁ k = 1 * Ω₁ k := by ring
        _ ≤ Ω₂ k * Ω₁ k := mul_le_mul_of_nonneg_right hΩ₂ge (hΩ₁pos k).le
        _ = Ω₁ k * Ω₂ k := by ring
        _ = 1 * (Ω₁ k * Ω₂ k) := by ring) y

/-- For an actual Dirac-pair element in the full weight Ω₁Ω₂, the repaired
cutoff norm converges to its Ω₁ norm.  The majorant is the summable squared
coefficient energy of the given full-weight pair. -/
theorem dm_repaired_cutoff_norm_limit (Ω₁ Ω₂ : ℤ → ℝ)
    (hΩ₁pos : ∀ k, 0 < Ω₁ k) (hΩ₂pos : ∀ k, 0 < Ω₂ k)
    (hΩ₂zero : Ω₂ 0 = 1)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ)))
    (y : WeightedPairHilbertOfPositive (factorizedWeight Ω₁ Ω₂)
      (fun k => mul_pos (hΩ₁pos k) (hΩ₂pos k))) :
    Tendsto (fun ε : ℝ => weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
      (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
      (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (weightedPairNormOfPositive Ω₁ hΩ₁pos
        (weightedPairToBaseWeight Ω₁ Ω₂ hΩ₁pos hΩ₂pos hΩ₂zero hΩ₂even hΩ₂mono y))) := by
  letI : Fact (∀ k : ℤ, 0 < factorizedWeight Ω₁ Ω₂ k ^ 2) :=
    ⟨fun k => sq_pos_of_pos (mul_pos (hΩ₁pos k) (hΩ₂pos k))⟩
  let bound : ℤ → ℝ := fun k => factorizedWeight Ω₁ Ω₂ k ^ 2 *
    (‖(y true : ℤ → ℂ) k‖ ^ 2 + ‖(y false : ℤ → ℂ) k‖ ^ 2)
  have hbound : Summable bound := by
    have ht := weightedHilbert_hasSum
      (fun k => factorizedWeight Ω₁ Ω₂ k ^ 2) (y true)
    have hf := weightedHilbert_hasSum
      (fun k => factorizedWeight Ω₁ Ω₂ k ^ 2) (y false)
    simpa [bound, mul_add] using ht.summable.add hf.summable
  let summand : ℝ → ℤ → ℝ := fun ε k =>
    repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2 *
      (‖(y true : ℤ → ℂ) k‖ ^ 2 + ‖(y false : ℤ → ℂ) k‖ ^ 2)
  let limitSummand : ℤ → ℝ := fun k => Ω₁ k ^ 2 *
      (‖(y true : ℤ → ℂ) k‖ ^ 2 + ‖(y false : ℤ → ℂ) k‖ ^ 2)
  have hpoint (k : ℤ) : Tendsto (summand · k) (𝓝[>] (0 : ℝ)) (𝓝 (limitSummand k)) := by
    have hc := repairedCutoff_tendsto Ω₁ Ω₂ k hΩ₂zero hΩ₂even hΩ₂mono
    have hsq := hc.mul hc
    have hmul := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => (‖(y true : ℤ → ℂ) k‖ ^ 2 + ‖(y false : ℤ → ℂ) k‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (‖(y true : ℤ → ℂ) k‖ ^ 2 + ‖(y false : ℤ → ℂ) k‖ ^ 2))).mul hsq
    simpa [summand, limitSummand, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hdom : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ k, ‖summand ε k‖ ≤ bound k := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    intro k
    have hcutpos := repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos k
    have hbasepos := mul_pos (hΩ₁pos k) (hΩ₂pos k)
    have hup := repairedCutoff_upper Ω₁ Ω₂ ε (fun j => (hΩ₁pos j).le) k
    have henergy : 0 ≤ (‖(y true : ℤ → ℂ) k‖ ^ 2 + ‖(y false : ℤ → ℂ) k‖ ^ 2) := by positivity
    have hsquare : repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2 ≤
        factorizedWeight Ω₁ Ω₂ k ^ 2 := by
      exact (sq_le_sq₀ hcutpos.le hbasepos.le).2 (by simpa [factorizedWeight] using hup)
    rw [Real.norm_of_nonneg]
    · exact mul_le_mul_of_nonneg_right hsquare henergy
    · exact mul_nonneg (sq_nonneg _) henergy
  have hsum := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  letI : Fact (∀ k : ℤ, 0 < Ω₁ k ^ 2) :=
    ⟨fun k => sq_pos_of_pos (hΩ₁pos k)⟩
  let y₁ := weightedPairToBaseWeight Ω₁ Ω₂ hΩ₁pos hΩ₂pos hΩ₂zero hΩ₂even hΩ₂mono y
  have hcutnorm (ε : ℝ) :
      weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
        (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y) ^ 2 =
        ∑' k, summand ε k := by
    letI : Fact (∀ k : ℤ, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) :=
      ⟨fun k => sq_pos_of_pos (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos k)⟩
    let z := weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y
    have hcoeff := weightedPairToRepairedCutoff_coefficients Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y
    change ‖z‖ ^ 2 = _
    rw [weightedPairHilbert_norm_sq]
    apply tsum_congr
    intro k
    have h₁ : (z true : ℤ → ℂ) k = (y true : ℤ → ℂ) k :=
      congrFun (congrFun hcoeff true) k
    have h₂ : (z false : ℤ → ℂ) k = (y false : ℤ → ℂ) k :=
      congrFun (congrFun hcoeff false) k
    rw [h₁, h₂]
  have hbaseNorm : weightedPairNormOfPositive Ω₁ hΩ₁pos y₁ ^ 2 = ∑' k, limitSummand k := by
    let z := y₁
    have hcoeff := weightedPairToBaseWeight_coefficients Ω₁ Ω₂ hΩ₁pos hΩ₂pos
      hΩ₂zero hΩ₂even hΩ₂mono y
    change ‖z‖ ^ 2 = _
    rw [weightedPairHilbert_norm_sq]
    apply tsum_congr
    intro k
    have h₁ : (z true : ℤ → ℂ) k = (y true : ℤ → ℂ) k :=
      congrFun (congrFun hcoeff true) k
    have h₂ : (z false : ℤ → ℂ) k = (y false : ℤ → ℂ) k :=
      congrFun (congrFun hcoeff false) k
    rw [h₁, h₂]
  have hnormSq : Tendsto
      (fun ε : ℝ => weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
        (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (weightedPairNormOfPositive Ω₁ hΩ₁pos y₁ ^ 2)) := by
    have hsum' : Tendsto
        (fun ε : ℝ => weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
          (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
          (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (∑' k, limitSummand k)) :=
      (tendsto_congr' (Eventually.of_forall fun ε => (hcutnorm ε).symm)).1 hsum
    simpa only [← hbaseNorm] using hsum'
  have hnorm : Tendsto
      (fun ε : ℝ => weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
        (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (weightedPairNormOfPositive Ω₁ hΩ₁pos y₁)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    have hnorm' : Tendsto
        (fun ε : ℝ => weightedPairNormOfPositive (repairedCutoffWeight Ω₁ Ω₂ ε)
          (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
          (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Real.sqrt (weightedPairNormOfPositive Ω₁ hΩ₁pos y₁ ^ 2))) :=
      (tendsto_congr' (Eventually.of_forall fun ε => weightedPairNormOfPositive_eq_sqrt
        (repairedCutoffWeight Ω₁ Ω₂ ε) (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos)
        (weightedPairToRepairedCutoff Ω₁ Ω₂ ε hΩ₁pos hΩ₂pos y))).2 h
    simpa only [← weightedPairNormOfPositive_eq_sqrt Ω₁ hΩ₁pos y₁] using hnorm'
  simpa [y₁] using hnorm

end NlsGge.Atomic.DM049
