import NlsGge.Atomic.DM.DM047
import NlsGge.Sobolev.WeightedHilbert

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.DM048

open NlsGge.Atomic.DM046
open NlsGge.Atomic.DM047
open NlsGge.Pilot
open Filter
open scoped Topology

/-- The source factorization Ω = Ω₁ Ω₂. -/
def factorizedWeight (Ω₁ Ω₂ : ℤ → ℝ) (k : ℤ) : ℝ := Ω₁ k * Ω₂ k

/-- DM's repaired cutoff retains Ω₁ and truncates only Ω₂. -/
def repairedCutoffWeight (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ) (k : ℤ) : ℝ :=
  Ω₁ k * secondaryCutoff Ω₂ ε k

/-- A sequence belongs to the closed radius-r ball for the genuine weighted
Hilbert carrier whose squared coefficient weights are `W k ^ 2`. -/
def weightedClosedBall (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) (r : ℝ) : Set (ℤ → ℂ) :=
  by
    letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
    exact {x | ∃ y : WeightedHilbert (fun k => W k ^ 2),
      (y : ℤ → ℂ) = x ∧ ‖y‖ ≤ r}

/-- The corresponding open ball in the same genuine weighted carrier. -/
def weightedOpenBall (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) (r : ℝ) : Set (ℤ → ℂ) :=
  by
    letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
    exact {x | ∃ y : WeightedHilbert (fun k => W k ^ 2),
      (y : ℤ → ℂ) = x ∧ ‖y‖ < r}

/-- Genuine Dirac-pair Hilbert carrier: two weighted sequence Hilbert spaces
with the Hilbert `L²` norm across the two components. -/
abbrev WeightedPairHilbert (W : ℤ → ℝ)
    [Fact (∀ k : ℤ, 0 < W k ^ 2)] :=
  PiLp 2 (fun _ : Bool => WeightedHilbert (fun k => W k ^ 2))

/-- The raw pair of Fourier coefficient sequences represented by a weighted
Dirac-pair Hilbert element. -/
def weightedPairCoefficients (W : ℤ → ℝ)
    [Fact (∀ k : ℤ, 0 < W k ^ 2)] (x : WeightedPairHilbert W) : Bool → ℤ → ℂ :=
  fun b k => (x b : ℤ → ℂ) k

/-- The source squared norm of a weighted Dirac pair is exactly the sum over
integer modes of both coefficient energies. -/
theorem weightedPairHilbert_norm_sq (W : ℤ → ℝ)
    [hW : Fact (∀ k : ℤ, 0 < W k ^ 2)] (x : WeightedPairHilbert W) :
    ‖x‖ ^ 2 = ∑' k : ℤ, W k ^ 2 *
      (‖(x true : ℤ → ℂ) k‖ ^ 2 + ‖(x false : ℤ → ℂ) k‖ ^ 2) := by
  have ht := weightedHilbert_hasSum (fun k => W k ^ 2) (x true)
  have hf := weightedHilbert_hasSum (fun k => W k ^ 2) (x false)
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_bool,
    weightedHilbert_norm_sq (fun k => W k ^ 2) (x true),
    weightedHilbert_norm_sq (fun k => W k ^ 2) (x false)]
  rw [← ht.summable.tsum_add hf.summable]
  apply tsum_congr
  intro k
  ring

/-- Closed source ball for two coefficient sequences with the exact joint
Hilbert radius. -/
def weightedPairClosedBall (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) (r : ℝ) :
    Set (Bool → ℤ → ℂ) := by
  letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
  exact {x | ∃ y : WeightedPairHilbert W,
    weightedPairCoefficients W y = x ∧ ‖y‖ ≤ r}

/-- Open source ball for two coefficient sequences with the exact joint
Hilbert radius. -/
def weightedPairOpenBall (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) (r : ℝ) :
    Set (Bool → ℤ → ℂ) := by
  letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
  exact {x | ∃ y : WeightedPairHilbert W,
    weightedPairCoefficients W y = x ∧ ‖y‖ < r}

private theorem weightedPair_norm_le_of_components
    (w v : ℤ → ℝ)
    [Fact (∀ k : ℤ, 0 < w k ^ 2)] [Fact (∀ k : ℤ, 0 < v k ^ 2)]
    (x : WeightedPairHilbert w) (y : WeightedPairHilbert v)
    (h : ∀ b : Bool, ‖x b‖ ≤ ‖y b‖) : ‖x‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ = ∑ b : Bool, ‖x b‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ x
    _ ≤ ∑ b : Bool, ‖y b‖ ^ 2 := Finset.sum_le_sum
      (fun b _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h b))
    _ = _ := (PiLp.norm_sq_eq_of_L2 _ y).symm

theorem secondaryCutoff_ge_one (Ω₂ : ℤ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hΩ₂ : ∀ k, 1 ≤ Ω₂ k) (k : ℤ) : 1 ≤ secondaryCutoff Ω₂ ε k := by
  apply le_min
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  · exact hΩ₂ k

theorem secondaryCutoff_le (Ω₂ : ℤ → ℝ) (ε : ℝ) (k : ℤ) :
    secondaryCutoff Ω₂ ε k ≤ Ω₂ k := min_le_right _ _

theorem secondaryCutoff_pos (Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hΩ₂ : ∀ k, 0 < Ω₂ k) (k : ℤ) : 0 < secondaryCutoff Ω₂ ε k := by
  apply lt_min
  · exact Real.exp_pos _
  · exact hΩ₂ k

/-- A positive, normalized, even, monotone secondary weight is at least one
on every integer mode. -/
theorem secondaryWeight_ge_one (Ω₂ : ℤ → ℝ) (hzero : Ω₂ 0 = 1)
    (heven : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hmono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    ∀ k : ℤ, 1 ≤ Ω₂ k := by
  intro k
  cases k with
  | ofNat n =>
      simpa [hzero] using hmono (show 0 ≤ n by omega)
  | negSucc n =>
      have hnat : 1 ≤ Ω₂ ((n + 1 : ℕ) : ℤ) := by
        simpa [hzero] using hmono (show 0 ≤ n + 1 by omega)
      have hcast : ((n + 1 : ℕ) : ℤ) = -((Int.negSucc n : ℤ)) := by omega
      rw [hcast, heven] at hnat
      exact hnat

theorem repairedCutoff_lower (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hΩ₁ : ∀ k, 0 ≤ Ω₁ k) (hzero : Ω₂ 0 = 1)
    (heven : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hmono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    ∀ k, Ω₁ k ≤ repairedCutoffWeight Ω₁ Ω₂ ε k := by
  intro k
  unfold repairedCutoffWeight
  have hcut := secondaryCutoff_ge_one Ω₂ ε hε
    (secondaryWeight_ge_one Ω₂ hzero heven hmono) k
  calc
    Ω₁ k = Ω₁ k * 1 := by ring
    _ ≤ Ω₁ k * secondaryCutoff Ω₂ ε k := mul_le_mul_of_nonneg_left hcut (hΩ₁ k)

theorem repairedCutoff_upper (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hΩ₁ : ∀ k, 0 ≤ Ω₁ k) :
    ∀ k, repairedCutoffWeight Ω₁ Ω₂ ε k ≤ factorizedWeight Ω₁ Ω₂ k := by
  intro k
  unfold repairedCutoffWeight factorizedWeight
  exact mul_le_mul_of_nonneg_left (secondaryCutoff_le Ω₂ ε k) (hΩ₁ k)

theorem repairedCutoff_pos (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hΩ₁ : ∀ k, 0 < Ω₁ k) (hΩ₂ : ∀ k, 0 < Ω₂ k) :
    ∀ k, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k := by
  intro k
  unfold repairedCutoffWeight
  exact mul_pos (hΩ₁ k) (secondaryCutoff_pos Ω₂ ε hΩ₂ k)

theorem repairedCutoff_tendsto (Ω₁ Ω₂ : ℤ → ℝ) (k : ℤ)
    (hzero : Ω₂ 0 = 1) (heven : ∀ j, Ω₂ (-j) = Ω₂ j)
    (hmono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    Tendsto (fun ε : ℝ => repairedCutoffWeight Ω₁ Ω₂ ε k)
      (𝓝[>] (0 : ℝ)) (𝓝 (Ω₁ k)) := by
  have hexp : Tendsto (fun ε : ℝ => Real.exp (ε * (k.natAbs : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : Tendsto (fun ε : ℝ => Real.exp (ε * (k.natAbs : ℝ)))
        (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hc : Continuous (fun ε : ℝ => Real.exp (ε * (k.natAbs : ℝ))) :=
        Real.continuous_exp.comp
          (continuous_id.mul (continuous_const : Continuous fun _ : ℝ => (k.natAbs : ℝ)))
      have hat0 : ContinuousAt
          (fun ε : ℝ => Real.exp (ε * (k.natAbs : ℝ))) 0 := hc.continuousAt
      have h := hat0.tendsto
      simpa using h
    have hzero : Real.exp ((0 : ℝ) * (k.natAbs : ℝ)) = 1 := by simp
    simpa only [hzero] using hcont.mono_left nhdsWithin_le_nhds
  have hmin : Tendsto (fun ε : ℝ =>
      min (Real.exp (ε * (k.natAbs : ℝ))) (Ω₂ k))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => Ω₂ k) (𝓝[>] (0 : ℝ)) (𝓝 (Ω₂ k)) :=
      tendsto_const_nhds
    have h := hexp.min hconst
    have hΩ₂ : 1 ≤ Ω₂ k := secondaryWeight_ge_one Ω₂ hzero heven hmono k
    simpa [min_eq_left hΩ₂] using h
  have hmul : Tendsto (fun ε : ℝ => Ω₁ k *
      min (Real.exp (ε * (k.natAbs : ℝ))) (Ω₂ k))
      (𝓝[>] (0 : ℝ)) (𝓝 (Ω₁ k)) := by
    simpa using (tendsto_const_nhds.mul hmin)
  simpa [repairedCutoffWeight, secondaryCutoff] using hmul

private theorem square_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ b - a) (by linarith : 0 ≤ b + a)]

private theorem cutoff_square_ge (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hΩ₁ : ∀ k, 0 < Ω₁ k) (hzero : Ω₂ 0 = 1)
    (heven : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hmono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) (k : ℤ) :
    Ω₁ k ^ 2 ≤ repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2 := by
  apply square_mono (le_of_lt (hΩ₁ k))
  exact repairedCutoff_lower Ω₁ Ω₂ ε hε (fun j => (hΩ₁ j).le)
    hzero heven hmono k

private theorem cutoff_square_pos (Ω₁ Ω₂ : ℤ → ℝ) (ε : ℝ)
    (hΩ₁ : ∀ k, 0 < Ω₁ k) (hΩ₂ : ∀ k, 0 < Ω₂ k) :
    ∀ k, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2 := by
  intro k
  exact sq_pos_of_pos (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁ hΩ₂ k)

private theorem base_square_pos (Ω₁ : ℤ → ℝ) (hΩ₁ : ∀ k, 0 < Ω₁ k) :
    ∀ k, 0 < Ω₁ k ^ 2 := fun k => sq_pos_of_pos (hΩ₁ k)

theorem repairedCutoff_closed_ball_inclusion (Ω₁ Ω₂ : ℤ → ℝ) (ε r : ℝ)
    (hε : 0 ≤ ε) (hΩ₁ : ∀ k, 0 < Ω₁ k)
    (hΩ₂zero : Ω₂ 0 = 1)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    weightedClosedBall (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
          lt_of_lt_of_le zero_lt_one (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))) r ⊆
      weightedClosedBall Ω₁ hΩ₁ r := by
  intro x hx
  obtain ⟨y, hy, hyr⟩ := hx
  letI : Fact (∀ k : ℤ, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) :=
    ⟨cutoff_square_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
      lt_of_lt_of_le zero_lt_one (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))⟩
  letI : Fact (∀ k : ℤ, 0 < Ω₁ k ^ 2) := ⟨base_square_pos Ω₁ hΩ₁⟩
  let cmp := weightedComparison
    (fun k => repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) (fun k => Ω₁ k ^ 2) 1
    (by norm_num)
    (fun k => by simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero hΩ₂even hΩ₂mono k)
  let z : WeightedHilbert (fun k => Ω₁ k ^ 2) := cmp y
  have hz : (z : ℤ → ℂ) = x := by
    ext k
    change ((y : ℤ → ℂ) k) = x k
    exact congrFun hy k
  have hnorm : ‖z‖ ≤ r := by
    calc
      ‖z‖ ≤ ‖y‖ := by
        simpa [z, cmp] using weightedComparison_norm_le
          (fun k => repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2)
          (fun k => Ω₁ k ^ 2) 1 (by norm_num)
          (fun k => by simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero hΩ₂even hΩ₂mono k) y
      _ ≤ r := hyr
  exact ⟨z, hz, hnorm⟩

theorem repairedCutoff_open_ball_inclusion (Ω₁ Ω₂ : ℤ → ℝ) (ε r : ℝ)
    (hε : 0 ≤ ε) (hΩ₁ : ∀ k, 0 < Ω₁ k)
    (hΩ₂zero : Ω₂ 0 = 1)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    weightedOpenBall (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
          lt_of_lt_of_le zero_lt_one (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))) r ⊆
      weightedOpenBall Ω₁ hΩ₁ r := by
  intro x hx
  obtain ⟨y, hy, hyr⟩ := hx
  letI : Fact (∀ k : ℤ, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) :=
    ⟨cutoff_square_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
      lt_of_lt_of_le zero_lt_one (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))⟩
  letI : Fact (∀ k : ℤ, 0 < Ω₁ k ^ 2) := ⟨base_square_pos Ω₁ hΩ₁⟩
  let cmp := weightedComparison
    (fun k => repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) (fun k => Ω₁ k ^ 2) 1
    (by norm_num)
    (fun k => by simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero hΩ₂even hΩ₂mono k)
  let z : WeightedHilbert (fun k => Ω₁ k ^ 2) := cmp y
  have hz : (z : ℤ → ℂ) = x := by
    ext k
    change ((y : ℤ → ℂ) k) = x k
    exact congrFun hy k
  have hnorm : ‖z‖ < r := by
    calc
      ‖z‖ ≤ ‖y‖ := by
        simpa [z, cmp] using weightedComparison_norm_le
          (fun k => repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2)
          (fun k => Ω₁ k ^ 2) 1 (by norm_num)
          (fun k => by simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero hΩ₂even hΩ₂mono k) y
      _ < r := hyr
  exact ⟨z, hz, hnorm⟩

/-- Closed Dirac-pair balls for the repaired cutoff lie in the source
Dirac-pair ball with the same radius.  The comparison acts coefficientwise
on both components, so its Pi-L² operator norm is one. -/
theorem repairedCutoff_pair_closed_ball_inclusion (Ω₁ Ω₂ : ℤ → ℝ) (ε r : ℝ)
    (hε : 0 ≤ ε) (hΩ₁ : ∀ k, 0 < Ω₁ k)
    (hΩ₂zero : Ω₂ 0 = 1)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    weightedPairClosedBall (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
          lt_of_lt_of_le zero_lt_one
            (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))) r ⊆
      weightedPairClosedBall Ω₁ hΩ₁ r := by
  intro x hx
  obtain ⟨y, hy, hyr⟩ := hx
  letI : Fact (∀ k : ℤ, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) :=
    ⟨cutoff_square_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
      lt_of_lt_of_le zero_lt_one
        (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))⟩
  letI : Fact (∀ k : ℤ, 0 < Ω₁ k ^ 2) := ⟨base_square_pos Ω₁ hΩ₁⟩
  let cmp := weightedComparison
    (fun k => repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) (fun k => Ω₁ k ^ 2) 1
    (by norm_num)
    (fun k => by
      simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero hΩ₂even hΩ₂mono k)
  let z : WeightedPairHilbert Ω₁ := WithLp.toLp 2 (fun b => cmp (y b))
  have hz : weightedPairCoefficients Ω₁ z = x := by
    funext b
    funext k
    change ((cmp (y b) : ℤ → ℂ) k) = x b k
    rw [weightedComparison_apply]
    exact congrFun (congrFun hy b) k
  have hnorm : ‖z‖ ≤ r := by
    calc
      ‖z‖ ≤ ‖y‖ := weightedPair_norm_le_of_components _ _ z y (fun b => by
        change ‖cmp (y b)‖ ≤ ‖y b‖
        calc
          ‖cmp (y b)‖ ≤ Real.sqrt 1 * ‖y b‖ := by
            exact weightedComparison_norm_le _ _ 1 (by norm_num)
              (fun k => by
                simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero
                  hΩ₂even hΩ₂mono k) (y b)
          _ = ‖y b‖ := by simp)
      _ ≤ r := hyr
  exact ⟨z, hz, hnorm⟩

/-- Open Dirac-pair balls for the repaired cutoff lie in the source
Dirac-pair ball with the same radius. -/
theorem repairedCutoff_pair_open_ball_inclusion (Ω₁ Ω₂ : ℤ → ℝ) (ε r : ℝ)
    (hε : 0 ≤ ε) (hΩ₁ : ∀ k, 0 < Ω₁ k)
    (hΩ₂zero : Ω₂ 0 = 1)
    (hΩ₂even : ∀ k, Ω₂ (-k) = Ω₂ k)
    (hΩ₂mono : Monotone (fun n : ℕ => Ω₂ (n : ℤ))) :
    weightedPairOpenBall (repairedCutoffWeight Ω₁ Ω₂ ε)
        (repairedCutoff_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
          lt_of_lt_of_le zero_lt_one
            (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))) r ⊆
      weightedPairOpenBall Ω₁ hΩ₁ r := by
  intro x hx
  obtain ⟨y, hy, hyr⟩ := hx
  letI : Fact (∀ k : ℤ, 0 < repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) :=
    ⟨cutoff_square_pos Ω₁ Ω₂ ε hΩ₁ (fun k =>
      lt_of_lt_of_le zero_lt_one
        (secondaryWeight_ge_one Ω₂ hΩ₂zero hΩ₂even hΩ₂mono k))⟩
  letI : Fact (∀ k : ℤ, 0 < Ω₁ k ^ 2) := ⟨base_square_pos Ω₁ hΩ₁⟩
  let cmp := weightedComparison
    (fun k => repairedCutoffWeight Ω₁ Ω₂ ε k ^ 2) (fun k => Ω₁ k ^ 2) 1
    (by norm_num)
    (fun k => by
      simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero hΩ₂even hΩ₂mono k)
  let z : WeightedPairHilbert Ω₁ := WithLp.toLp 2 (fun b => cmp (y b))
  have hz : weightedPairCoefficients Ω₁ z = x := by
    funext b
    funext k
    change ((cmp (y b) : ℤ → ℂ) k) = x b k
    rw [weightedComparison_apply]
    exact congrFun (congrFun hy b) k
  have hnorm : ‖z‖ < r := by
    calc
      ‖z‖ ≤ ‖y‖ := weightedPair_norm_le_of_components _ _ z y (fun b => by
        change ‖cmp (y b)‖ ≤ ‖y b‖
        calc
          ‖cmp (y b)‖ ≤ Real.sqrt 1 * ‖y b‖ := by
            exact weightedComparison_norm_le _ _ 1 (by norm_num)
              (fun k => by
                simpa using cutoff_square_ge Ω₁ Ω₂ ε hε hΩ₁ hΩ₂zero
                  hΩ₂even hΩ₂mono k) (y b)
          _ = ‖y b‖ := by simp)
      _ < r := hyr
  exact ⟨z, hz, hnorm⟩

end NlsGge.Atomic.DM048
