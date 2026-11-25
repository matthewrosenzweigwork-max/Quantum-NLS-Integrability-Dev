import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.DM.DM049
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Filter
open scoped Topology

namespace NlsGge.Atomic.KST044

open NlsGge.Atomic.KST002
open NlsGge.Atomic.KST043
open NlsGge.Atomic.DM047
open NlsGge.Atomic.DM048
open NlsGge.Pilot

/-- The source product weight `w v`. -/
def productWeight (w v : ℤ → ℝ) (k : ℤ) : ℝ := w k * v k

/-- The source weight with only its secondary factor exponentially truncated. -/
def truncatedProductWeight (w v : ℤ → ℝ) (ε : ℝ) (k : ℤ) : ℝ :=
  w k * secondaryCutoff v ε k

/-- The actual weighted-pair carrier, with its positivity instance derived from
its named positive weight hypothesis. -/
abbrev PairCarrier (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) : Type :=
  NlsGge.Atomic.DM049.WeightedPairHilbertOfPositive W hW

/-- The actual outer PiLp norm on a positive weighted-pair carrier.  The
wrapper makes the positivity-derived carrier instance explicit in signatures. -/
def pairNorm (W : ℤ → ℝ) (hW : ∀ k, 0 < W k)
    (x : PairCarrier W hW) : ℝ :=
  NlsGge.Atomic.DM049.weightedPairNormOfPositive W hW x

/-- The actual raw two-channel Fourier coefficients carried by a weighted
Dirac pair. -/
def pairCoefficients (W : ℤ → ℝ) (hW : ∀ k, 0 < W k)
    (x : PairCarrier W hW) : Bool → ℤ → ℂ :=
  NlsGge.Atomic.DM049.weightedPairCoefficientsOfPositive W hW x

/-- Coefficient-space membership is represented by the range of the actual
weighted-pair coefficient map. -/
def pairCoefficientSpace (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) :
    Set (Bool → ℤ → ℂ) := Set.range (pairCoefficients W hW)

/-- The source subexponential hypotheses imply `v k ≥ 1` at every signed index. -/
theorem subexponentialWeight_ge_one (v : ℤ → ℝ)
    (hv : KSTSubexponentialWeight v) (k : ℤ) : 1 ≤ v k := by
  rcases hv with ⟨hv0, heven, hmono, hsub, hlim, heventual⟩
  cases k with
  | ofNat n =>
      exact hv0.trans (hmono (Nat.zero_le n))
  | negSucc n =>
      have hpos : 1 ≤ v ((n + 1 : ℕ) : ℤ) :=
        hv0.trans (hmono (Nat.zero_le (n + 1)))
      have hneg : ((n + 1 : ℕ) : ℤ) = -((Int.negSucc n : ℤ)) := by omega
      rw [hneg, heven] at hpos
      exact hpos

/-- The cutoff factor stays above one when `ε ≥ 0`. -/
theorem secondaryCutoff_ge_one (v : ℤ → ℝ)
    (hv : KSTSubexponentialWeight v) (ε : ℝ) (hε : 0 ≤ ε) (k : ℤ) :
    1 ≤ secondaryCutoff v ε k := by
  apply le_min
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hε (Nat.cast_nonneg _))
  · exact subexponentialWeight_ge_one v hv k

/-- The cutoff factor is positive for every real cutoff parameter. -/
theorem secondaryCutoff_pos (v : ℤ → ℝ)
    (hv : KSTSubexponentialWeight v) (ε : ℝ) (k : ℤ) :
    0 < secondaryCutoff v ε k := by
  apply lt_min
  · exact Real.exp_pos _
  · exact lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)

/-- Pointwise source bounds for `w v_ε`, retaining the entire secondary factor. -/
theorem truncatedProductWeight_bounds (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v)
    (ε : ℝ) (hε : 0 ≤ ε) (k : ℤ) :
    w k ≤ truncatedProductWeight w v ε k ∧
      truncatedProductWeight w v ε k ≤ productWeight w v k := by
  constructor
  · unfold truncatedProductWeight
    have hcut := secondaryCutoff_ge_one v hv ε hε k
    nlinarith [hw k]
  · unfold truncatedProductWeight productWeight secondaryCutoff
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt (hw k))

/-- The source and truncated product weights are positive, without imposing any
extra growth, boundedness, or submultiplicativity assumption on `w`. -/
theorem truncatedProductWeight_pos (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v)
    (ε : ℝ) (k : ℤ) : 0 < truncatedProductWeight w v ε k := by
  unfold truncatedProductWeight
  exact mul_pos (hw k) (secondaryCutoff_pos v hv ε k)

/-- A coefficient-preserving map between actual KST weighted-pair Hilbert
carriers whenever the squared target weight is bounded by a multiple of the
squared source weight. -/
noncomputable def pairWeightComparison {W V : ℤ → ℝ}
    (hW : ∀ k, 0 < W k) (hV : ∀ k, 0 < V k)
    (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ k, V k ^ 2 ≤ C * W k ^ 2) :
    PairCarrier W hW →ₗ[ℂ] PairCarrier V hV := by
  letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
  letI : Fact (∀ k : ℤ, 0 < V k ^ 2) := ⟨fun k => sq_pos_of_pos (hV k)⟩
  exact {
    toFun := fun x => WithLp.toLp 2 (fun b =>
      NlsGge.Pilot.weightedComparison (fun k => W k ^ 2) (fun k => V k ^ 2)
        C hC hcmp (x b))
    map_add' := by
      intro x y
      apply PiLp.ext
      intro b
      exact map_add
        (NlsGge.Pilot.weightedComparison (fun k => W k ^ 2) (fun k => V k ^ 2)
          C hC hcmp) (x b) (y b)
    map_smul' := by
      intro c x
      apply PiLp.ext
      intro b
      exact map_smul
        (NlsGge.Pilot.weightedComparison (fun k => W k ^ 2) (fun k => V k ^ 2)
          C hC hcmp) c (x b)
  }

/-- The pair comparison leaves every raw Fourier coefficient unchanged. -/
theorem pairWeightComparison_coeff {W V : ℤ → ℝ}
    (hW : ∀ k, 0 < W k) (hV : ∀ k, 0 < V k)
    (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ k, V k ^ 2 ≤ C * W k ^ 2)
    (x : PairCarrier W hW) (b : Bool) (k : ℤ) :
    (pairWeightComparison hW hV C hC hcmp x b : ℤ → ℂ) k = (x b) k := by
  letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
  letI : Fact (∀ k : ℤ, 0 < V k ^ 2) := ⟨fun k => sq_pos_of_pos (hV k)⟩
  change ((NlsGge.Pilot.weightedComparison (fun j => W j ^ 2)
      (fun j => V j ^ 2) C hC hcmp (x b) : ℤ → ℂ) k) = (x b : ℤ → ℂ) k
  exact NlsGge.Pilot.weightedComparison_apply _ _ C hC hcmp (x b) k

/-- Each component of a pair comparison has the scalar weighted-comparison
norm bound. -/
theorem pairWeightComparison_norm_le {W V : ℤ → ℝ}
    (hW : ∀ k, 0 < W k) (hV : ∀ k, 0 < V k)
    (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ k, V k ^ 2 ≤ C * W k ^ 2)
    (x : PairCarrier W hW) :
    pairNorm V hV (pairWeightComparison hW hV C hC hcmp x) ≤
      Real.sqrt C * pairNorm W hW x := by
  letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
  letI : Fact (∀ k : ℤ, 0 < V k ^ 2) := ⟨fun k => sq_pos_of_pos (hV k)⟩
  change ‖pairWeightComparison hW hV C hC hcmp x‖ ≤ Real.sqrt C * ‖x‖
  have hcomp (b : Bool) :
      ‖pairWeightComparison hW hV C hC hcmp x b‖ ≤ Real.sqrt C * ‖x b‖ := by
    exact NlsGge.Pilot.weightedComparison_norm_le
      (fun k => W k ^ 2) (fun k => V k ^ 2) C hC hcmp (x b)
  have hsum : ‖pairWeightComparison hW hV C hC hcmp x‖ ^ 2 ≤
      (Real.sqrt C * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hb (b : Bool) :
        ‖pairWeightComparison hW hV C hC hcmp x b‖ ^ 2 ≤
          (Real.sqrt C * ‖x b‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
        (hcomp b)
    have hfin : (∑ b : Bool, ‖pairWeightComparison hW hV C hC hcmp x b‖ ^ 2) ≤
        ∑ b : Bool, (Real.sqrt C * ‖x b‖) ^ 2 :=
      Finset.sum_le_sum (fun b _ => hb b)
    have hfactor :
        (∑ b : Bool, (Real.sqrt C * ‖x b‖) ^ 2) =
          (Real.sqrt C * ‖x‖) ^ 2 := by
      calc
        (∑ b : Bool, (Real.sqrt C * ‖x b‖) ^ 2) =
            C * ∑ b : Bool, ‖x b‖ ^ 2 := by
          simp_rw [mul_pow, Real.sq_sqrt hC]
          rw [Finset.mul_sum]
        _ = C * ‖x‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]
        _ = (Real.sqrt C * ‖x‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hC]
    exact hfin.trans_eq hfactor
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 hsum

/-- The inclusion from the source `H^{wv}` carrier to the retained-cutoff
carrier, with the exact raw coefficient identity. -/
noncomputable def cutoffInclusion (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v) (ε : ℝ) :
    PairCarrier (productWeight w v) (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) →ₗ[ℂ]
    PairCarrier (truncatedProductWeight w v ε)
      (truncatedProductWeight_pos w v hw hv ε) :=
  pairWeightComparison
    (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)))
    (truncatedProductWeight_pos w v hw hv ε)
    1 (by norm_num)
    (fun k => by
      have hcut : secondaryCutoff v ε k ≤ v k := min_le_right _ _
      have hleft : 0 ≤ w k * secondaryCutoff v ε k :=
        mul_nonneg (hw k).le (secondaryCutoff_pos v hv ε k).le
      have hright : 0 ≤ w k * v k := mul_nonneg (hw k).le
        (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)).le
      have hmul : w k * secondaryCutoff v ε k ≤ w k * v k :=
        mul_le_mul_of_nonneg_left hcut (hw k).le
      have hsquare := (sq_le_sq₀ hleft hright).2 hmul
      simpa [truncatedProductWeight, productWeight] using hsquare)

/-- Forgetting the secondary factor is an actual coefficient-preserving map
`H^{wv} → H^w`. -/
noncomputable def baseInclusion (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v) :
    PairCarrier (productWeight w v) (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) →ₗ[ℂ]
    PairCarrier w hw :=
  pairWeightComparison
    (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)))
    hw 1 (by norm_num)
    (fun k => by
      have hv1 := subexponentialWeight_ge_one v hv k
      have hleft : 0 ≤ w k := (hw k).le
      have hcmp : w k ≤ w k * v k := by
        calc
          w k = 1 * w k := by ring
          _ ≤ v k * w k := mul_le_mul_of_nonneg_right hv1 hleft
          _ = w k * v k := by ring
      have hvpos : 0 < v k := lt_of_lt_of_le zero_lt_one hv1
      have hright : 0 ≤ w k * v k := mul_nonneg hleft hvpos.le
      have hsquare := (sq_le_sq₀ hleft hright).2 hcmp
      simpa [productWeight] using hsquare)

/-- The retained-cutoff Hilbert map preserves each actual Fourier coefficient. -/
theorem cutoffInclusion_coefficients (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v) (ε : ℝ)
    (ψ : PairCarrier (productWeight w v) (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)))) :
    pairCoefficients (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε) (cutoffInclusion w v hw hv ε ψ) =
      pairCoefficients (productWeight w v)
        (fun k => mul_pos (hw k)
          (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ := by
  funext b
  funext k
  exact pairWeightComparison_coeff _ _ _ _ _ ψ b k

/-- The base-weight Hilbert map also preserves each actual Fourier coefficient. -/
theorem baseInclusion_coefficients (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v)
    (ψ : PairCarrier (productWeight w v) (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)))) :
    pairCoefficients w hw (baseInclusion w v hw hv ψ) =
      pairCoefficients (productWeight w v)
        (fun k => mul_pos (hw k)
          (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ := by
  funext b
  funext k
  exact pairWeightComparison_coeff _ _ _ _ _ ψ b k

/-- The squared `wv_ε` coefficient energy of a fixed `ψ ∈ H^{wv}` converges to
its squared `w` coefficient energy. -/
theorem truncated_secondary_weight_sq_norm_tendsto (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v)
    (ψ : PairCarrier (productWeight w v) (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)))) :
    Tendsto
      (fun ε : ℝ => pairNorm (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε)
        (cutoffInclusion w v hw hv ε ψ) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (pairNorm w hw (baseInclusion w v hw hv ψ) ^ 2)) := by
  let W : ℤ → ℝ := productWeight w v
  let hW : ∀ k, 0 < W k := by
    intro k
    exact mul_pos (hw k) (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))
  letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
  let bound : ℤ → ℝ := fun k => W k ^ 2 *
    (‖(ψ true : ℤ → ℂ) k‖ ^ 2 + ‖(ψ false : ℤ → ℂ) k‖ ^ 2)
  have hbound : Summable bound := by
    have ht := weightedHilbert_hasSum (fun k => W k ^ 2) (ψ true)
    have hf := weightedHilbert_hasSum (fun k => W k ^ 2) (ψ false)
    simpa [bound, mul_add] using ht.summable.add hf.summable
  let summand : ℝ → ℤ → ℝ := fun ε k =>
    truncatedProductWeight w v ε k ^ 2 *
      (‖(ψ true : ℤ → ℂ) k‖ ^ 2 + ‖(ψ false : ℤ → ℂ) k‖ ^ 2)
  let limitSummand : ℤ → ℝ := fun k => w k ^ 2 *
    (‖(ψ true : ℤ → ℂ) k‖ ^ 2 + ‖(ψ false : ℤ → ℂ) k‖ ^ 2)
  have hpoint (k : ℤ) : Tendsto (summand · k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (limitSummand k)) := by
    have hε0 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have harg : Tendsto (fun ε : ℝ => ε * (k.natAbs : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hε0.mul_const (k.natAbs : ℝ)
    have hexp : Tendsto (fun ε : ℝ => Real.exp (ε * (k.natAbs : ℝ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.continuousAt.tendsto.comp harg)
    have hconst : Tendsto (fun _ : ℝ => v k)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (v k)) := tendsto_const_nhds
    have hcut : Tendsto (fun ε : ℝ => secondaryCutoff v ε k)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have hmin := hexp.min hconst
      have hminval : min 1 (v k) = 1 := min_eq_left
        (subexponentialWeight_ge_one v hv k)
      simpa [secondaryCutoff, hminval] using hmin
    have hsq := hcut.mul hcut
    have henergy : Tendsto
        (fun _ : ℝ => (‖(ψ true : ℤ → ℂ) k‖ ^ 2 +
          ‖(ψ false : ℤ → ℂ) k‖ ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (‖(ψ true : ℤ → ℂ) k‖ ^ 2 +
          ‖(ψ false : ℤ → ℂ) k‖ ^ 2)) := tendsto_const_nhds
    have hmul := henergy.mul (hsq.const_mul (w k ^ 2))
    simpa [summand, limitSummand, truncatedProductWeight, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hmul
  have hdom : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ k, ‖summand ε k‖ ≤ bound k := by
    filter_upwards with ε
    intro k
    have hcutpos := truncatedProductWeight_pos w v hw hv ε k
    have hWpos := hW k
    have hup : truncatedProductWeight w v ε k ≤ W k := by
      have hcut : secondaryCutoff v ε k ≤ v k := min_le_right _ _
      unfold truncatedProductWeight W productWeight
      exact mul_le_mul_of_nonneg_left hcut (hw k).le
    have hsquare : truncatedProductWeight w v ε k ^ 2 ≤ W k ^ 2 :=
      (sq_le_sq₀ hcutpos.le hWpos.le).2 hup
    have henergy : 0 ≤ (‖(ψ true : ℤ → ℂ) k‖ ^ 2 +
        ‖(ψ false : ℤ → ℂ) k‖ ^ 2) := by positivity
    rw [Real.norm_of_nonneg]
    · exact mul_le_mul_of_nonneg_right hsquare henergy
    · exact mul_nonneg (sq_nonneg _) henergy
  have hsum := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hcutnorm (ε : ℝ) :
      pairNorm (truncatedProductWeight w v ε) (truncatedProductWeight_pos w v hw hv ε)
        (cutoffInclusion w v hw hv ε ψ) ^ 2 = ∑' k, summand ε k := by
    let V : ℤ → ℝ := truncatedProductWeight w v ε
    let hV : ∀ k, 0 < V k := truncatedProductWeight_pos w v hw hv ε
    letI : Fact (∀ k : ℤ, 0 < V k ^ 2) :=
      ⟨fun k => sq_pos_of_pos (hV k)⟩
    change ‖cutoffInclusion w v hw hv ε ψ‖ ^ 2 = _
    rw [NlsGge.Atomic.DM048.weightedPairHilbert_norm_sq]
    apply tsum_congr
    intro k
    have htrue : (cutoffInclusion w v hw hv ε ψ true : ℤ → ℂ) k =
        (ψ true : ℤ → ℂ) k := by
      exact pairWeightComparison_coeff _ _ _ _ _ ψ true k
    have hfalse : (cutoffInclusion w v hw hv ε ψ false : ℤ → ℂ) k =
        (ψ false : ℤ → ℂ) k := by
      exact pairWeightComparison_coeff _ _ _ _ _ ψ false k
    simp only [summand, truncatedProductWeight, htrue, hfalse]
  have hbaseNorm : pairNorm w hw (baseInclusion w v hw hv ψ) ^ 2 =
      ∑' k, limitSummand k := by
    letI : Fact (∀ k : ℤ, 0 < w k ^ 2) :=
      ⟨fun k => sq_pos_of_pos (hw k)⟩
    change ‖baseInclusion w v hw hv ψ‖ ^ 2 = _
    rw [NlsGge.Atomic.DM048.weightedPairHilbert_norm_sq]
    apply tsum_congr
    intro k
    have htrue : (baseInclusion w v hw hv ψ true : ℤ → ℂ) k =
        (ψ true : ℤ → ℂ) k := by
      exact pairWeightComparison_coeff _ _ _ _ _ ψ true k
    have hfalse : (baseInclusion w v hw hv ψ false : ℤ → ℂ) k =
        (ψ false : ℤ → ℂ) k := by
      exact pairWeightComparison_coeff _ _ _ _ _ ψ false k
    simp only [limitSummand, htrue, hfalse]
  have hnormSq : Tendsto
      (fun ε : ℝ => pairNorm (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε)
        (cutoffInclusion w v hw hv ε ψ) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (pairNorm w hw (baseInclusion w v hw hv ψ) ^ 2)) := by
    have hsum' : Tendsto (fun ε : ℝ => pairNorm (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε)
        (cutoffInclusion w v hw hv ε ψ) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑' k, limitSummand k)) :=
      (tendsto_congr' (Eventually.of_forall fun ε => (hcutnorm ε).symm)).1 hsum
    simpa only [← hbaseNorm] using hsum'
  exact hnormSq

/-- Norm convergence follows from convergence of the squared norms. -/
theorem truncated_secondary_weight_norm_tendsto (w v : ℤ → ℝ)
    (hw : ∀ k, 0 < w k) (hv : KSTSubexponentialWeight v)
    (ψ : PairCarrier (productWeight w v) (fun k => mul_pos (hw k)
      (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)))) :
    Tendsto
      (fun ε : ℝ => pairNorm (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε) (cutoffInclusion w v hw hv ε ψ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (pairNorm w hw (baseInclusion w v hw hv ψ))) := by
  have hsq := truncated_secondary_weight_sq_norm_tendsto w v hw hv ψ
  have hcont := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm (W : ℤ → ℝ) (hW : ∀ k, 0 < W k) (x : PairCarrier W hW) :
      Real.sqrt (pairNorm W hW x ^ 2) = pairNorm W hW x := by
    letI : Fact (∀ k : ℤ, 0 < W k ^ 2) := ⟨fun k => sq_pos_of_pos (hW k)⟩
    change Real.sqrt (‖x‖ ^ 2) = ‖x‖
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact norm_nonneg x
  have h' : Tendsto
      (fun ε : ℝ => pairNorm (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε) (cutoffInclusion w v hw hv ε ψ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.sqrt (pairNorm w hw (baseInclusion w v hw hv ψ) ^ 2))) :=
    (tendsto_congr' (Eventually.of_forall fun ε =>
      (hnorm (truncatedProductWeight w v ε) (truncatedProductWeight_pos w v hw hv ε)
        (cutoffInclusion w v hw hv ε ψ)).symm)).2 hcont
  simpa only [hnorm] using h'

/-- A subexponential secondary profile is eventually below each positive
exponential rate. -/
private theorem kstLogRatio_tendsto_logProfile (v : ℤ → ℝ)
    (hv : KSTSubexponentialWeight v) :
    Tendsto (fun n : ℕ+ => NlsGge.Atomic.DM047.logProfile v n / (n : ℝ))
      atTop (nhds 0) := by
  rcases hv with ⟨_, _, _, _, hlim, _⟩
  change Tendsto (fun n : ℕ+ => Real.log (v (n : ℤ)) / (n : ℝ))
    atTop (nhds 0) at hlim
  simpa [NlsGge.Atomic.DM047.logProfile, NlsGge.Atomic.KST043.KSTLogRatio] using hlim

/-- The retained cutoff agrees with the full product weight away from a finite
central interval.  The interval can contain zero when `v 0 > 1`; this is why
the source permits `v 0 ≥ 1` rather than normalizing `v 0` to one. -/
theorem truncated_secondary_weight_eq_product_off_finite
    (w v : ℤ → ℝ) (hw : ∀ k, 0 < w k)
    (hv : KSTSubexponentialWeight v) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℤ, N < k.natAbs →
      truncatedProductWeight w v ε k = productWeight w v k := by
  have hvpos : ∀ k, 0 < v k := fun k =>
    lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)
  have heven : ∀ k : ℤ, v (-k) = v k := hv.2.1
  have h := NlsGge.Atomic.DM049.repairedCutoff_eq_factorized_off_finite
    w v hvpos heven (kstLogRatio_tendsto_logProfile v hv) hε
  simpa [truncatedProductWeight, productWeight,
    NlsGge.Atomic.DM048.repairedCutoffWeight,
    NlsGge.Atomic.DM048.factorizedWeight] using h

/-- Finite modification preserves the actual weighted-pair space, with
coefficient-preserving maps and equivalent Hilbert norms in both directions. -/
theorem truncated_secondary_weight_pair_equivalent
    (w v : ℤ → ℝ) (hw : ∀ k, 0 < w k)
    (hv : KSTSubexponentialWeight v) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ ψ : NlsGge.Atomic.DM049.WeightedPairHilbertOfPositive
          (NlsGge.Atomic.DM048.factorizedWeight w v)
          (fun k => mul_pos (hw k)
            (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))),
        ∃ χ : NlsGge.Atomic.DM049.WeightedPairHilbertOfPositive
            (NlsGge.Atomic.DM048.repairedCutoffWeight w v ε)
            (NlsGge.Atomic.DM048.repairedCutoff_pos w v ε hw
              (fun k => lt_of_lt_of_le zero_lt_one
                (subexponentialWeight_ge_one v hv k))),
          NlsGge.Atomic.DM049.weightedPairCoefficientsOfPositive
              (NlsGge.Atomic.DM048.repairedCutoffWeight w v ε)
              (NlsGge.Atomic.DM048.repairedCutoff_pos w v ε hw
                (fun k => lt_of_lt_of_le zero_lt_one
                  (subexponentialWeight_ge_one v hv k))) χ =
            NlsGge.Atomic.DM049.weightedPairCoefficientsOfPositive
              (NlsGge.Atomic.DM048.factorizedWeight w v)
              (fun k => mul_pos (hw k)
                (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ ∧
          NlsGge.Atomic.DM049.weightedPairNormOfPositive
              (NlsGge.Atomic.DM048.repairedCutoffWeight w v ε)
              (NlsGge.Atomic.DM048.repairedCutoff_pos w v ε hw
                (fun k => lt_of_lt_of_le zero_lt_one
                  (subexponentialWeight_ge_one v hv k))) χ ≤
            C * NlsGge.Atomic.DM049.weightedPairNormOfPositive
              (NlsGge.Atomic.DM048.factorizedWeight w v)
              (fun k => mul_pos (hw k)
                (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ) ∧
      (∀ χ : NlsGge.Atomic.DM049.WeightedPairHilbertOfPositive
          (NlsGge.Atomic.DM048.repairedCutoffWeight w v ε)
          (NlsGge.Atomic.DM048.repairedCutoff_pos w v ε hw
            (fun k => lt_of_lt_of_le zero_lt_one
              (subexponentialWeight_ge_one v hv k))),
        ∃ ψ : NlsGge.Atomic.DM049.WeightedPairHilbertOfPositive
            (NlsGge.Atomic.DM048.factorizedWeight w v)
            (fun k => mul_pos (hw k)
              (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))),
          NlsGge.Atomic.DM049.weightedPairCoefficientsOfPositive
              (NlsGge.Atomic.DM048.factorizedWeight w v)
              (fun k => mul_pos (hw k)
                (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ =
            NlsGge.Atomic.DM049.weightedPairCoefficientsOfPositive
              (NlsGge.Atomic.DM048.repairedCutoffWeight w v ε)
              (NlsGge.Atomic.DM048.repairedCutoff_pos w v ε hw
                (fun k => lt_of_lt_of_le zero_lt_one
                  (subexponentialWeight_ge_one v hv k))) χ ∧
          NlsGge.Atomic.DM049.weightedPairNormOfPositive
              (NlsGge.Atomic.DM048.factorizedWeight w v)
              (fun k => mul_pos (hw k)
                (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ ≤
            C * NlsGge.Atomic.DM049.weightedPairNormOfPositive
              (NlsGge.Atomic.DM048.repairedCutoffWeight w v ε)
              (NlsGge.Atomic.DM048.repairedCutoff_pos w v ε hw
                (fun k => lt_of_lt_of_le zero_lt_one
                  (subexponentialWeight_ge_one v hv k))) χ) := by
  have hvpos : ∀ k, 0 < v k := fun k =>
    lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)
  exact NlsGge.Atomic.DM049.repairedCutoff_pair_equivalent
    w v hw hvpos hv.2.1 (kstLogRatio_tendsto_logProfile v hv) hε

/-- The two coefficient spaces are equal as sets; the preceding theorem gives
the coefficient-preserving identifications and both norm bounds. -/
theorem truncated_secondary_weight_coefficient_space_eq
    (w v : ℤ → ℝ) (hw : ∀ k, 0 < w k)
    (hv : KSTSubexponentialWeight v) {ε : ℝ} (hε : 0 < ε) :
    pairCoefficientSpace (productWeight w v)
        (fun k => mul_pos (hw k)
          (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k)) ) =
      pairCoefficientSpace (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε) := by
  obtain ⟨C, hC, hforward, hbackward⟩ :=
    truncated_secondary_weight_pair_equivalent w v hw hv hε
  ext a
  change (∃ ψ : PairCarrier (productWeight w v)
      (fun k => mul_pos (hw k)
          (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))),
      pairCoefficients (productWeight w v)
        (fun k => mul_pos (hw k)
          (lt_of_lt_of_le zero_lt_one (subexponentialWeight_ge_one v hv k))) ψ = a) ↔
    (∃ χ : PairCarrier (truncatedProductWeight w v ε)
      (truncatedProductWeight_pos w v hw hv ε),
      pairCoefficients (truncatedProductWeight w v ε)
        (truncatedProductWeight_pos w v hw hv ε) χ = a)
  constructor
  · rintro ⟨ψ, hψ⟩
    obtain ⟨χ, hχ, _⟩ := hforward ψ
    exact ⟨χ, hχ.trans hψ⟩
  · rintro ⟨χ, hχ⟩
    obtain ⟨ψ, hψ, _⟩ := hbackward χ
    exact ⟨ψ, hψ.trans hχ⟩

end NlsGge.Atomic.KST044
