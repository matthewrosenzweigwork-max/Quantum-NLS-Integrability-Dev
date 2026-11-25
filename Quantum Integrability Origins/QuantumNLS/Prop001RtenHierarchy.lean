import QuantumNLS.Prop001Constants
import QuantumNLS.TraceIdeal
import QuantumNLS.Prop001Dynamics
import Mathlib.Data.Nat.Factorial.BigOperators
import QuantumNLS.PlacementFusion
import QuantumNLS.PlacementOverlap
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Calculus.MeanValue


/-! Actual zero extension of the PROP-001 finite marginals and all-rank
initial bounds. The commutator estimate is on the constructed trace norm. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace QuantumNLS.Prop001
open TensorCarrier PhysicalTensor TraceClass TraceCompact TraceIdeal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev RankOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (k : ℕ) :=
  HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k

/-- The source convention at every rank, including k>N. -/
def extendedMarginal (A : Interactions H) (N k : ℕ) (t : ℝ)
    (ψ : SymSector ℂ H N) : RankOperator H k :=
  if hk : k ≤ N then marginal A N k hk t ψ else 0

def coherentProjector (k : ℕ) (v : H) : RankOperator H k :=
  InnerProductSpace.rankOne ℂ (htpow k v : HilbertTensorPower ℂ H k) (htpow k v)

theorem coherentProjector_traceNorm (k : ℕ) (v : H) (hv : ‖v‖ = 1) :
    traceNorm (coherentProjector k v) = 1 := by
  have h := traceNorm_reducedDensityN k k le_rfl
    (htpow k v : HilbertTensorPower ℂ H k)
  simpa [reducedDensityN_htpow, norm_htpow, hv, coherentProjector] using h

theorem extendedMarginal_of_le (A : Interactions H) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) :
    extendedMarginal A N k t ψ = marginal A N k hk t ψ := dite_eq_left hk

theorem extendedMarginal_of_gt (A : Interactions H) (N k : ℕ) (hk : N < k)
    (t : ℝ) (ψ : SymSector ℂ H N) : extendedMarginal A N k t ψ = 0 :=
  dite_eq_right (not_le.mpr hk)

theorem extendedMarginal_error_le_two (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N k : ℕ) (t : ℝ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (v : H) (hv : ‖v‖ = 1) :
    traceNorm (extendedMarginal A N k t ψ - coherentProjector k v) ≤ 2 := by
  by_cases hk : k ≤ N
  · rw [extendedMarginal_of_le A N k hk]
    exact marginal_error_le_two A hA N k hk t ψ hψ v hv
  · rw [extendedMarginal, dite_eq_right hk, zero_sub, ← neg_one_smul ℂ,
      traceNorm_smul, coherentProjector_traceNorm k v hv]
    norm_num

/-- Exact initial product marginal, not an assumed initial hierarchy. -/
theorem extendedMarginal_initial (A : Interactions H) (N k : ℕ)
    (u : H) (hu : ‖u‖ = 1) :
    extendedMarginal A N k 0 (productVector N u) =
      if k ≤ N then coherentProjector k u else 0 := by
  by_cases hk : k ≤ N
  · rw [extendedMarginal_of_le A N k hk, ite_eq_left hk]
    change reducedDensityN N k hk
      (quantumEvolution A N 0 (productVector N u) : HilbertTensorPower ℂ H N) = _
    rw [show quantumEvolution A N 0 = 1 from LinearTailPhysicalEvolution.evolution_zero _]
    change reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ H N) = _
    simp [reducedDensityN_htpow, hu, coherentProjector]
  · simp [extendedMarginal, hk]

theorem extendedMarginal_initial_error (A : Interactions H) (N k : ℕ)
    (u : H) (hu : ‖u‖ = 1) :
    traceNorm (extendedMarginal A N k 0 (productVector N u) - coherentProjector k u) =
      if k ≤ N then 0 else 1 := by
  rw [extendedMarginal_initial A N k u hu]
  split_ifs
  · simp [traceNorm_eq_zero_iff]
  · rw [zero_sub, ← neg_one_smul ℂ, traceNorm_smul,
      coherentProjector_traceNorm k u hu]
    norm_num

/-- All-rank source initial estimate, with positive particle number. -/
theorem extendedMarginal_initial_error_le (A : Interactions H) (N k : ℕ)
    (hN : 0 < N) (u : H) (hu : ‖u‖ = 1) :
    traceNorm (extendedMarginal A N k 0 (productVector N u) - coherentProjector k u) ≤
      ENNReal.ofReal ((k : ℝ) / N) := by
  rw [extendedMarginal_initial_error A N k u hu]
  split_ifs with hk
  · exact bot_le
  · have hNk : (N : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt (not_le.mp hk))
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have h : (1 : ℝ) ≤ (k : ℝ) / N := (le_div_iff₀ hNp).mpr (by simpa using hNk)
    exact_mod_cast (ENNReal.ofReal_le_ofReal h)

/-- The commutator bound used before the hierarchy partial trace. -/
theorem traceNorm_commutator_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A T : E →L[ℂ] E) :
    traceNorm (A * T - T * A) ≤ 2 * ENNReal.ofReal ‖A‖ * traceNorm T := by
  have hn : traceNorm (-(T * A)) = traceNorm (T * A) := by
    rw [← neg_one_smul ℂ, traceNorm_smul]
    simp
  calc
    _ ≤ traceNorm (A * T) + traceNorm (-(T * A)) := by
      simpa only [sub_eq_add_neg] using traceNorm_add_le (A * T) (-(T * A))
    _ = traceNorm (A * T) + traceNorm (T * A) := by rw [hn]
    _ ≤ ENNReal.ofReal ‖A‖ * traceNorm T + traceNorm T * ENNReal.ofReal ‖A‖ :=
      add_le_add (traceNorm_mul_left_le A T) (traceNorm_mul_right_le T A)
    _ = _ := by ring

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.extendedMarginal
#print axioms QuantumNLS.Prop001.coherentProjector_traceNorm
#print axioms QuantumNLS.Prop001.extendedMarginal_of_le
#print axioms QuantumNLS.Prop001.extendedMarginal_of_gt
#print axioms QuantumNLS.Prop001.extendedMarginal_error_le_two
#print axioms QuantumNLS.Prop001.extendedMarginal_initial
#print axioms QuantumNLS.Prop001.extendedMarginal_initial_error
#print axioms QuantumNLS.Prop001.extendedMarginal_initial_error_le
#print axioms QuantumNLS.Prop001.traceNorm_commutator_le


/-! Exact numerical coefficients in the bounded PROP-001 hierarchy.
These identities do not assume a hierarchy equation. Index n is r-1. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Prop001

/-- One-overlap coefficient divided by r, including zero for impossible ranks. -/
def alpha (N k n : ℕ) : ℝ := ((N - k).descFactorial n : ℝ) / (N : ℝ) ^ n

theorem alpha_nonneg (N k n : ℕ) : 0 ≤ alpha N k n := by unfold alpha; positivity

theorem alpha_le_one (N k n : ℕ) : alpha N k n ≤ 1 := by
  unfold alpha
  apply div_le_one_of_le₀
  · exact_mod_cast (Nat.descFactorial_le n (Nat.sub_le N k)).trans (Nat.descFactorial_le_pow N n)
  · positivity

theorem alpha_zero (N k : ℕ) : alpha N k 0 = 1 := by simp [alpha]

theorem alpha_succ (N k n : ℕ) :
    alpha N k (n + 1) = ((N - k - n : ℕ) : ℝ) / N * alpha N k n := by
  simp only [alpha, Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
  ring

/-- Exact source deficit, with n=r-1. -/
theorem alpha_deficit (N k n : ℕ) (hN : 0 < N) (hn : k + n ≤ N) :
    0 ≤ 1 - alpha N k n ∧
      1 - alpha N k n ≤ ((n : ℝ) * k + (n : ℝ) * (n - 1) / 2) / N := by
  refine ⟨sub_nonneg.mpr (alpha_le_one N k n), ?_⟩
  induction n with
  | zero => simp [alpha_zero]
  | succ n ih =>
    have hkn : k + n ≤ N := by omega
    have hind := ih hkn
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hcast : ((N - k - n : ℕ) : ℝ) = (N : ℝ) - k - n := by
      rw [Nat.cast_sub (by omega : n ≤ N - k), Nat.cast_sub (by omega : k ≤ N)]
    have hp : 0 ≤ ((k : ℝ) + n) / N := by positivity
    have ha := alpha_le_one N k n
    have hid : 1 - alpha N k (n + 1) =
        (1 - alpha N k n) + ((k : ℝ) + n) / N * alpha N k n := by
      rw [alpha_succ, hcast]
      field_simp
      ring
    rw [hid]
    have hb := mul_le_mul_of_nonneg_left ha hp
    push_cast
    calc
      _ ≤ (((n : ℝ) * k + n * (n - 1) / 2) / N) + ((k : ℝ) + n) / N :=
        add_le_add hind (by simpa using hb)
      _ = _ := by ring

/-- The weaker printed upper bound, now for every admissible n=r-1. -/
theorem alpha_deficit_coarse (N k n : ℕ) (hN : 0 < N) (hn : k + n ≤ N) :
    1 - alpha N k n ≤ ((n + 1 : ℕ) : ℝ) * (k + (n + 1 : ℕ)) / N := by
  refine (alpha_deficit N k n hN hn).2.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast
  nlinarith [show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ n by positivity]

/-- Scalar coefficient of one fixed ell-subset after choosing the spectators. -/
def hierarchyCoefficient (N k r ell : ℕ) : ℝ :=
  (r.factorial : ℝ) * (N : ℝ) / (N : ℝ) ^ r * ((N - k).choose (r - ell) : ℝ)

/-- One overlap has exactly the printed coefficient r alpha. -/
theorem hierarchyCoefficient_one (N k n : ℕ) (hN : 0 < N) :
    hierarchyCoefficient N k (n + 1) 1 = (n + 1 : ℕ) * alpha N k n := by
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold hierarchyCoefficient alpha
  rw [Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul, pow_succ]
  field_simp

/-- The binomial-normalized generator has the raw-subset coefficient r! N/N^r. -/
theorem generator_subset_coefficient (N r : ℕ) (hr : r ≤ N) :
    (N : ℝ) * theta N r / (N.choose r : ℝ) = (r.factorial : ℝ) * N / (N : ℝ) ^ r := by
  have hc : (N.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hr))
  unfold theta
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.alpha_nonneg
#print axioms QuantumNLS.Prop001.alpha_le_one
#print axioms QuantumNLS.Prop001.alpha_zero
#print axioms QuantumNLS.Prop001.alpha_succ
#print axioms QuantumNLS.Prop001.alpha_deficit
#print axioms QuantumNLS.Prop001.alpha_deficit_coarse
#print axioms QuantumNLS.Prop001.hierarchyCoefficient_one
#print axioms QuantumNLS.Prop001.generator_subset_coefficient


/-! The literal two-or-more-overlap hypergeometric bound. The probability
is a finite sum of the frozen normalized overlap coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Prop001
open PlacementFusion

/-- Exact count of r-subsets having at least two entries in the k-block.
The index s enumerates intersection sizes s+2. -/
def multipleOverlapCount (N k r : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (r - 1), k.choose (s + 2) * (N - k).choose (r - (s + 2))

def multipleOverlapProbability (N k r : ℕ) : ℝ :=
  (multipleOverlapCount N k r : ℝ) / (N.choose r : ℝ)

theorem multipleOverlapProbability_eq_sum (N k r : ℕ) :
    multipleOverlapProbability N k r =
      ∑ s ∈ Finset.range (r - 1), overlapCoefficient N k r (s + 2) := by
  unfold multipleOverlapProbability multipleOverlapCount
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  have hsr : s + 2 ≤ r := by have := Finset.mem_range.mp hs; omega
  simp [overlapCoefficient, hsr]

/-- Count pairs of selected coordinates in the k-block. Every subset with
at least two overlaps contributes at least one such pair. -/
theorem multipleOverlapCount_le (N k r : ℕ) (hk : k ≤ N) :
    multipleOverlapCount N k r ≤ k.choose 2 * (N - 2).choose (r - 2) := by
  by_cases hk2 : 2 ≤ k
  · by_cases hr2 : 2 ≤ r
    · have hsum :
          (∑ s ∈ Finset.range (r - 1),
            (k - 2).choose s * (N - k).choose (r - (s + 2))) =
            (N - 2).choose (r - 2) := by
        have hv := Nat.add_choose_eq (k - 2) (N - k) (r - 2)
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
        have hN : k - 2 + (N - k) = N - 2 := by omega
        rw [hN] at hv
        simpa only [Nat.succ_eq_add_one, show r - 2 + 1 = r - 1 by omega,
          show ∀ s, r - 2 - s = r - (s + 2) by omega] using hv.symm
      unfold multipleOverlapCount
      calc
        _ ≤ ∑ s ∈ Finset.range (r - 1),
            (k.choose 2 * (k - 2).choose s) * (N - k).choose (r - (s + 2)) := by
          apply Finset.sum_le_sum
          intro s _
          apply Nat.mul_le_mul_right
          have hp : 1 ≤ (s + 2).choose 2 := Nat.choose_pos (by omega)
          have hm := Nat.choose_mul (n := k) (k := s + 2) (s := 2) (by omega)
          rw [show s + 2 - 2 = s by omega] at hm
          calc
            k.choose (s + 2) ≤ k.choose (s + 2) * (s + 2).choose 2 :=
              Nat.le_mul_of_pos_right _ hp
            _ = _ := hm
        _ = k.choose 2 * (∑ s ∈ Finset.range (r - 1),
            (k - 2).choose s * (N - k).choose (r - (s + 2))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = _ := by rw [hsum]
    · have hr : r - 1 = 0 := by omega
      simp [multipleOverlapCount, hr]
  · have hz : ∀ s, k.choose (s + 2) = 0 := fun s => Nat.choose_eq_zero_of_lt (by omega)
    simp [multipleOverlapCount, hz]

/-- The usual hypergeometric pair bound, in binomial form. -/
theorem multipleOverlapProbability_le_choose (N k r : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hr : r ≤ N) :
    multipleOverlapProbability N k r ≤
      (r.choose 2 : ℝ) * (k.choose 2 : ℝ) / (N.choose 2 : ℝ) := by
  by_cases hr2 : 2 ≤ r
  · have hcN : (N.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_ne_zero hr)
    have hc2 : (N.choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_ne_zero hN)
    have hm : (N.choose r : ℝ) * (r.choose 2 : ℝ) =
        (N.choose 2 : ℝ) * ((N - 2).choose (r - 2) : ℝ) := by
      exact_mod_cast (Nat.choose_mul (n := N) hr2)
    unfold multipleOverlapProbability
    have hcount : (multipleOverlapCount N k r : ℝ) ≤
        (k.choose 2 : ℝ) * ((N - 2).choose (r - 2) : ℝ) := by
      exact_mod_cast multipleOverlapCount_le N k r hk
    refine (div_le_div_of_nonneg_right hcount
      (by positivity : (0 : ℝ) ≤ N.choose r)).trans (le_of_eq ?_)
    apply (div_eq_div_iff hcN hc2).mpr
    calc
      _ = (k.choose 2 : ℝ) * ((N.choose 2 : ℝ) * ((N - 2).choose (r - 2) : ℝ)) := by ring
      _ = (k.choose 2 : ℝ) * ((N.choose r : ℝ) * (r.choose 2 : ℝ)) := by rw [← hm]
      _ = _ := by ring
  · have hr0 : r - 1 = 0 := by omega
    have hz : r.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [multipleOverlapProbability, multipleOverlapCount, hr0, hz]

/-- Eq. A2-hypergeometric, literally in descending-factorial notation. -/
theorem multipleOverlapProbability_le (N k r : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hr : r ≤ N) :
    multipleOverlapProbability N k r ≤
      (r.descFactorial 2 : ℝ) * (k.descFactorial 2 : ℝ) /
        (2 * (N.descFactorial 2 : ℝ)) := by
  refine (multipleOverlapProbability_le_choose N k r hN hk hr).trans (le_of_eq ?_)
  simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  norm_num
  ring

/-- The printed bound on the norm majorant for all multi-overlap terms of
one interaction rank, including the N theta factor of the actual generator. -/
theorem multipleOverlap_generator_bound (N k r : ℕ) (hN : 2 ≤ N)
    (hk : k ≤ N) (hr : r ≤ N) (M : ℝ) (hM : 0 ≤ M) :
    2 * N * theta N r * M * multipleOverlapProbability N k r ≤
      2 * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * M / N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNm : (0 : ℝ) < (N - 1 : ℕ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hprob := multipleOverlapProbability_le N k r hN hk hr
  have ht0 := theta_nonneg N r
  have ht1 := theta_le_one N r
  have hp0 : 0 ≤ multipleOverlapProbability N k r := by
    unfold multipleOverlapProbability; positivity
  have htheta : 2 * (N : ℝ) * theta N r * M * multipleOverlapProbability N k r ≤
      2 * N * M * multipleOverlapProbability N k r := by
    have h := mul_le_mul_of_nonneg_left ht1
      (show 0 ≤ 2 * (N : ℝ) * M * multipleOverlapProbability N k r by positivity)
    convert h using 1 <;> ring
  refine htheta.trans ?_
  have hdf (n : ℕ) : (n.descFactorial 2 : ℝ) = n * (n - 1 : ℕ) := by
    simp [Nat.descFactorial_succ, mul_comm]
  simp only [hdf] at hprob
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hden : (0 : ℝ) < 2 * ((N : ℝ) * (N - 1 : ℕ)) := by positivity
  have hrsub : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
  have hksub : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hsmall : (r : ℝ) * (r - 1 : ℕ) * ((k : ℝ) * (k - 1 : ℕ)) ≤
      (r : ℝ)^2 * (k : ℝ)^2 := by
    calc
      _ ≤ ((r : ℝ) * r) * ((k : ℝ) * k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrsub (by positivity))
          (mul_le_mul_of_nonneg_left hksub (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  have hpbound : multipleOverlapProbability N k r ≤
      (r : ℝ)^2 * (k : ℝ)^2 / (2 * ((N : ℝ) * (N - 1 : ℕ))) :=
    hprob.trans (div_le_div_of_nonneg_right hsmall hden.le)
  have hhalf : (N : ℝ) ≤ 2 * (N - 1 : ℕ) := by
    rw [hcast]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  calc
    _ ≤ (2 * (N : ℝ) * M) *
        ((r : ℝ)^2 * (k : ℝ)^2 / (2 * ((N : ℝ) * (N - 1 : ℕ)))) :=
      mul_le_mul_of_nonneg_left hpbound (by positivity)
    _ = (r : ℝ)^2 * (k : ℝ)^2 * M / (N - 1 : ℕ) := by
      field_simp
    _ ≤ 2 * (r : ℝ)^2 * (k : ℝ)^2 * M / N := by
      apply (div_le_div_iff₀ hNm hNp).mpr
      have h := mul_le_mul_of_nonneg_left hhalf
        (show 0 ≤ (r : ℝ)^2 * (k : ℝ)^2 * M by positivity)
      nlinarith [h]

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.multipleOverlapProbability_eq_sum
#print axioms QuantumNLS.Prop001.multipleOverlapCount_le
#print axioms QuantumNLS.Prop001.multipleOverlapProbability_le_choose
#print axioms QuantumNLS.Prop001.multipleOverlapProbability_le
#print axioms QuantumNLS.Prop001.multipleOverlap_generator_bound


/-! Scalar Duhamel majorants, with their printed n+1 and n+2 factors.
No hierarchy equation or propagation conclusion is a premise here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Prop001

/-- x^j/j! ≤ a^(-j) exp(a x), using the actual exponential series. -/
theorem factorial_exp_majorant {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (j : ℕ) :
    x ^ j / (j.factorial : ℝ) ≤ Real.exp (a * x) / a ^ j := by
  have h := Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) j
  rw [mul_pow] at h
  apply (le_div_iff₀ (pow_pos ha j)).mpr
  calc
    _ = a ^ j * x ^ j / (j.factorial : ℝ) := by ring
    _ ≤ _ := h

/-- Initial-data term after n substitutions. -/
theorem initial_factorial_majorant {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (n : ℕ) :
    x ^ (n + 1) / (n.factorial : ℝ) ≤
      (n + 1 : ℕ) * Real.exp (a * x) / a ^ (n + 1) := by
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have h := factorial_exp_majorant ha hx (n + 1)
  rw [Nat.factorial_succ, Nat.cast_mul] at h
  have hm := mul_le_mul_of_nonneg_left h hn.le
  convert hm using 1 <;> field_simp

/-- Forcing term after n substitutions, including its extra time integration. -/
theorem forcing_factorial_majorant {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (n : ℕ) :
    x ^ (n + 2) / ((n + 1).factorial : ℝ) ≤
      (n + 2 : ℕ) * Real.exp (a * x) / a ^ (n + 2) := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using initial_factorial_majorant ha hx (n + 1)

theorem initial_geometric_series {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    HasSum (fun n : ℕ => (n + 1 : ℕ) * rho ^ n) (1 / (1 - rho) ^ 2) := by
  have hn : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hn

theorem forcing_geometric_series {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    HasSum (fun n : ℕ => (n + 2 : ℕ) * rho ^ n) ((2 - rho) / (1 - rho) ^ 2) := by
  have hgeom := hasSum_geometric_of_lt_one h0 h1
  have hinit := initial_geometric_series h0 h1
  have hne : 1 - rho ≠ 0 := by linarith
  convert hinit.add hgeom using 1
  · ext n
    push_cast
    ring
  · field_simp
    ring

/-- Exact printed initial-data series with its common prefactor. -/
theorem initial_series_value {a N rho : ℝ} (k : ℕ)
    (h0 : 0 ≤ rho) (h1 : rho < 1) :
    HasSum (fun n : ℕ => Real.exp (a * k) / (a * N) * ((n + 1 : ℕ) * rho ^ n))
      (Real.exp (a * k) / (a * N * (1 - rho) ^ 2)) := by
  convert (initial_geometric_series h0 h1).mul_left (Real.exp (a * k) / (a * N)) using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact printed forcing series with its common prefactor. -/
theorem forcing_series_value {a C0 t N rho : ℝ} (k : ℕ)
    (h0 : 0 ≤ rho) (h1 : rho < 1) :
    HasSum (fun n : ℕ => C0 * t * Real.exp (a * k) / (a ^ 2 * N) *
        ((n + 2 : ℕ) * rho ^ n))
      (C0 * t * Real.exp (a * k) * (2 - rho) / (a ^ 2 * N * (1 - rho) ^ 2)) := by
  convert (forcing_geometric_series h0 h1).mul_left
    (C0 * t * Real.exp (a * k) / (a ^ 2 * N)) using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The unsubstituted scalar majorant tends to zero at exactly the printed
radius t C_a < a. This is a limit of the majorant, not a Duhamel construction. -/
theorem iteration_majorant_tends_to_zero {a Ca t : ℝ} (k : ℕ)
    (ha : 0 < a) (hCa : 0 ≤ Ca) (ht : 0 ≤ t) (hsmall : t * Ca < a) :
    Filter.Tendsto (fun n : ℕ => 2 * Real.exp (a * k) * (t * Ca / a) ^ n)
      Filter.atTop (nhds 0) := by
  have hr0 : 0 ≤ t * Ca / a := by positivity
  have hr1 : t * Ca / a < 1 := (div_lt_one ha).mpr hsmall
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (2 * Real.exp (a * k))

/-- The printed first-interval constants follow from rho≤1/4. -/
theorem first_interval_scalar_bound {a C0 t N rho : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C0) (ht : 0 ≤ t) (hN : 0 < N)
    (_hr0 : 0 ≤ rho) (hr : rho ≤ 1 / 4) :
    1 / (a * N * (1 - rho) ^ 2) +
        C0 * t * (2 - rho) / (a ^ 2 * N * (1 - rho) ^ 2) ≤
      (4 / a + 8 * C0 * t / a ^ 2) / N := by
  have hden : 0 < (1 - rho) ^ 2 := sq_pos_of_pos (by linarith)
  have hi : 1 / (1 - rho) ^ 2 ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg rho]
  have hf : (2 - rho) / (1 - rho) ^ 2 ≤ (8 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg rho]
  have hleft := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / (a * N) by positivity)
  have hright := mul_le_mul_of_nonneg_left hf (show 0 ≤ C0 * t / (a ^ 2 * N) by positivity)
  calc
    _ = 1 / (a * N) * (1 / (1 - rho) ^ 2) +
          C0 * t / (a ^ 2 * N) * ((2 - rho) / (1 - rho) ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ 1 / (a * N) * 4 + C0 * t / (a ^ 2 * N) * 8 := add_le_add hleft hright
    _ = _ := by ring

/-- The interpolation used at every restart, with both bounds explicit. -/
theorem restart_interpolation {d R : ℝ} (hd : 0 ≤ d) (h2 : d ≤ 2) (hR : d ≤ R) :
    d ≤ Real.sqrt (2 * R) := by
  have hsq : d ^ 2 ≤ 2 * R := by
    nlinarith [mul_le_mul h2 hR hd (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The ceiling really gives enough intervals of length at most tau. -/
theorem ceiling_subdivision {tau T : ℝ} (htau : 0 < tau) (_hT : 0 ≤ T) :
    let m := max 1 (⌈T / tau⌉₊)
    1 ≤ m ∧ 0 ≤ T / m ∧ T / m ≤ tau := by
  dsimp
  have hm : 1 ≤ max 1 (⌈T / tau⌉₊) := le_max_left _ _
  have hmp : (0 : ℝ) < (max 1 (⌈T / tau⌉₊) : ℕ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hceil := Nat.le_ceil (T / tau)
  have hmceil : (⌈T / tau⌉₊ : ℝ) ≤ (max 1 (⌈T / tau⌉₊) : ℕ) := by exact_mod_cast le_max_right 1 (⌈T / tau⌉₊)
  refine ⟨hm, div_nonneg _hT hmp.le, ?_⟩
  apply (div_le_iff₀ hmp).mpr
  have hx := (div_le_iff₀ htau).mp (hceil.trans hmceil)
  nlinarith

theorem rateExponent_positive (tau T : ℝ) : 0 < rateExponent tau T := by
  unfold rateExponent
  positivity

theorem rateExponent_le_one (tau T : ℝ) : rateExponent tau T ≤ 1 := by
  unfold rateExponent
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  exact sub_nonpos.mpr (le_max_left (1 : ℝ) (⌈T / tau⌉₊ : ℝ))

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.factorial_exp_majorant
#print axioms QuantumNLS.Prop001.initial_factorial_majorant
#print axioms QuantumNLS.Prop001.forcing_factorial_majorant
#print axioms QuantumNLS.Prop001.initial_geometric_series
#print axioms QuantumNLS.Prop001.forcing_geometric_series
#print axioms QuantumNLS.Prop001.initial_series_value
#print axioms QuantumNLS.Prop001.forcing_series_value
#print axioms QuantumNLS.Prop001.iteration_majorant_tends_to_zero

#print axioms QuantumNLS.Prop001.first_interval_scalar_bound
#print axioms QuantumNLS.Prop001.restart_interpolation
#print axioms QuantumNLS.Prop001.ceiling_subdivision
#print axioms QuantumNLS.Prop001.rateExponent_positive
#print axioms QuantumNLS.Prop001.rateExponent_le_one


/-! Differentiate actual reduced-density matrix elements along exp(-it H_N).
This is the ungrouped finite hierarchy; no marginal equation is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop001
open TensorCarrier PhysicalTensor TraceClass TensorPlacements
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual split-and-inclusion map from the symmetric N-sector. -/
def marginalSplit (N k : ℕ) (hk : k ≤ N) :
    SymSector ℂ H N →L[ℂ]
      HilbertTensor ℂ (HilbertTensorPower ℂ H k) (HilbertTensorPower ℂ H (N - k)) :=
  (splitIsometry k (N - k)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ((castHTP (Nat.add_sub_cancel' hk).symm).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (SymSector ℂ H N).subtypeL)

/-- Rank-one test observable, pulled back to the actual symmetric sector. -/
def marginalTest (N k : ℕ) (hk : k ≤ N)
    (x y : HilbertTensorPower ℂ H k) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (marginalSplit N k hk).adjoint ∘L
    ((htmap (InnerProductSpace.rankOne ℂ y x)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H (N - k)))) ∘L
        marginalSplit N k hk)

theorem marginal_matrixElement (A : Interactions H) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) (x y : HilbertTensorPower ℂ H k) :
    ⟪marginal A N k hk t ψ x, y⟫_ℂ =
      ⟪quantumEvolution A N t ψ, marginalTest N k hk x y (quantumEvolution A N t ψ)⟫_ℂ := by
  change ⟪reducedDensity _ x, y⟫_ℂ = _
  rw [inner_reducedDensity_left]
  simp only [marginalTest, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Differentiation of a bounded test along the actual finite quantum flow. -/
theorem quantum_test_derivative (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N : ℕ) (ψ : SymSector ℂ H N)
    (B : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (t : ℝ) :
    HasDerivAt (fun s => ⟪quantumEvolution A N s ψ, B (quantumEvolution A N s ψ)⟫_ℂ)
      ((-Complex.I) * ⟪quantumEvolution A N t ψ,
        (B * generator A N - generator A N * B) (quantumEvolution A N t ψ)⟫_ℂ) t := by
  apply (LinearTailPhysicalEvolution.hasDerivAt_expectation_commutator
    (generator_selfAdjoint A hA N) B ψ t).congr_deriv
  simp only [sub_apply, mul_apply_eq_comp, inner_sub_right, quantumEvolution]
  ring

/-- The actual finite marginal has this weak derivative for every matrix
entry. The generator on the right is the literal frozen H_N. -/
theorem marginal_matrixElement_derivative (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N k : ℕ) (hk : k ≤ N)
    (ψ : SymSector ℂ H N) (x y : HilbertTensorPower ℂ H k) (t : ℝ) :
    HasDerivAt (fun s => ⟪marginal A N k hk s ψ x, y⟫_ℂ)
      ((-Complex.I) * ⟪quantumEvolution A N t ψ,
        (marginalTest N k hk x y * generator A N -
          generator A N * marginalTest N k hk x y) (quantumEvolution A N t ψ)⟫_ℂ) t := by
  simp only [marginal_matrixElement]
  exact quantum_test_derivative A hA N ψ (marginalTest N k hk x y) t

/-- Zero extension has zero weak derivative at every rank above N. -/
theorem extendedMarginal_matrixElement_derivative_above (A : Interactions H)
    (N k : ℕ) (hk : N < k) (ψ : SymSector ℂ H N)
    (x y : HilbertTensorPower ℂ H k) (t : ℝ) :
    HasDerivAt (fun s => ⟪extendedMarginal A N k s ψ x, y⟫_ℂ) 0 t := by
  simp only [extendedMarginal_of_gt A N k hk, zero_apply, inner_zero_left]
  exact hasDerivAt_const t 0

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.marginalSplit
#print axioms QuantumNLS.Prop001.marginalTest
#print axioms QuantumNLS.Prop001.marginal_matrixElement
#print axioms QuantumNLS.Prop001.quantum_test_derivative
#print axioms QuantumNLS.Prop001.marginal_matrixElement_derivative
#print axioms QuantumNLS.Prop001.extendedMarginal_matrixElement_derivative_above


/-! Actual finite switches of the source classical and quantum flows.
This module constructs the switched paths, their continuity, matching,
and their ODEs away from the switch. No time-dependent propagation rate
is assumed or claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop001
open TensorCarrier PhysicalTensor TraceClass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance (priority := low) : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

/-- Two literal kernel families, with a switch at s. -/
def switchedClassical (D E : ClassicalData H) (u : Sphere H) (s t : ℝ) : H :=
  if t ≤ s then trajectory D u t else trajectory E (flow D s u) (t - s)

theorem switchedClassical_match (D E : ClassicalData H) (u : Sphere H) (s : ℝ) :
    trajectory E (flow D s u) 0 = trajectory D u s :=
  (trajectory_spec E (flow D s u)).1

theorem switchedClassical_norm (D E : ClassicalData H) (u : Sphere H) (s t : ℝ) :
    ‖switchedClassical D E u s t‖ = 1 := by
  unfold switchedClassical
  split_ifs
  · exact ((trajectory_spec D u).2.2.1 t).1
  · exact ((trajectory_spec E (flow D s u)).2.2.1 (t - s)).1

theorem switchedClassical_zero (D E : ClassicalData H) (u : Sphere H)
    (s : ℝ) (hs : 0 ≤ s) : switchedClassical D E u s 0 = u.val := by
  rw [switchedClassical, ite_eq_left hs, (trajectory_spec D u).1]

theorem switchedClassical_continuous (D E : ClassicalData H) (u : Sphere H) (s : ℝ) :
    Continuous (switchedClassical D E u s) := by
  apply Continuous.if
  · intro t ht
    have hts : t = s := by
      change t ∈ frontier (Iic s) at ht
      simpa only [frontier_Iic, mem_singleton_iff] using ht
    subst t
    rw [sub_self, switchedClassical_match]
  · exact (trajectory_spec D u).2.1.continuous
  · exact (trajectory_spec E (flow D s u)).2.1.continuous.comp (continuous_id.sub continuous_const)

theorem switchedClassical_derivative_left (D E : ClassicalData H) (u : Sphere H)
    (s t : ℝ) (ht : t < s) :
    HasDerivAt (switchedClassical D E u s)
      (Ext025A8.sourceHartreeField D.A (switchedClassical D E u s t)) t := by
  have heq : switchedClassical D E u s =ᶠ[nhds t] trajectory D u := by
    filter_upwards [eventually_lt_nhds ht] with r hr
    exact ite_eq_left hr.le
  rw [heq.eq_of_nhds]
  exact (((trajectory_spec D u).2.2.1 t).2).congr_of_eventuallyEq heq

theorem switchedClassical_derivative_right (D E : ClassicalData H) (u : Sphere H)
    (s t : ℝ) (ht : s < t) :
    HasDerivAt (switchedClassical D E u s)
      (Ext025A8.sourceHartreeField E.A (switchedClassical D E u s t)) t := by
  have heq : switchedClassical D E u s =ᶠ[nhds t]
      (fun r => trajectory E (flow D s u) (r - s)) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    exact ite_eq_right (not_le.mpr hr)
  rw [heq.eq_of_nhds]
  have hd := (((trajectory_spec E (flow D s u)).2.2.1 (t - s)).2).scomp t
    ((hasDerivAt_id t).sub_const s)
  simpa only [Function.comp_def, one_smul] using hd.congr_of_eventuallyEq heq

/-- On the quantum side the later propagator is composed with the earlier
one. The full definition is a bounded linear operator, before any vector. -/
def switchedQuantum (D E : ClassicalData H) (N : ℕ) (s t : ℝ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  if t ≤ s then quantumEvolution D.A N t else
    quantumEvolution E.A N (t - s) ∘L quantumEvolution D.A N s

theorem switchedQuantum_norm (D E : ClassicalData H) (N : ℕ) (s t : ℝ)
    (ψ : SymSector ℂ H N) : ‖switchedQuantum D E N s t ψ‖ = ‖ψ‖ := by
  unfold switchedQuantum
  split_ifs
  · exact quantumEvolution_norm D.A D.selfAdjoint N t ψ
  · rw [ContinuousLinearMap.comp_apply, quantumEvolution_norm E.A E.selfAdjoint,
      quantumEvolution_norm D.A D.selfAdjoint]

theorem switchedQuantum_match (D E : ClassicalData H) (N : ℕ) (s : ℝ)
    (ψ : SymSector ℂ H N) :
    quantumEvolution E.A N 0 (quantumEvolution D.A N s ψ) = quantumEvolution D.A N s ψ := by
  rw [show quantumEvolution E.A N 0 = 1 from LinearTailPhysicalEvolution.evolution_zero _]
  rfl

theorem switchedQuantum_continuous (D E : ClassicalData H) (N : ℕ) (s : ℝ)
    (ψ : SymSector ℂ H N) : Continuous (fun t => switchedQuantum D E N s t ψ) := by
  have hD : Continuous (fun t => quantumEvolution D.A N t ψ) :=
    continuous_iff_continuousAt.mpr (fun t => (quantumEvolution_derivative D.A N ψ t).continuousAt)
  have hE : Continuous (fun t => quantumEvolution E.A N t (quantumEvolution D.A N s ψ)) :=
    continuous_iff_continuousAt.mpr
      (fun t => (quantumEvolution_derivative E.A N (quantumEvolution D.A N s ψ) t).continuousAt)
  have heq : (fun t => switchedQuantum D E N s t ψ) =
      (fun t => if t ≤ s then quantumEvolution D.A N t ψ else
        quantumEvolution E.A N (t - s) (quantumEvolution D.A N s ψ)) := by
    funext t
    unfold switchedQuantum
    split_ifs <;> rfl
  rw [heq]
  apply Continuous.if
  · intro t ht
    have hts : t = s := by
      change t ∈ frontier (Iic s) at ht
      simpa only [frontier_Iic, mem_singleton_iff] using ht
    subst t
    rw [sub_self, switchedQuantum_match]
  · exact hD
  · exact hE.comp (continuous_id.sub continuous_const)

/-- Packet stability survives a switch with no growth factor. -/
theorem switched_packet_stability (D E : ClassicalData H) (N k : ℕ) (hk : k ≤ N)
    (s t : ℝ) (ψ φ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (reducedDensityN N k hk (switchedQuantum D E N s t ψ : HilbertTensorPower ℂ H N) -
      reducedDensityN N k hk (switchedQuantum D E N s t φ : HilbertTensorPower ℂ H N)) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  have h := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk
    (switchedQuantum D E N s t ψ : HilbertTensorPower ℂ H N)
    (switchedQuantum D E N s t φ : HilbertTensorPower ℂ H N)
  have hn (x : SymSector ℂ H N) :
      ‖(switchedQuantum D E N s t x : HilbertTensorPower ℂ H N)‖ = ‖x‖ :=
    switchedQuantum_norm D E N s t x
  have hd : ‖(switchedQuantum D E N s t ψ : HilbertTensorPower ℂ H N) -
      (switchedQuantum D E N s t φ : HilbertTensorPower ℂ H N)‖ = ‖ψ - φ‖ := by
    change ‖switchedQuantum D E N s t ψ - switchedQuantum D E N s t φ‖ = _
    rw [← map_sub, switchedQuantum_norm]
  simpa only [hn ψ, hn φ, hd, hψ, hφ, one_add_one_eq_two, mul_comm] using h

/-- Arbitrarily many finite switches, represented by the ordered sequence
of actual segment propagators. -/
def quantumSegments (N : ℕ) : List (ClassicalData H × ℝ) →
    (SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
  | [] => 1
  | (D, t) :: segments => quantumSegments N segments ∘L quantumEvolution D.A N t

def classicalSegments : List (ClassicalData H × ℝ) → Sphere H → Sphere H
  | [], u => u
  | (D, t) :: segments, u => classicalSegments segments (flow D t u)

theorem quantumSegments_norm (N : ℕ) (segments : List (ClassicalData H × ℝ))
    (ψ : SymSector ℂ H N) : ‖quantumSegments N segments ψ‖ = ‖ψ‖ := by
  induction segments generalizing ψ with
  | nil => rfl
  | cons segment segments ih =>
    obtain ⟨D,t⟩ := segment
    rw [quantumSegments, ContinuousLinearMap.comp_apply, ih, quantumEvolution_norm D.A D.selfAdjoint]

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.switchedClassical_match
#print axioms QuantumNLS.Prop001.switchedClassical_norm
#print axioms QuantumNLS.Prop001.switchedClassical_zero
#print axioms QuantumNLS.Prop001.switchedClassical_continuous
#print axioms QuantumNLS.Prop001.switchedClassical_derivative_left
#print axioms QuantumNLS.Prop001.switchedClassical_derivative_right
#print axioms QuantumNLS.Prop001.switchedQuantum_norm
#print axioms QuantumNLS.Prop001.switchedQuantum_match
#print axioms QuantumNLS.Prop001.switchedQuantum_continuous
#print axioms QuantumNLS.Prop001.switched_packet_stability
#print axioms QuantumNLS.Prop001.quantumSegments_norm


/-! Literal zero-overlap cancellation on the split tensor carrier: evolving
only spectator coordinates leaves the actual reduced density unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped InnerProductSpace
namespace QuantumNLS.Prop001
open TensorCarrier LinearTailPhysicalEvolution
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Disjoint completed-tensor placements commute before any compression. -/
theorem disjoint_htmap_commute (B : X →L[ℂ] X) (C : Y →L[ℂ] Y) :
    Commute (htmap B (ContinuousLinearMap.id ℂ Y))
      (htmap (ContinuousLinearMap.id ℂ X) C) := by
  change htmap B (ContinuousLinearMap.id ℂ Y) ∘L htmap (ContinuousLinearMap.id ℂ X) C =
    htmap (ContinuousLinearMap.id ℂ X) C ∘L htmap B (ContinuousLinearMap.id ℂ Y)
  rw [← htmap_comp, ← htmap_comp]
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

theorem spectator_selfAdjoint (C : Y →L[ℂ] Y) (hC : IsSelfAdjoint C) :
    IsSelfAdjoint (htmap (ContinuousLinearMap.id ℂ X) C) := by
  change (htmap (ContinuousLinearMap.id ℂ X) C).adjoint = _
  rw [adjoint_htmap, show C.adjoint = C from hC]
  simp only [ContinuousLinearMap.adjoint_id]

/-- Each matrix element has zero derivative when its generator acts only
on the factors that the actual reduced density traces out. -/
theorem spectator_reducedDensity_derivative (C : Y →L[ℂ] Y) (hC : IsSelfAdjoint C)
    (ψ : HilbertTensor ℂ X Y) (x y : X) (t : ℝ) :
    HasDerivAt (fun s => ⟪reducedDensity
      (evolution (htmap (ContinuousLinearMap.id ℂ X) C) s ψ) x, y⟫_ℂ) 0 t := by
  simp only [inner_reducedDensity_left]
  have hc := disjoint_htmap_commute (InnerProductSpace.rankOne ℂ y x) C
  have h := hasDerivAt_expectation_commutator (spectator_selfAdjoint C hC)
    (htmap (InnerProductSpace.rankOne ℂ y x) (ContinuousLinearMap.id ℂ Y)) ψ t
  have hz : htmap (ContinuousLinearMap.id ℂ X) C *
      htmap (InnerProductSpace.rankOne ℂ y x) (ContinuousLinearMap.id ℂ Y) -
    htmap (InnerProductSpace.rankOne ℂ y x) (ContinuousLinearMap.id ℂ Y) *
      htmap (ContinuousLinearMap.id ℂ X) C = 0 := sub_eq_zero.mpr hc.eq.symm
  simpa only [hz, zero_apply, inner_zero_right, mul_zero] using h

/-- Zero-overlap cancellation for the constructed partial trace of a pure
state, at every real time and on arbitrary complete Hilbert factors. -/
theorem spectator_reducedDensity_invariant (C : Y →L[ℂ] Y) (hC : IsSelfAdjoint C)
    (ψ : HilbertTensor ℂ X Y) (t : ℝ) :
    reducedDensity (evolution (htmap (ContinuousLinearMap.id ℂ X) C) t ψ) =
      reducedDensity ψ := by
  ext x
  apply ext_inner_right ℂ
  intro y
  have h : ∀ s, HasDerivAt (fun r => ⟪reducedDensity
      (evolution (htmap (ContinuousLinearMap.id ℂ X) C) r ψ) x, y⟫_ℂ) 0 s :=
    fun s => spectator_reducedDensity_derivative C hC ψ x y s
  have heq := is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt)
    (fun s => (h s).deriv) t 0
  simpa only [evolution_zero, one_apply_eq_self] using heq

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.disjoint_htmap_commute
#print axioms QuantumNLS.Prop001.spectator_selfAdjoint
#print axioms QuantumNLS.Prop001.spectator_reducedDensity_derivative
#print axioms QuantumNLS.Prop001.spectator_reducedDensity_invariant


/-! The two numerical contributions to the printed C0 remainder budget.
These are norm-majorant sums; identifying their sum with a bound on the
actual marginal remainder requires the finite hierarchy regrouping. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Prop001
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The missing-one-overlap scalar budget at one admissible rank. -/
theorem oneOverlap_term_bound (N k n : ℕ) (hN : 0 < N) (hk : 1 ≤ k)
    (hn : k + n ≤ N) (M : ℝ) (hM : 0 ≤ M) :
    2 * (n + 1 : ℕ) * k * (1 - alpha N k n) * M ≤
      4 * (k : ℝ) ^ 2 / N * ((n + 1 : ℕ) : ℝ) ^ 3 * M := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := alpha_deficit_coarse N k n hN hn
  have hkr : ((k : ℝ) + (n + 1 : ℕ)) ≤ 2 * k * (n + 1 : ℕ) := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hnR : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hnR)]
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 2 * (n + 1 : ℕ) * (k : ℝ) by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hkr
    (show 0 ≤ 2 * ((n + 1 : ℕ) : ℝ)^2 * k / N by positivity)
  have hbase : 2 * (n + 1 : ℕ) * k * (1 - alpha N k n) ≤
      4 * (k : ℝ)^2 / N * ((n + 1 : ℕ) : ℝ)^3 := by
    calc
      _ ≤ 2 * (n + 1 : ℕ) * k *
          (((n + 1 : ℕ) : ℝ) * (k + (n + 1 : ℕ)) / N) := hm
      _ = (2 * ((n + 1 : ℕ) : ℝ)^2 * k / N) * (k + (n + 1 : ℕ)) := by ring
      _ ≤ (2 * ((n + 1 : ℕ) : ℝ)^2 * k / N) * (2 * k * (n + 1 : ℕ)) := hm2
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hbase hM

/-- Sum of the printed one-overlap costs over all ranks that can occur. -/
theorem oneOverlap_sum_bound (A : Interactions H) (N k : ℕ)
    (hN : 0 < N) (hk : 1 ≤ k) (hkN : k ≤ N)
    (hs : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖)) :
    (∑ n ∈ Finset.range (N - k + 1),
      2 * (n + 1 : ℕ) * k * (1 - alpha N k n) * ‖A n‖) ≤
      4 * (k : ℝ) ^ 2 / N * ∑' n, ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖ := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N - k + 1),
        4 * (k : ℝ) ^ 2 / N * ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : k + n ≤ N := by have := Finset.mem_range.mp hn; omega
      exact oneOverlap_term_bound N k n hN hk hn' ‖A n‖ (ContinuousLinearMap.opNorm_nonneg (A n))
    _ = 4 * (k : ℝ) ^ 2 / N *
        ∑ n ∈ Finset.range (N - k + 1), ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Finset.range (N - k + 1)) (fun n _ => by positivity)) (by positivity)

/-- All multi-overlap costs, in the same rank-cubic norm sum. -/
theorem multipleOverlap_sum_bound (A : Interactions H) (N k : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N)
    (hs : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖)) :
    (∑ n : Fin N, 2 * N * theta N (n.val + 1) * ‖A n.val‖ *
      multipleOverlapProbability N k (n.val + 1)) ≤
      2 * (k : ℝ) ^ 2 / N * ∑' n, ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖ := by
  have hterm (n : Fin N) :
      2 * N * theta N (n.val + 1) * ‖A n.val‖ * multipleOverlapProbability N k (n.val + 1) ≤
        2 * (k : ℝ)^2 / N * ((n.val + 1 : ℕ) : ℝ)^3 * ‖A n.val‖ := by
    refine (multipleOverlap_generator_bound N k (n.val + 1) hN hk
      (Nat.succ_le_of_lt n.isLt) ‖A n.val‖ (ContinuousLinearMap.opNorm_nonneg (A n.val))).trans ?_
    have hr : (1 : ℝ) ≤ (n.val + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n.val + 1)
    have hr2 : ((n.val + 1 : ℕ) : ℝ)^2 ≤ ((n.val + 1 : ℕ) : ℝ)^3 := by
      nlinarith [mul_nonneg (sq_nonneg ((n.val + 1 : ℕ) : ℝ)) (sub_nonneg.mpr hr)]
    have hm := mul_le_mul_of_nonneg_left hr2
      (show 0 ≤ 2 * (k : ℝ)^2 / N * ‖A n.val‖ by positivity)
    convert hm using 1 <;> ring
  calc
    _ ≤ ∑ n : Fin N, 2 * (k : ℝ)^2 / N * ((n.val + 1 : ℕ) : ℝ)^3 * ‖A n.val‖ :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = 2 * (k : ℝ)^2 / N * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)^3 * ‖A n‖ := by
      rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Finset.range N) (fun n _ => by positivity)) (by positivity)

/-- The printed C0 is exactly sufficient for the sum of the two numerical
majorants. This theorem does not postulate an actual remainder norm bound. -/
theorem hierarchy_scalar_budget (D : ClassicalData H) (N k : ℕ)
    (hN : 2 ≤ N) (hk : 1 ≤ k) (hkN : k ≤ N) :
    (∑ n ∈ Finset.range (N - k + 1),
      2 * (n + 1 : ℕ) * k * (1 - alpha N k n) * ‖D.A n‖) +
    (∑ n : Fin N, 2 * N * theta N (n.val + 1) * ‖D.A n.val‖ *
      multipleOverlapProbability N k (n.val + 1)) ≤
      errorSum D.A * (k : ℝ)^2 / N := by
  have h1 := oneOverlap_sum_bound D.A N k (by omega) hk hkN D.cubic
  have h2 := multipleOverlap_sum_bound D.A N k hN hkN D.cubic
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold errorSum
  ring

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.oneOverlap_term_bound
#print axioms QuantumNLS.Prop001.oneOverlap_sum_bound
#print axioms QuantumNLS.Prop001.multipleOverlap_sum_bound
#print axioms QuantumNLS.Prop001.hierarchy_scalar_budget

/-! Derivatives of the actual coherent tensor projectors, using the frozen
source tensor multilinear map and the constructed Hartree trajectory. -/
namespace QuantumNLS.Prop001
open TensorCarrier
open scoped BigOperators InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance (priority := low) : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

/-- Literal sum of the k tensors obtained by differentiating one slot. -/
def tensorVelocity (k : ℕ) (u v : H) : HilbertTensorPower ℂ H k :=
  (Ext025A8.tensorMultilinear k).linearDeriv (fun _ => u) (fun _ => v)

omit [CompleteSpace H] in
theorem tensorVelocity_eq_sum (k : ℕ) (u v : H) :
    tensorVelocity k u v = ∑ j : Fin k,
      Ext025A8.tensorMultilinear k (Function.update (fun _ => u) j v) := by
  simp only [tensorVelocity, ContinuousMultilinearMap.linearDeriv_apply]

omit [CompleteSpace H] in
theorem tensorPower_derivative (k : ℕ) (alpha : ℝ → H) (v : H) (t : ℝ)
    (h : HasDerivAt alpha v t) :
    HasDerivAt (fun s => (htpow k (alpha s) : HilbertTensorPower ℂ H k))
      (tensorVelocity k (alpha t) v) t := by
  have hpi : HasDerivAt (fun s => (fun _ : Fin k => alpha s)) (fun _ => v) t :=
    hasDerivAt_pi.mpr (fun _ => h)
  have hd := ((Ext025A8.tensorMultilinear (H := H) k).restrictScalars ℝ).hasFDerivAt
    (fun _ => alpha t)
  convert hd.comp_hasDerivAt t hpi using 1
  · rfl
  · simp only [tensorVelocity, ContinuousMultilinearMap.linearDeriv_apply]
    rfl

/-- Actual constructed source trajectory, differentiated in every tensor slot. -/
theorem trajectory_tensor_derivative (D : ClassicalData H) (u : Sphere H) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s => (htpow k (trajectory D u s) : HilbertTensorPower ℂ H k))
      (tensorVelocity k (trajectory D u t)
        (Ext025A8.sourceHartreeField D.A (trajectory D u t))) t :=
  tensorPower_derivative k (trajectory D u) _ t ((trajectory_spec D u).2.2.1 t).2

/-- Weak derivative of the literal coherent projector, for arbitrary curves. -/
theorem coherentProjector_matrixElement_derivative (k : ℕ) (alpha : ℝ → H)
    (v : H) (t : ℝ) (h : HasDerivAt alpha v t)
    (x y : HilbertTensorPower ℂ H k) :
    HasDerivAt (fun s => ⟪coherentProjector k (alpha s) x, y⟫_ℂ)
      (⟪x, tensorVelocity k (alpha t) v⟫_ℂ * ⟪htpow k (alpha t), y⟫_ℂ +
        ⟪x, htpow k (alpha t)⟫_ℂ * ⟪tensorVelocity k (alpha t) v, y⟫_ℂ) t := by
  have hz := tensorPower_derivative k alpha v t h
  have h1 := (hasDerivAt_const t x).inner ℂ hz
  have h2 := hz.inner ℂ (hasDerivAt_const t y)
  convert! h1.mul h2 using 1 <;>
    simp only [coherentProjector, InnerProductSpace.inner_left_rankOne_apply,
      inner_zero_left, inner_zero_right, add_zero, zero_add]
  rfl

/-- Differentiation of the constructed product hierarchy, with no derivative
or evolution law of the hierarchy assumed. The identification of this
literal derivative with the infinite collision series remains separate. -/
theorem trajectory_projector_derivative (D : ClassicalData H) (u : Sphere H)
    (k : ℕ) (t : ℝ) (x y : HilbertTensorPower ℂ H k) :
    HasDerivAt (fun s => ⟪coherentProjector k (trajectory D u s) x, y⟫_ℂ)
      (⟪x, tensorVelocity k (trajectory D u t)
        (Ext025A8.sourceHartreeField D.A (trajectory D u t))⟫_ℂ *
          ⟪htpow k (trajectory D u t), y⟫_ℂ +
        ⟪x, htpow k (trajectory D u t)⟫_ℂ *
          ⟪tensorVelocity k (trajectory D u t)
            (Ext025A8.sourceHartreeField D.A (trajectory D u t)), y⟫_ℂ) t :=
  coherentProjector_matrixElement_derivative k (trajectory D u) _ t
    ((trajectory_spec D u).2.2.1 t).2 x y

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.tensorVelocity_eq_sum
#print axioms QuantumNLS.Prop001.tensorPower_derivative
#print axioms QuantumNLS.Prop001.trajectory_tensor_derivative
#print axioms QuantumNLS.Prop001.coherentProjector_matrixElement_derivative
#print axioms QuantumNLS.Prop001.trajectory_projector_derivative
#print axioms QuantumNLS.Prop001.classicalSegments

namespace QuantumNLS.Prop001
open TensorCarrier PhysicalTensor TraceClass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact expansion of the actual finite generator commutator by rank. -/
theorem generator_commutator_expansion (A : Interactions H) (N : ℕ)
    (B : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    B * generator A N - generator A N * B =
      (N : ℂ) • ∑ n : Fin N, (theta N (n.val + 1) : ℂ) •
        (B * KernelDefinition.genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val) -
          KernelDefinition.genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val) * B) := by
  ext x
  simp only [generator, mul_apply_eq_comp, sub_apply, smul_apply, sum_apply,
    map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]

/-- Ordered concatenation of arbitrary finite lists of quantum segments. -/
theorem quantumSegments_append (N : ℕ) (L M : List (ClassicalData H × ℝ)) :
    quantumSegments N (L ++ M) = quantumSegments N M ∘L quantumSegments N L := by
  induction L with
  | nil => ext ψ; rfl
  | cons segment L ih =>
    obtain ⟨D,t⟩ := segment
    simp only [List.cons_append, quantumSegments, ih, ContinuousLinearMap.comp_assoc]

theorem classicalSegments_append (L M : List (ClassicalData H × ℝ)) (u : Sphere H) :
    classicalSegments (L ++ M) u = classicalSegments M (classicalSegments L u) := by
  induction L generalizing u with
  | nil => rfl
  | cons segment L ih =>
    obtain ⟨D,t⟩ := segment
    exact ih (flow D t u)

/-- The literal packet estimate for any finite piecewise-constant schedule,
with no factor depending on the number or length of the segments. -/
theorem quantumSegments_packet_stability (N k : ℕ) (hk : k ≤ N)
    (segments : List (ClassicalData H × ℝ))
    (ψ φ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (reducedDensityN N k hk (quantumSegments N segments ψ : HilbertTensorPower ℂ H N) -
      reducedDensityN N k hk (quantumSegments N segments φ : HilbertTensorPower ℂ H N)) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  have h := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk
    (quantumSegments N segments ψ : HilbertTensorPower ℂ H N)
    (quantumSegments N segments φ : HilbertTensorPower ℂ H N)
  have hn (x : SymSector ℂ H N) :
      ‖(quantumSegments N segments x : HilbertTensorPower ℂ H N)‖ = ‖x‖ :=
    quantumSegments_norm N segments x
  have hd : ‖(quantumSegments N segments ψ : HilbertTensorPower ℂ H N) -
      (quantumSegments N segments φ : HilbertTensorPower ℂ H N)‖ = ‖ψ - φ‖ := by
    change ‖quantumSegments N segments ψ - quantumSegments N segments φ‖ = _
    rw [← map_sub, quantumSegments_norm]
  simpa only [hn ψ, hn φ, hd, hψ, hφ, one_add_one_eq_two, mul_comm] using h

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.generator_commutator_expansion
#print axioms QuantumNLS.Prop001.quantumSegments_append
#print axioms QuantumNLS.Prop001.classicalSegments_append
#print axioms QuantumNLS.Prop001.quantumSegments_packet_stability

namespace QuantumNLS.Prop001

/-- The actual event among the uniform r-subsets of N tensor coordinates. -/
def multipleOverlapEvent {N : ℕ} (P : Finset (Fin N)) (r : ℕ) : Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin N)).powersetCard r).filter (fun Q => 2 ≤ (P ∩ Q).card)

/-- The numerical count above counts exactly the actual two-overlap event. -/
theorem card_multipleOverlapEvent {N k : ℕ} (P : Finset (Fin N)) (hP : P.card = k) (r : ℕ) :
    (multipleOverlapEvent P r).card = multipleOverlapCount N k r := by
  classical
  have hmap : (↑(multipleOverlapEvent P r) : Set (Finset (Fin N))).MapsTo
      (fun Q => (P ∩ Q).card - 2) (Finset.range (r - 1)) := by
    intro Q hQ
    obtain ⟨hQr,h2⟩ := Finset.mem_filter.mp hQ
    have hcard := (Finset.mem_powersetCard.mp hQr).2
    have hle := Finset.card_le_card (Finset.inter_subset_right : P ∩ Q ⊆ Q)
    apply Finset.mem_range.mpr
    change (P ∩ Q).card - 2 < r - 1
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  unfold multipleOverlapCount
  apply Finset.sum_congr rfl
  intro s hs
  have hsr : s + 2 ≤ r := by have := Finset.mem_range.mp hs; omega
  have hf : ((multipleOverlapEvent P r).filter (fun Q => (P ∩ Q).card - 2 = s)) =
      PlacementOverlap.overlapFiber P r (s + 2) := by
    ext Q
    simp only [multipleOverlapEvent, PlacementOverlap.overlapFiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hQ,h2⟩,he⟩
      exact ⟨hQ, by omega⟩
    · rintro ⟨hQ,he⟩
      exact ⟨⟨hQ, by omega⟩, by omega⟩
  rw [hf, PlacementOverlap.card_overlapFiber P hP hsr]

/-- Eq. A2-hypergeometric for the literal event, with the actual number of
r-subsets as denominator, not a supplied probability distribution. -/
theorem actual_hypergeometric_bound {N k : ℕ} (P : Finset (Fin N)) (hP : P.card = k)
    (r : ℕ) (hN : 2 ≤ N) (hr : r ≤ N) :
    ((multipleOverlapEvent P r).card : ℝ) / (N.choose r : ℝ) ≤
      (r.descFactorial 2 : ℝ) * (k.descFactorial 2 : ℝ) / (2 * (N.descFactorial 2 : ℝ)) := by
  rw [card_multipleOverlapEvent P hP r]
  have hk : k ≤ N := by rw [← hP]; exact (Finset.card_le_univ P).trans (by simp)
  exact multipleOverlapProbability_le N k r hN hk hr

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.card_multipleOverlapEvent
#print axioms QuantumNLS.Prop001.actual_hypergeometric_bound

set_option maxHeartbeats 4000000
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.Prop001.extendedMarginal,
    ``QuantumNLS.Prop001.coherentProjector_traceNorm,
    ``QuantumNLS.Prop001.extendedMarginal_of_le,
    ``QuantumNLS.Prop001.extendedMarginal_of_gt,
    ``QuantumNLS.Prop001.extendedMarginal_error_le_two,
    ``QuantumNLS.Prop001.extendedMarginal_initial,
    ``QuantumNLS.Prop001.extendedMarginal_initial_error,
    ``QuantumNLS.Prop001.extendedMarginal_initial_error_le,
    ``QuantumNLS.Prop001.traceNorm_commutator_le,
    ``QuantumNLS.Prop001.alpha_nonneg,
    ``QuantumNLS.Prop001.alpha_le_one,
    ``QuantumNLS.Prop001.alpha_zero,
    ``QuantumNLS.Prop001.alpha_succ,
    ``QuantumNLS.Prop001.alpha_deficit,
    ``QuantumNLS.Prop001.alpha_deficit_coarse,
    ``QuantumNLS.Prop001.hierarchyCoefficient_one,
    ``QuantumNLS.Prop001.generator_subset_coefficient,
    ``QuantumNLS.Prop001.multipleOverlapProbability_eq_sum,
    ``QuantumNLS.Prop001.multipleOverlapCount_le,
    ``QuantumNLS.Prop001.multipleOverlapProbability_le_choose,
    ``QuantumNLS.Prop001.multipleOverlapProbability_le,
    ``QuantumNLS.Prop001.multipleOverlap_generator_bound,
    ``QuantumNLS.Prop001.factorial_exp_majorant,
    ``QuantumNLS.Prop001.initial_factorial_majorant,
    ``QuantumNLS.Prop001.forcing_factorial_majorant,
    ``QuantumNLS.Prop001.initial_geometric_series,
    ``QuantumNLS.Prop001.forcing_geometric_series,
    ``QuantumNLS.Prop001.initial_series_value,
    ``QuantumNLS.Prop001.forcing_series_value,
    ``QuantumNLS.Prop001.iteration_majorant_tends_to_zero,
    ``QuantumNLS.Prop001.first_interval_scalar_bound,
    ``QuantumNLS.Prop001.restart_interpolation,
    ``QuantumNLS.Prop001.ceiling_subdivision,
    ``QuantumNLS.Prop001.rateExponent_positive,
    ``QuantumNLS.Prop001.rateExponent_le_one,
    ``QuantumNLS.Prop001.marginalSplit,
    ``QuantumNLS.Prop001.marginalTest,
    ``QuantumNLS.Prop001.marginal_matrixElement,
    ``QuantumNLS.Prop001.quantum_test_derivative,
    ``QuantumNLS.Prop001.marginal_matrixElement_derivative,
    ``QuantumNLS.Prop001.extendedMarginal_matrixElement_derivative_above,
    ``QuantumNLS.Prop001.switchedClassical_match,
    ``QuantumNLS.Prop001.switchedClassical_norm,
    ``QuantumNLS.Prop001.switchedClassical_zero,
    ``QuantumNLS.Prop001.switchedClassical_continuous,
    ``QuantumNLS.Prop001.switchedClassical_derivative_left,
    ``QuantumNLS.Prop001.switchedClassical_derivative_right,
    ``QuantumNLS.Prop001.switchedQuantum_norm,
    ``QuantumNLS.Prop001.switchedQuantum_match,
    ``QuantumNLS.Prop001.switchedQuantum_continuous,
    ``QuantumNLS.Prop001.switched_packet_stability,
    ``QuantumNLS.Prop001.quantumSegments_norm,
    ``QuantumNLS.Prop001.disjoint_htmap_commute,
    ``QuantumNLS.Prop001.spectator_selfAdjoint,
    ``QuantumNLS.Prop001.spectator_reducedDensity_derivative,
    ``QuantumNLS.Prop001.spectator_reducedDensity_invariant,
    ``QuantumNLS.Prop001.oneOverlap_term_bound,
    ``QuantumNLS.Prop001.oneOverlap_sum_bound,
    ``QuantumNLS.Prop001.multipleOverlap_sum_bound,
    ``QuantumNLS.Prop001.hierarchy_scalar_budget,
    ``QuantumNLS.Prop001.tensorVelocity_eq_sum,
    ``QuantumNLS.Prop001.tensorPower_derivative,
    ``QuantumNLS.Prop001.trajectory_tensor_derivative,
    ``QuantumNLS.Prop001.coherentProjector_matrixElement_derivative,
    ``QuantumNLS.Prop001.trajectory_projector_derivative,
    ``QuantumNLS.Prop001.classicalSegments,
    ``QuantumNLS.Prop001.generator_commutator_expansion,
    ``QuantumNLS.Prop001.quantumSegments_append,
    ``QuantumNLS.Prop001.classicalSegments_append,
    ``QuantumNLS.Prop001.quantumSegments_packet_stability,
    ``QuantumNLS.Prop001.card_multipleOverlapEvent,
    ``QuantumNLS.Prop001.actual_hypergeometric_bound]
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
            throwError "PROP001Rten nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some value := ci.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "PROP001Rten missing dependency: {n}"
  Lean.logInfo m!"PROP001Rten aggregate audit PASS: {seen.size} transitive constants; 72 explicit roots; only standard dependencies. Author verification only."
