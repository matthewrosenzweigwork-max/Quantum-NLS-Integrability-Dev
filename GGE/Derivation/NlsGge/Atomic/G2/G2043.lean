import Mathlib
import NlsGge.Atomic.G1.G1062
import NlsGge.Definitions.PilotInterfaces
import NlsGge.GK38.Defs
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaDefs
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Atomic.G2.G2042
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST059
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.KST.KST030Unif
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01

/- G2-043 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/G2/G2043.lean,
   namespace NlsGge.GKDefinitionDesign.  Head VERBATIM from design STATEMENTS/G2.md "## G2-043" (gpt6pro_followup10; no Pro round entry).
   Route: G2_042 pointwise bound + gamma2 = gap^2 (gamma2_value38) + the locally uniform weighted gap tail
   `K030U.gap_tail_uniform` (support module KST030Unif) with the polynomial weight (1+|m|)^(k-1); tails by Finset splitting. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped ENNReal BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2043S

/-- The polynomial weight `(1+|m|)^(k-1)` on the doubled labels. -/
def pw (k : ℕ) (m : ℤ) : ℝ := (1 + (m.natAbs : ℝ)) ^ (k - 1)

theorem pw_slow (k : ℕ) : NlsGge.Atomic.KST.SlowWeight (pw k) (2 ^ (k - 1)) where
  one_le m := one_le_pow₀ (by have : (0 : ℝ) ≤ m.natAbs := Nat.cast_nonneg _; linarith)
  even m := by simp [pw]
  radial_mono a b h := by
    unfold pw
    apply pow_le_pow_left₀ (by positivity)
    have : (a.natAbs : ℝ) ≤ b.natAbs := by exact_mod_cast h
    linarith
  doubling n := by
    unfold pw
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : ((2 * n).natAbs : ℝ) = 2 * n.natAbs := by
      rw [Int.natAbs_mul]; push_cast; ring
    rw [this]; nlinarith [(Nat.cast_nonneg n.natAbs : (0 : ℝ) ≤ n.natAbs)]

theorem natAbs_sq_real (m : ℤ) : (m.natAbs : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
  rw [show (m.natAbs : ℝ) = |(m : ℝ)| by simp, sq_abs]

theorem jb_le (n : ℤ) : japaneseBracket n ≤ 1 + (n.natAbs : ℝ) := by
  unfold japaneseBracket
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have := natAbs_sq_real n
  nlinarith [Nat.cast_nonneg (α := ℝ) n.natAbs]

theorem pw_sq_le (k : ℕ) (m : ℤ) :
    pw k (2 * m) ^ 2 ≤ 8 ^ (k - 1) * japaneseBracket m ^ (2 * (k - 1)) := by
  unfold pw
  have h2 : ((2 * m).natAbs : ℝ) = 2 * m.natAbs := by
    rw [Int.natAbs_mul]; push_cast; ring
  have hj : japaneseBracket m ^ 2 = 1 + (m : ℝ) ^ 2 := by
    unfold japaneseBracket
    rw [Real.sq_sqrt (by positivity)]
  have ha := natAbs_sq_real m
  have key : (1 + 2 * (m.natAbs : ℝ)) ^ 2 ≤ 8 * japaneseBracket m ^ 2 := by
    rw [hj]; nlinarith [sq_nonneg ((m.natAbs : ℝ) - 1), Nat.cast_nonneg (α := ℝ) m.natAbs]
  rw [h2]
  calc ((1 + 2 * (m.natAbs : ℝ)) ^ (k - 1)) ^ 2 = ((1 + 2 * (m.natAbs : ℝ)) ^ 2) ^ (k - 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (8 * japaneseBracket m ^ 2) ^ (k - 1) := pow_le_pow_left₀ (by positivity) key _
    _ = 8 ^ (k - 1) * japaneseBracket m ^ (2 * (k - 1)) := by rw [mul_pow, ← pow_mul]

theorem jb_pw_le (k N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    japaneseBracket n ^ (k - 1) * (1 + (N : ℝ)) ^ (k - 1) ≤ pw k (2 * n) ^ 2 := by
  unfold pw
  have h2 : ((2 * n).natAbs : ℝ) = 2 * n.natAbs := by
    rw [Int.natAbs_mul]; push_cast; ring
  have hN : (N : ℝ) ≤ n.natAbs := by exact_mod_cast hn
  have hj := jb_le n
  have h0 : (0 : ℝ) ≤ n.natAbs := Nat.cast_nonneg _
  rw [h2, sq]
  have hjp : 0 ≤ japaneseBracket n := (Real.sqrt_nonneg _)
  calc japaneseBracket n ^ (k - 1) * (1 + (N : ℝ)) ^ (k - 1)
      ≤ (1 + 2 * (n.natAbs : ℝ)) ^ (k - 1) * (1 + 2 * (n.natAbs : ℝ)) ^ (k - 1) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ hjp (by linarith) _
        · exact pow_le_pow_left₀ (by positivity) (by linarith) _
        · positivity
        · positivity
    _ = _ := rfl

theorem rpow_eq_pow_two_mul (r : ℕ) (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * (r : ℝ)) = japaneseBracket n ^ (2 * r) := by
  rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
  exact Real.rpow_natCast _ _

theorem hasSum_fourier_psn (r : ℕ) (u : PhysicalL2) (hu : physicalSobolev (r : ℝ) u) :
    HasSum (fun m : ℤ => japaneseBracket m ^ (2 * r) * ‖physicalFourier u m‖ ^ 2)
      (physicalSobolevNorm (r : ℝ) u ^ 2) := by
  set f : ℤ → ℝ := fun n => japaneseBracket n ^ (2 * r) * ‖reflectedFourierL2 u n‖ ^ 2 with hf
  have hconv : ∀ n : ℤ, Real.rpow (japaneseBracket n) (2 * (r : ℝ)) * ‖reflectedFourierL2 u n‖ ^ 2 = f n := by
    intro n
    simp only [hf, rpow_eq_pow_two_mul]
  have hs : Summable f := by
    refine hu.congr (fun n => ?_)
    exact hconv n
  have hnn : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (sq_nonneg _)
  have hpsn : physicalSobolevNorm (r : ℝ) u ^ 2 = ∑' n, f n := by
    unfold physicalSobolevNorm
    rw [Real.sq_sqrt (tsum_nonneg (fun n => by rw [hconv n]; exact hnn n))]
    exact tsum_congr hconv
  have h2 : HasSum (fun m : ℤ => f (-m)) (∑' n, f n) := (Equiv.neg ℤ).hasSum_iff.2 hs.hasSum
  rw [hpsn]
  convert h2 using 1
  funext m
  simp only [hf, reflectedFourierL2_apply, reflectedFourier, japaneseBracket_neg,
    neg_neg, norm_neg]

theorem weightedNormSq_le (k : ℕ) (d : PotPair) (hd : pairSobolev ((k - 1 : ℕ) : ℝ) d) :
    NlsGge.Atomic.KST001.weightedNormSq₂ (pw k) d ≤
      ENNReal.ofReal (8 ^ (k - 1) * pairSobolevNorm ((k - 1 : ℕ) : ℝ) d ^ 2) := by
  have hwE : NlsGge.Atomic.KST001.EvenWeight (pw k) := ⟨(pw_slow k).one_le, (pw_slow k).even⟩
  rw [NlsGge.Atomic.KST001.periodOne_weightedPair_norm _ d hwE]
  unfold NlsGge.Atomic.KST001.weightedEvenFourierNormSq NlsGge.Atomic.KST001.weightedPairMode
  have h1 := hasSum_fourier_psn (k - 1) d.1 hd.1
  have h2 := hasSum_fourier_psn (k - 1) d.2 hd.2
  set g : ℤ → ℝ := fun m => 8 ^ (k - 1) * (japaneseBracket m ^ (2 * (k - 1)) * ‖physicalFourier d.1 m‖ ^ 2 +
    japaneseBracket m ^ (2 * (k - 1)) * ‖physicalFourier d.2 m‖ ^ 2) with hg
  have hgs : HasSum g (8 ^ (k - 1) * (physicalSobolevNorm ((k - 1 : ℕ) : ℝ) d.1 ^ 2 +
      physicalSobolevNorm ((k - 1 : ℕ) : ℝ) d.2 ^ 2)) := (h1.add h2).mul_left _
  have hgn : ∀ m, 0 ≤ g m := fun m => by
    have hjb : 0 ≤ japaneseBracket m := Real.sqrt_nonneg _
    simp only [hg]; positivity
  have hterm : ∀ m : ℤ, ENNReal.ofReal (pw k (2 * m) ^ 2) *
      (ENNReal.ofReal (‖physicalFourier d.1 m‖ ^ 2) + ENNReal.ofReal (‖physicalFourier d.2 m‖ ^ 2))
      ≤ ENNReal.ofReal (g m) := by
    intro m
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := pw_sq_le k m
    calc pw k (2 * m) ^ 2 * (‖physicalFourier d.1 m‖ ^ 2 + ‖physicalFourier d.2 m‖ ^ 2)
        ≤ (8 ^ (k - 1) * japaneseBracket m ^ (2 * (k - 1))) *
            (‖physicalFourier d.1 m‖ ^ 2 + ‖physicalFourier d.2 m‖ ^ 2) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = g m := by rw [hg]; ring
  have hpair : pairSobolevNorm ((k - 1 : ℕ) : ℝ) d ^ 2 =
      physicalSobolevNorm ((k - 1 : ℕ) : ℝ) d.1 ^ 2 + physicalSobolevNorm ((k - 1 : ℕ) : ℝ) d.2 ^ 2 := by
    unfold pairSobolevNorm
    exact Real.sq_sqrt (by positivity)
  calc (∑' m : ℤ, ENNReal.ofReal (pw k (2 * m) ^ 2) *
      (ENNReal.ofReal (‖physicalFourier d.1 m‖ ^ 2) + ENNReal.ofReal (‖physicalFourier d.2 m‖ ^ 2)))
      ≤ ∑' m : ℤ, ENNReal.ofReal (g m) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' m : ℤ, g m) := (ENNReal.ofReal_tsum_of_nonneg hgn hgs.summable).symm
    _ = _ := by rw [hgs.tsum_eq, hpair]

theorem l2_le_pair (r : ℕ) (d : PotPair) (hd : pairSobolev (r : ℝ) d) :
    ‖d‖ ≤ pairSobolevNorm (r : ℝ) d := by
  have hp : ∀ u : PhysicalL2, physicalSobolev (r : ℝ) u → ‖u‖ ≤ physicalSobolevNorm (r : ℝ) u := by
    intro u hu
    have := (psn_mono (Nat.zero_le r) hu).2
    simpa [NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] using this
  have hs : ∀ a b : ℝ, 0 ≤ a → a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    intro a b ha
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  rw [Prod.norm_def]
  apply max_le
  · exact (hp _ hd.1).trans (hs _ (physicalSobolevNorm (r : ℝ) d.2) (psn_nonneg r _))
  · refine (hp _ hd.2).trans ?_
    unfold pairSobolevNorm
    rw [add_comm]
    exact hs _ _ (psn_nonneg r _)


theorem pair_sub_sobolev (r : ℕ) (φ φ₀ : PotPair) (h : pairSobolev (r : ℝ) φ) (h₀ : pairSobolev (r : ℝ) φ₀) :
    pairSobolev (r : ℝ) (φ - φ₀) := by
  have hs : ∀ u v : PhysicalL2, physicalSobolev (r : ℝ) u → physicalSobolev (r : ℝ) v →
      physicalSobolev (r : ℝ) (u - v) := by
    intro u v hu hv
    rw [sub_eq_add_neg]
    exact (psn_add r hu (psn_neg r hv).1).1
  exact ⟨hs _ _ h.1 h₀.1, hs _ _ h.2 h₀.2⟩

/-- Abstract tail bookkeeping for a series dominated, outside a finite set, by `c * g`. -/
theorem series_tail {J : ℤ → ℂ} {g : ℤ → ℝ} {c B : ℝ} (N : ℕ) (hc : 0 ≤ c)
    (hg0 : ∀ n, 0 ≤ g n) (hgs : Summable g) (hgB : ∑' n, g n ≤ B)
    (hJg : ∀ n, N ≤ n.natAbs → ‖J n‖ ≤ c * g n) :
    Summable (fun n => ‖J n‖) ∧
      ∀ S : Finset ℤ, (∀ n, n ∉ S → N ≤ n.natAbs) →
        ‖(∑' n, J n) - ∑ n ∈ S, J n‖ ≤ c * B ∧
        |(∑' n, ‖J n‖) - ∑ n ∈ S, ‖J n‖| ≤ c * B := by
  classical
  have hcg : Summable (fun n => c * g n) := hgs.mul_left c
  have hcgB : ∑' n, c * g n ≤ c * B := by
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hgB hc
  -- finite part
  have hfin : Summable (fun n : ℤ => if N ≤ n.natAbs then (0 : ℝ) else ‖J n‖) := by
    apply summable_of_ne_finset_zero (s := Finset.Ioo (-(N : ℤ)) N)
    intro n hn
    have : N ≤ n.natAbs := by
      simp only [Finset.mem_Ioo, not_and_or, not_lt] at hn
      omega
    simp [this]
  have hsumN : Summable (fun n => ‖J n‖) := by
    have h1 : Summable (fun n : ℤ => if N ≤ n.natAbs then ‖J n‖ else 0) :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp)
        (fun n => by
          by_cases hn : N ≤ n.natAbs
          · simp only [hn, if_true]; exact hJg n hn
          · simp only [hn, if_false]; exact mul_nonneg hc (hg0 n)) hcg
    refine (h1.add hfin).congr (fun n => ?_)
    by_cases hn : N ≤ n.natAbs <;> simp [hn]
  refine ⟨hsumN, fun S hS => ?_⟩
  have hJs : Summable J := hsumN.of_norm
  set J' : ℤ → ℂ := fun n => if n ∈ S then 0 else J n with hJ'
  set f' : ℤ → ℝ := fun n => if n ∈ S then 0 else ‖J n‖ with hf'
  have hf'le : ∀ n, f' n ≤ c * g n := by
    intro n
    by_cases hn : n ∈ S
    · simp only [hf', hn, if_true]; exact mul_nonneg hc (hg0 n)
    · simp only [hf', hn, if_false]; exact hJg n (hS n hn)
  have hf's : Summable f' := Summable.of_nonneg_of_le (fun n => by simp only [hf']; split_ifs <;> simp) hf'le hcg
  have hJ's : Summable J' := by
    refine Summable.of_norm_bounded hf's (fun n => ?_)
    by_cases hn : n ∈ S <;> simp [hJ', hf', hn]
  have hsplitC : (∑' n, J n) = (∑' n, J' n) + ∑ n ∈ S, J n := by
    have h2 : (fun n => J n) = fun n => J' n + (if n ∈ S then J n else 0) := by
      funext n; by_cases hn : n ∈ S <;> simp [hJ', hn]
    have hfin : Summable (fun n => if n ∈ S then J n else 0) :=
      summable_of_ne_finset_zero (s := S) (fun n hn => by simp [hn])
    conv_lhs => rw [h2]
    have e2 : ∑' n, (if n ∈ S then J n else 0) = ∑ n ∈ S, J n := by
      rw [tsum_eq_sum (s := S) (fun n hn => by simp [hn])]
      exact Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [Summable.tsum_add hJ's hfin, e2]
  have hsplitR : (∑' n, ‖J n‖) = (∑' n, f' n) + ∑ n ∈ S, ‖J n‖ := by
    have h2 : (fun n => ‖J n‖) = fun n => f' n + (if n ∈ S then ‖J n‖ else 0) := by
      funext n; by_cases hn : n ∈ S <;> simp [hf', hn]
    have hfin : Summable (fun n => if n ∈ S then ‖J n‖ else 0) :=
      summable_of_ne_finset_zero (s := S) (fun n hn => by simp [hn])
    conv_lhs => rw [h2]
    have e2 : ∑' n, (if n ∈ S then ‖J n‖ else 0) = ∑ n ∈ S, ‖J n‖ := by
      rw [tsum_eq_sum (s := S) (fun n hn => by simp [hn])]
      exact Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [Summable.tsum_add hf's hfin, e2]
  have hf'nn : 0 ≤ ∑' n, f' n := tsum_nonneg (fun n => by simp only [hf']; split_ifs <;> simp)
  have hf'B : ∑' n, f' n ≤ c * B := (hf's.tsum_le_tsum hf'le hcg).trans hcgB
  constructor
  · rw [hsplitC, add_sub_cancel_right]
    calc ‖∑' n, J' n‖ ≤ ∑' n, ‖J' n‖ := norm_tsum_le_tsum_norm (hJ's.norm)
      _ ≤ ∑' n, f' n := by
          refine hJ's.norm.tsum_le_tsum (fun n => ?_) hf's
          by_cases hn : n ∈ S <;> simp [hJ', hf', hn]
      _ ≤ c * B := hf'B
  · rw [hsplitR, add_sub_cancel_right, abs_of_nonneg hf'nn]
    exact hf'B

end G2043S

theorem G2_043 (k : ℕ) (hk : 2 ≤ k) (φ₀ : PotPair)
    (hφ₀ : φ₀ ∈ sourceW) (hreg : pairSobolev ((k-1 : ℕ) : ℝ) φ₀) :
    Summable (fun n : ℤ => ‖higherAction k φ₀ n‖) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ S₀ : Finset ℤ,
      ∀ φ : PotPair, pairSobolev ((k-1 : ℕ) : ℝ) φ →
        pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ-φ₀) < δ →
        φ ∈ sourceW ∧ Summable (fun n : ℤ => ‖higherAction k φ n‖) ∧
        ∀ S : Finset ℤ, S₀ ⊆ S →
          ‖(∑' n : ℤ, higherAction k φ n) - ∑ n ∈ S, higherAction k φ n‖ < ε ∧
          |(∑' n : ℤ, ‖higherAction k φ n‖) - ∑ n ∈ S, ‖higherAction k φ n‖| < ε := by
  obtain ⟨hWo, -, hWgk, -⟩ := G2_075
  have hgk : φ₀ ∈ gkW := hWgk hφ₀
  obtain ⟨-, -, hU⟩ := G2_042 k hk
  obtain ⟨U, hUo, hφU, hUgk, C, hC, hbound⟩ := hU φ₀ hgk
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hUo.inter hWo) φ₀ ⟨hφU, hφ₀⟩
  have h0 : NlsGge.Atomic.KST001.weightedNormSq₂ (G2043S.pw k) φ₀ < ⊤ :=
    lt_of_le_of_lt (G2043S.weightedNormSq_le k φ₀ hreg) ENNReal.ofReal_lt_top
  obtain ⟨e, he, N₁, B, hB⟩ := NlsGge.ThirdConsultation.KST.K030U.gap_tail_uniform (G2043S.pw k)
    (2 ^ (k - 1)) (G2043S.pw_slow k) φ₀ h0
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hk1 : 1 ≤ k - 1 := by omega
  set P : ℝ := 8 ^ (k - 1) with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by norm_num)
  set δ₀ : ℝ := min ρ (e / P) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hρ (div_pos he (by linarith))
  -- the key local package
  have key : ∀ φ : PotPair, pairSobolev ((k-1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) < δ₀ →
      φ ∈ sourceW ∧
      (∀ n : ℤ, ‖higherAction k φ n‖ ≤ C * japaneseBracket n ^ (k - 1) * ‖gamma2 φ n‖) ∧
      ∀ N : ℕ, N₁ ≤ N → (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (G2043S.pw k (2 * n) ^ 2 * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2)
          else 0) ≤ ENNReal.ofReal B' := by
    intro φ hφ hn
    have hd := G2043S.pair_sub_sobolev (k - 1) φ φ₀ hφ hreg
    have hl2 := G2043S.l2_le_pair (k - 1) (φ - φ₀) hd
    have hmem : φ ∈ Metric.ball φ₀ ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt hl2 (lt_of_lt_of_le hn (min_le_left _ _))
    obtain ⟨hφU', hφW⟩ := hball hmem
    refine ⟨hφW, fun n => hbound φ hφU' n, fun N hN => ?_⟩
    have hsq : P * pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) ^ 2 < e ^ 2 := by
      have hpn : 0 ≤ pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) := Real.sqrt_nonneg _
      have h1 : pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) < e / P :=
        lt_of_lt_of_le hn (min_le_right _ _)
      have h2 : pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) ^ 2 < (e / P) ^ 2 :=
        pow_lt_pow_left₀ h1 hpn (by norm_num)
      calc P * pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) ^ 2 < P * (e / P) ^ 2 :=
            mul_lt_mul_of_pos_left h2 (by linarith)
        _ = e ^ 2 / P := by field_simp
        _ ≤ e ^ 2 := div_le_self (sq_nonneg _) hP1
    have henergy : NlsGge.Atomic.KST001.weightedNormSq₂ (G2043S.pw k) (φ - φ₀) <
        ENNReal.ofReal (e ^ 2) :=
      lt_of_le_of_lt (G2043S.weightedNormSq_le k (φ - φ₀) hd)
        ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hsq)
    exact (hB φ henergy N hN).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the series statement for a point of the ball
  have series : ∀ φ : PotPair, pairSobolev ((k-1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ - φ₀) < δ₀ → ∀ N : ℕ, N₁ ≤ N →
      Summable (fun n : ℤ => ‖higherAction k φ n‖) ∧
      ∀ S : Finset ℤ, (∀ n, n ∉ S → N ≤ n.natAbs) →
        ‖(∑' n : ℤ, higherAction k φ n) - ∑ n ∈ S, higherAction k φ n‖ ≤
          C / (1 + (N : ℝ)) ^ (k - 1) * B' ∧
        |(∑' n : ℤ, ‖higherAction k φ n‖) - ∑ n ∈ S, ‖higherAction k φ n‖| ≤
          C / (1 + (N : ℝ)) ^ (k - 1) * B' := by
    intro φ hφ hn N hN
    obtain ⟨hφW, hJ, hsum⟩ := key φ hφ hn
    have hφgk : φ ∈ gkW := hWgk hφW
    set g : ℤ → ℝ := fun n => if N ≤ n.natAbs then
      G2043S.pw k (2 * n) ^ 2 * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 else 0 with hg
    have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
    have hgE : (fun n => ENNReal.ofReal (g n)) = fun n : ℤ => if N ≤ n.natAbs then
        ENNReal.ofReal (G2043S.pw k (2 * n) ^ 2 * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2)
          else 0 := by
      funext n; simp only [hg]; split_ifs <;> simp
    have hfinE : ∑' n, ENNReal.ofReal (g n) ≤ ENNReal.ofReal B' := by
      rw [hgE]; exact hsum N hN
    have hgs : Summable g := by
      have hne : ∑' n, ENNReal.ofReal (g n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfinE
      have := ENNReal.summable_toReal hne
      refine this.congr (fun n => ?_)
      exact ENNReal.toReal_ofReal (hg0 n)
    have hgB : ∑' n, g n ≤ B' :=
      (ENNReal.ofReal_le_ofReal_iff hB'0).1
        (by rw [ENNReal.ofReal_tsum_of_nonneg hg0 hgs]; exact hfinE)
    have hc : 0 ≤ C / (1 + (N : ℝ)) ^ (k - 1) := by positivity
    refine G2043S.series_tail (J := fun n => higherAction k φ n) (g := g)
      (c := C / (1 + (N : ℝ)) ^ (k - 1)) (B := B') N hc hg0 hgs hgB (fun n hn' => ?_)
    -- pointwise: ‖J n‖ ≤ C/(1+N)^(k-1) * g n for |n| ≥ N
    have hgap : ‖gamma2 φ n‖ = ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 := by
      rw [gamma2_value38 φ hφgk n]
      unfold NlsGge.Atomic.KST059.actualGapSequence
      rw [norm_pow]
    have hgn : g n = G2043S.pw k (2 * n) ^ 2 * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 := by
      simp only [hg, hn', if_true]
    have hjp : 0 < (1 + (N : ℝ)) ^ (k - 1) := by positivity
    have hjb := G2043S.jb_pw_le k N n hn'
    calc ‖higherAction k φ n‖ ≤ C * japaneseBracket n ^ (k - 1) * ‖gamma2 φ n‖ := hJ n
      _ = C * (japaneseBracket n ^ (k - 1)) * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 := by
          rw [hgap]
      _ ≤ C / (1 + (N : ℝ)) ^ (k - 1) * g n := by
          rw [hgn, div_mul_eq_mul_div, le_div_iff₀ hjp]
          have hsq0 : 0 ≤ ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 := sq_nonneg _
          calc C * japaneseBracket n ^ (k - 1) * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 *
                (1 + (N : ℝ)) ^ (k - 1)
              = C * (japaneseBracket n ^ (k - 1) * (1 + (N : ℝ)) ^ (k - 1)) *
                  ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 := by ring
            _ ≤ C * (G2043S.pw k (2 * n) ^ 2) * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2 := by
                gcongr
            _ = C * (G2043S.pw k (2 * n) ^ 2 * ‖NlsGge.Atomic.KST059.actualGapSequence φ n‖ ^ 2) := by
                ring
  -- zero distance for φ₀ itself
  have hzero : pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ₀ - φ₀) < δ₀ := by
    have : pairSobolevNorm ((k-1 : ℕ) : ℝ) (φ₀ - φ₀) = 0 := by
      rw [sub_self]
      unfold pairSobolevNorm
      have h0' : physicalSobolevNorm ((k-1 : ℕ) : ℝ) (0 : PhysicalL2) = 0 := NlsGge.ThirdConsultation.KSPSSupport.h161_psn_zero (k - 1)
      simp [h0']
    rw [this]; exact hδ₀pos
  refine ⟨(series φ₀ hreg hzero N₁ le_rfl).1, fun ε hε => ?_⟩
  -- choose N large
  obtain ⟨N, hN⟩ := exists_nat_gt (max (C * B' / ε) 0)
  set N' : ℕ := max N N₁ with hN'
  have hN'₁ : N₁ ≤ N' := le_max_right _ _
  have hNε : C * B' / ε < (N' : ℝ) := by
    have : (N : ℝ) ≤ N' := by exact_mod_cast le_max_left N N₁
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) this
  have hsmall : C / (1 + (N' : ℝ)) ^ (k - 1) * B' < ε := by
    have h1 : (1 + (N' : ℝ)) ≤ (1 + (N' : ℝ)) ^ (k - 1) := by
      calc (1 + (N' : ℝ)) = (1 + (N' : ℝ)) ^ 1 := (pow_one _).symm
        _ ≤ (1 + (N' : ℝ)) ^ (k - 1) := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg N' : (0:ℝ) ≤ N')]) hk1
    have hpos : 0 < (1 + (N' : ℝ)) := by positivity
    have h2 : C / (1 + (N' : ℝ)) ^ (k - 1) * B' ≤ C * B' / (1 + (N' : ℝ)) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hpos h1
    have h3 : C * B' / (1 + (N' : ℝ)) < ε := by
      rw [div_lt_iff₀ hpos]
      have := (div_lt_iff₀ hε).1 hNε
      nlinarith
    exact lt_of_le_of_lt h2 h3
  refine ⟨δ₀, hδ₀pos, Finset.Ioo (-(N' : ℤ)) N', fun φ hφ hn => ?_⟩
  obtain ⟨hφW, -, -⟩ := key φ hφ hn
  obtain ⟨hs, hS⟩ := series φ hφ hn N' hN'₁
  refine ⟨hφW, hs, fun S hS₀ => ?_⟩
  have hcompl : ∀ n, n ∉ S → N' ≤ n.natAbs := by
    intro n hnS
    have : n ∉ Finset.Ioo (-(N' : ℤ)) N' := fun h => hnS (hS₀ h)
    simp only [Finset.mem_Ioo, not_and_or, not_lt] at this
    omega
  obtain ⟨h1, h2⟩ := hS S hcompl
  exact ⟨lt_of_le_of_lt h1 hsmall, lt_of_le_of_lt h2 hsmall⟩

end
end NlsGge.GKDefinitionDesign
