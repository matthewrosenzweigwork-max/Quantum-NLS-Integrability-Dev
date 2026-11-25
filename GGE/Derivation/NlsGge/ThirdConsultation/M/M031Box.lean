import Mathlib
import NlsGge.ThirdConsultation.M.M031Host
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.IsolatingDefs
import NlsGge.Atomic.M.M054

/-!
# M-031 support: assembling both printed heads from the three support facts (proof development, AUTHOR; not self-reviewed)

Pure bookkeeping, no spectral input: the three hypotheses are exactly the (zeta-reduced) statements of the supports
`periodic_spectral_localization_high` (M031High), `low_label_re_bound` (M031LowCore + landed bridge) and
`lamSeq_abs_im_le` (M031Im); M031 instantiates them.  Uniform constants (Pro: "Choose N by 8B² ≤ 1+N and enlarge the
low real bound by Nπ plus the radius bound"): `N = ⌈8B²⌉₊`, `C = B² + √2 B`, `R = Nπ + C + 8B²π`; a label with
`|n| < N` is either thresholded for its actual Q (radius bound) or low (actual central box), and `|Im| ≤ Q ≤ B`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem m031_indexWeight_le_two (n : ℤ) :
    NlsGge.Atomic.M.M054.indexWeight n ≤ NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
  unfold NlsGge.Atomic.M.M054.indexWeight
  push_cast
  rw [abs_mul]
  have := abs_nonneg (n : ℝ)
  norm_num
  linarith

theorem m031_one_le_indexWeight (n : ℤ) : 1 ≤ NlsGge.Atomic.M.M054.indexWeight n := by
  unfold NlsGge.Atomic.M.M054.indexWeight
  linarith [abs_nonneg (n : ℝ)]

/-- Head 1 from the supports. -/
theorem m031_box_of_supports (φ : KSPS.SobolevC 1) (hW : KSPS.toPotPair φ ∈ gkW)
    (hhigh : ∀ n : ℤ,
      8 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n → ∀ plus : Bool,
        ‖(if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n) -
          (n : ℂ) * (Real.pi : ℂ)‖ ≤
          MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 /
              NlsGge.Atomic.M.M054.indexWeight n +
            Real.sqrt 2 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) /
              NlsGge.Atomic.M.M054.indexWeight (2 * n))
    (hlow : ∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n <
        8 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 → ∀ plus : Bool,
      |(if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n).re| ≤
        (8 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 - 1 / 2) * Real.pi)
    (him : ∀ k : ℤ, |(lamSeq (KSPS.toPotPair φ) k).im| ≤
      MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)
    (∀ n : ℤ, 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n →
      ∀ plus : Bool,
        ‖(if plus then lamPlus (KSPS.toPotPair φ) n
          else lamMinus (KSPS.toPotPair φ) n) -
          (n : ℂ) * (Real.pi : ℂ)‖ ≤
          Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
            Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n)) ∧
    (∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2 →
      ∀ plus : Bool,
        let z : ℂ := if plus then lamPlus (KSPS.toPotPair φ) n
          else lamMinus (KSPS.toPotPair φ) n
        |z.re| ≤ (8 * Q ^ 2 - 1 / 2) * Real.pi ∧ |z.im| ≤ Q) := by
  intro Q
  refine ⟨hhigh, ?_⟩
  intro n hn plus
  refine ⟨hlow n hn plus, ?_⟩
  cases plus
  · exact him (2 * n)
  · exact him (2 * n + 1)

/-- Head 2 from the supports (quantifier order `∀ B, ∃ N C R, ∀ φ`). -/
theorem m031_uniform_of_supports
    (hhigh : ∀ φ : KSPS.SobolevC 1, KSPS.toPotPair φ ∈ gkW → ∀ n : ℤ,
      8 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n → ∀ plus : Bool,
        ‖(if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n) -
          (n : ℂ) * (Real.pi : ℂ)‖ ≤
          MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 /
              NlsGge.Atomic.M.M054.indexWeight n +
            Real.sqrt 2 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) /
              NlsGge.Atomic.M.M054.indexWeight (2 * n))
    (hlow : ∀ φ : KSPS.SobolevC 1, ∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n <
        8 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 → ∀ plus : Bool,
      |(if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n).re| ≤
        (8 * MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ^ 2 - 1 / 2) * Real.pi)
    (him : ∀ φ : KSPS.SobolevC 1, ∀ k : ℤ, |(lamSeq (KSPS.toPotPair φ) k).im| ≤
      MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)) :
    ∀ B : ℝ, 0 < B →
      ∃ N : ℕ, ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      ∀ φ : KSPS.SobolevC 1,
        MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ≤ B →
        KSPS.toPotPair φ ∈ gkW →
        (∀ n : ℤ, N ≤ n.natAbs → ∀ plus : Bool,
          ‖(if plus then lamPlus (KSPS.toPotPair φ) n
            else lamMinus (KSPS.toPotPair φ) n) -
            (n : ℂ) * (Real.pi : ℂ)‖ ≤
              C / NlsGge.Atomic.M.M054.indexWeight n) ∧
        (∀ n : ℤ, n.natAbs < N → ∀ plus : Bool,
          let z : ℂ := if plus then lamPlus (KSPS.toPotPair φ) n
            else lamMinus (KSPS.toPotPair φ) n
          |z.re| ≤ R ∧ |z.im| ≤ B) := by
  intro B hB
  have hpi := Real.pi_pos
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hC0 : 0 ≤ B ^ 2 + Real.sqrt 2 * B := by positivity
  have hN0 : (0 : ℝ) ≤ (⌈8 * B ^ 2⌉₊ : ℝ) := Nat.cast_nonneg _
  refine ⟨⌈8 * B ^ 2⌉₊, B ^ 2 + Real.sqrt 2 * B,
    (⌈8 * B ^ 2⌉₊ : ℝ) * Real.pi + (B ^ 2 + Real.sqrt 2 * B) + 8 * B ^ 2 * Real.pi,
    hC0, by positivity, ?_⟩
  intro φ hQB hW
  have h1 := hhigh φ hW
  have h2 := hlow φ
  have h3 := him φ
  have hQ0 : 0 ≤ MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) := Real.sqrt_nonneg _
  generalize MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) = Q at h1 h2 h3 hQB hQ0
  have hQ2 : Q ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hQ0 hQB 2
  have hNle : 8 * B ^ 2 ≤ (⌈8 * B ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hrad : ∀ n : ℤ, Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
      Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) ≤
        (B ^ 2 + Real.sqrt 2 * B) / NlsGge.Atomic.M.M054.indexWeight n := by
    intro n
    have ha := m031_one_le_indexWeight n
    have hb := m031_indexWeight_le_two n
    have ha0 : 0 < NlsGge.Atomic.M.M054.indexWeight n := by linarith
    have e1 : Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n ≤ B ^ 2 / NlsGge.Atomic.M.M054.indexWeight n :=
      div_le_div_of_nonneg_right hQ2 ha0.le
    have e2 : Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) ≤
        Real.sqrt 2 * B / NlsGge.Atomic.M.M054.indexWeight n :=
      calc Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n)
          ≤ Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight n :=
            div_le_div_of_nonneg_left (by positivity) ha0 hb
        _ ≤ Real.sqrt 2 * B / NlsGge.Atomic.M.M054.indexWeight n :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQB hs2) ha0.le
    rw [add_div]
    linarith
  have hCle : ∀ n : ℤ, (B ^ 2 + Real.sqrt 2 * B) / NlsGge.Atomic.M.M054.indexWeight n ≤
      B ^ 2 + Real.sqrt 2 * B := fun n => div_le_self hC0 (m031_one_le_indexWeight n)
  have hnat : ∀ n : ℤ, ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
    intro n
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hthrN : ∀ n : ℤ, ⌈8 * B ^ 2⌉₊ ≤ n.natAbs → 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n := by
    intro n hn
    have e : ((⌈8 * B ^ 2⌉₊ : ℕ) : ℝ) ≤ ((n.natAbs : ℕ) : ℝ) := by exact_mod_cast hn
    rw [hnat] at e
    unfold NlsGge.Atomic.M.M054.indexWeight
    linarith
  refine ⟨fun n hn plus => (h1 n (hthrN n hn) plus).trans (hrad n), ?_⟩
  intro n hn plus
  dsimp only
  refine ⟨?_, ?_⟩
  · rcases le_or_gt (8 * Q ^ 2) (NlsGge.Atomic.M.M054.indexWeight n) with hth | hth
    · have h := (h1 n hth plus).trans ((hrad n).trans (hCle n))
      set z := (if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n)
      have hre := Complex.abs_re_le_norm (z - (n : ℂ) * (Real.pi : ℂ))
      have hre' : (z - (n : ℂ) * (Real.pi : ℂ)).re = z.re - (n : ℝ) * Real.pi := by simp
      rw [hre'] at hre
      have hnN : |(n : ℝ)| ≤ (⌈8 * B ^ 2⌉₊ : ℝ) := by
        rw [← hnat]
        exact_mod_cast hn.le
      have hab : |z.re| ≤ |z.re - (n : ℝ) * Real.pi| + |(n : ℝ)| * Real.pi := by
        have := abs_sub_abs_le_abs_sub z.re ((n : ℝ) * Real.pi)
        rw [abs_mul, abs_of_pos hpi] at this
        linarith
      have hnpi : |(n : ℝ)| * Real.pi ≤ (⌈8 * B ^ 2⌉₊ : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hnN hpi.le
      have hB8 : 0 ≤ 8 * B ^ 2 * Real.pi := by positivity
      linarith
    · have h := h2 n hth plus
      have hB8 : (8 * Q ^ 2 - 1 / 2) * Real.pi ≤ 8 * B ^ 2 * Real.pi := by nlinarith
      have hNpi : 0 ≤ (⌈8 * B ^ 2⌉₊ : ℝ) * Real.pi := by positivity
      linarith
  · cases plus
    · exact (h3 (2 * n)).trans hQB
    · exact (h3 (2 * n + 1)).trans hQB

end NlsGge.ThirdConsultation.M

end
