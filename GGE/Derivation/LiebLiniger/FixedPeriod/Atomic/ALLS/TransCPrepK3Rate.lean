import Mathlib
import NlsGge.ThirdConsultation.PDE.PDE061Core
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.Atomic.G6.G6034

/-! # Trunk C PREPARATORY (K3): the rate candidate `Ω_n(I) = rate_n(√I)`, its `ℓ¹₊`-continuity,
and identification with `actualOmega n` on `positiveActionCone` by density

Author: Claude Opus 5.5 (preparatory author P3).  NOT self-reviewed, NOT accepted, NOT approved,
NOT rooted.  Namespace `NlsGge.ALLS.TransCPrep`; every name carries the non-approved prefix
`prep_`.  None of the four pending trunk C commands is stated or proved here.

Binders / conclusions (one line each):
* `prep_l1Cone` : the set `ℓ¹₊ = {I : ℤ → ℝ | (∀ k, 0 ≤ I k) ∧ Summable I}` (raw, unweighted).
* `prep_sqrtSection I` : the coordinatewise real square root `k ↦ √(I k)`.
* `prep_omegaOfRate rate n I` : for an arbitrary family `rate : ℤ → (ℤ → ℝ) → ℝ` (rate of mode `n`
  as a function of the nonnegative amplitude sequence), equals `rate n (√I)` if `I ∈ ℓ¹₊` and `0`
  otherwise (declared junk value).
* `prep_sq_sqrt_sub_sqrt_le a b` : for `a, b ≥ 0`, `(√a − √b)² ≤ |a − b|`.
* `prep_sqrt_section_le I J` : for `I, J ≥ 0` with `Σ|I − J|` summable, `Σ (√I − √J)²` is summable and
  `≤ Σ |I − J|` (local copy of TransCSqrt.sqrt_section_le, which is not on this branch's base).
* `prep_sqrtSection_mem I hI` : `I ∈ ℓ¹₊` gives `√I ≥ 0` with `Σ (√I)²` summable (the `ℓ²₊` cone).
* `prep_omegaOfRate_of_not_mem` : `prep_omegaOfRate rate n I = 0` whenever `I ∉ ℓ¹₊`.
* `prep_omegaOfRate_of_mem` : `prep_omegaOfRate rate n I = rate n (√I)` whenever `I ∈ ℓ¹₊`.
* `prep_omegaOfRate_continuous rate n hrate` : if `rate n` is ε–δ continuous at every point of the
  `ℓ²₊` cone for the squared `ℓ²` distance `Σ (p − q)²` (hypothesis `hrate`, quantified over points
  of the cone only), then `prep_omegaOfRate rate n` is ε–δ continuous at every point of `ℓ¹₊` for
  the `ℓ¹` distance `Σ |J − I|` (the exact shape of C-MAIN item 3).
* `prep_one_le_actionWeight k` : `1 ≤ actionWeight k` (`= 1 + k²`).
* `prep_l1Cone_of_positiveActionCone I hI` : the energy cone `positiveActionCone` lies in `ℓ¹₊`.
* `prep_actualOmega_of_mem n I hI` : on `positiveActionCone`, `actualOmega n I` is
  `actionFrequency n (rawActionToPositive I hI)` (unfolding of the existing definition).
* `prep_actionFrequency_continuous n` : `actionFrequency n` is continuous on the weighted-`ℓ¹` cone
  `PositiveActionSpace` (the existing `freq_continuous` at `chosenActionExtension`).
* `prep_dist_rawActionToPositive` : the weighted-`ℓ¹` distance of two raw cone points is
  `Σ |w_k J_k − w_k I_k|`, `w_k = actionWeight k`.
* `prep_finiteSupport_approx n I hI η hη` : every `I ∈ positiveActionCone` is approximated, to within
  `η > 0` SIMULTANEOUSLY in the weighted-`ℓ¹` distance and the `ℓ¹` distance, by a finitely supported
  nonnegative `J` with `0 < J n` (truncation plus a small bump at `n`).
* `prep_eq_actualOmega_of_dense n f hf hD` : if `f : (ℤ → ℝ) → ℝ` is ε–δ `ℓ¹`-continuous at every
  point of `ℓ¹₊` (hypothesis `hf`, C-MAIN item 3 shape) and `f J = actualOmega n J` for every finitely
  supported nonnegative `J` with `0 < J n` (hypothesis `hD`), then `f I = actualOmega n I` for every
  `I ∈ positiveActionCone` (zero coordinates and infinite support included).
* `prep_omegaOfRate_eq_actualOmega` : the composition: under `hrate` and
  `rate n (√J) = actualOmega n J` on the same dense set, `prep_omegaOfRate rate n = actualOmega n` on
  `positiveActionCone`. -/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.PDE

namespace NlsGge.ALLS.TransCPrep

/-- The nonnegative `ℓ¹` cone of raw actions. -/
def prep_l1Cone : Set (ℤ → ℝ) := {I | (∀ k, 0 ≤ I k) ∧ Summable I}

/-- The real nonnegative square-root section. -/
def prep_sqrtSection (I : ℤ → ℝ) : ℤ → ℝ := fun k => Real.sqrt (I k)

open scoped Classical in
/-- Candidate frequency from a rate-of-amplitudes family; zero off `ℓ¹₊`. -/
def prep_omegaOfRate (rate : ℤ → (ℤ → ℝ) → ℝ) (n : ℤ) (I : ℤ → ℝ) : ℝ :=
  if I ∈ prep_l1Cone then rate n (prep_sqrtSection I) else 0

theorem prep_sq_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  set x := Real.sqrt a with hx
  set y := Real.sqrt b with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg a
  have hy0 : 0 ≤ y := Real.sqrt_nonneg b
  have hax : a = x ^ 2 := (Real.sq_sqrt ha).symm
  have hby : b = y ^ 2 := (Real.sq_sqrt hb).symm
  rw [hax, hby, show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul,
    abs_of_nonneg (add_nonneg hx0 hy0)]
  have h1 : |x - y| ≤ x + y := by
    rw [abs_le]; constructor <;> linarith
  have h2 : (x - y) ^ 2 = |x - y| * |x - y| := by rw [← sq, sq_abs]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem prep_sqrt_section_le (I J : ℤ → ℝ) (hI : ∀ n, 0 ≤ I n) (hJ : ∀ n, 0 ≤ J n)
    (hs : Summable fun n => |I n - J n|) :
    Summable (fun n => (Real.sqrt (I n) - Real.sqrt (J n)) ^ 2) ∧
      ∑' n, (Real.sqrt (I n) - Real.sqrt (J n)) ^ 2 ≤ ∑' n, |I n - J n| := by
  have hle : ∀ n, (Real.sqrt (I n) - Real.sqrt (J n)) ^ 2 ≤ |I n - J n| :=
    fun n => prep_sq_sqrt_sub_sqrt_le (hI n) (hJ n)
  have hsum : Summable (fun n => (Real.sqrt (I n) - Real.sqrt (J n)) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hle hs
  exact ⟨hsum, hsum.tsum_le_tsum hle hs⟩

theorem prep_sqrtSection_mem (I : ℤ → ℝ) (hI : (∀ k, 0 ≤ I k) ∧ Summable I) :
    (∀ k, 0 ≤ prep_sqrtSection I k) ∧ Summable (fun k => prep_sqrtSection I k ^ 2) :=
  ⟨fun _k => Real.sqrt_nonneg _, hI.2.congr (fun k => (Real.sq_sqrt (hI.1 k)).symm)⟩

theorem prep_omegaOfRate_of_not_mem (rate : ℤ → (ℤ → ℝ) → ℝ) (n : ℤ) (I : ℤ → ℝ)
    (hI : ¬ ((∀ k, 0 ≤ I k) ∧ Summable I)) : prep_omegaOfRate rate n I = 0 := by
  unfold prep_omegaOfRate
  rw [if_neg (show I ∉ prep_l1Cone from hI)]

theorem prep_omegaOfRate_of_mem (rate : ℤ → (ℤ → ℝ) → ℝ) (n : ℤ) (I : ℤ → ℝ)
    (hI : (∀ k, 0 ≤ I k) ∧ Summable I) :
    prep_omegaOfRate rate n I = rate n (prep_sqrtSection I) := by
  unfold prep_omegaOfRate
  rw [if_pos (show I ∈ prep_l1Cone from hI)]

/-- `ℓ²₊`-continuity of the rate gives `ℓ¹₊`-continuity of `Ω_n = rate_n ∘ √`. -/
theorem prep_omegaOfRate_continuous (rate : ℤ → (ℤ → ℝ) → ℝ) (n : ℤ)
    (hrate : ∀ q : ℤ → ℝ, ((∀ k, 0 ≤ q k) ∧ Summable (fun k => q k ^ 2)) →
      ∀ ε > 0, ∃ δ > 0, ∀ p : ℤ → ℝ, ((∀ k, 0 ≤ p k) ∧ Summable (fun k => p k ^ 2)) →
        ∑' k, (p k - q k) ^ 2 < δ → |rate n p - rate n q| < ε) :
    ∀ I : ℤ → ℝ, ((∀ k, 0 ≤ I k) ∧ Summable I) →
      ∀ ε > 0, ∃ δ > 0, ∀ J : ℤ → ℝ, ((∀ k, 0 ≤ J k) ∧ Summable J) →
        ∑' k, |J k - I k| < δ → |prep_omegaOfRate rate n J - prep_omegaOfRate rate n I| < ε := by
  intro I hI ε hε
  obtain ⟨δ, hδ, h⟩ := hrate _ (prep_sqrtSection_mem I hI) ε hε
  refine ⟨δ, hδ, fun J hJ hd => ?_⟩
  rw [prep_omegaOfRate_of_mem rate n J hJ, prep_omegaOfRate_of_mem rate n I hI]
  refine h _ (prep_sqrtSection_mem J hJ) ?_
  have hb := (prep_sqrt_section_le J I hJ.1 hI.1 (hJ.2.sub hI.2).abs).2
  exact lt_of_le_of_lt hb hd

theorem prep_one_le_actionWeight (k : ℤ) : 1 ≤ actionWeight k := by
  rw [G6034Aux.actionWeight_eq]
  nlinarith [sq_nonneg (k : ℝ)]

theorem prep_l1Cone_of_positiveActionCone (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) :
    (∀ k, 0 ≤ I k) ∧ Summable I := by
  refine ⟨hI.1, Summable.of_nonneg_of_le hI.1 (fun k => ?_) hI.2⟩
  have h1 := prep_one_le_actionWeight k
  nlinarith [hI.1 k]

theorem prep_actualOmega_of_mem (n : ℤ) (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) :
    actualOmega n I = actionFrequency n (rawActionToPositive I hI) := by
  unfold actualOmega
  rw [dif_pos hI]

theorem prep_actionFrequency_continuous (n : ℤ) : Continuous (actionFrequency n) :=
  freq_continuous chosenActionExtension chosenActionExtension_spec n

theorem prep_dist_rawActionToPositive (I J : ℤ → ℝ) (hI : I ∈ positiveActionCone)
    (hJ : J ∈ positiveActionCone) :
    dist (rawActionToPositive J hJ) (rawActionToPositive I hI) =
      ∑' k, |actionWeight k * J k - actionWeight k * I k| := by
  rw [Subtype.dist_eq, dist_eq_norm,
    ← (G6034Aux.hasSum_norm_one ((rawActionToPositive J hJ).val -
      (rawActionToPositive I hI).val)).tsum_eq]
  refine tsum_congr (fun k => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  rfl

/-- Tail of a summable family outside a finite set, as an ordinary `tsum`. -/
theorem prep_tsum_tail (g : ℤ → ℝ) (hg : Summable g) (s : Finset ℤ) :
    Summable (fun k => if k ∈ s then 0 else g k) ∧
      ∑' k, (if k ∈ s then 0 else g k) = ∑' k, g k - ∑ k ∈ s, g k := by
  have hin : Summable (fun k => if k ∈ s then g k else 0) :=
    summable_of_ne_finset_zero (s := s) (fun b hb => if_neg hb)
  have hout : Summable (fun k => if k ∈ s then 0 else g k) := by
    refine (hg.sub hin).congr (fun k => ?_)
    split_ifs <;> simp
  refine ⟨hout, ?_⟩
  have h1 : ∑' k, (if k ∈ s then g k else 0) = ∑ k ∈ s, g k := by
    rw [tsum_eq_sum (s := s) (fun b hb => if_neg hb)]
    exact Finset.sum_congr rfl (fun k hk => if_pos hk)
  have h2 : ∑' k, g k = ∑' k, ((if k ∈ s then g k else 0) + (if k ∈ s then 0 else g k)) := by
    refine tsum_congr (fun k => ?_)
    split_ifs <;> simp
  rw [h2, Summable.tsum_add hin hout, h1]
  ring

/-- Simultaneous weighted-`ℓ¹` and `ℓ¹` density of finitely supported nonnegative data with
positive `n`-th coordinate in the energy cone. -/
theorem prep_finiteSupport_approx (n : ℤ) (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) (η : ℝ)
    (hη : 0 < η) :
    ∃ J : ℤ → ℝ, (∀ k, 0 ≤ J k) ∧ (∃ s : Finset ℤ, ∀ k ∉ s, J k = 0) ∧ 0 < J n ∧
      ∑' k, |actionWeight k * J k - actionWeight k * I k| < η ∧ ∑' k, |J k - I k| < η := by
  set g : ℤ → ℝ := fun k => actionWeight k * I k with hgdef
  have hg : Summable g := hI.2
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg (sobolevModeWeight_pos 1 k).le (hI.1 k)
  have hIg : ∀ k, I k ≤ g k := fun k => by
    have h1 := prep_one_le_actionWeight k
    simp only [hgdef]; nlinarith [hI.1 k]
  -- a finite set carrying all but `η/2` of the weighted mass
  obtain ⟨s, hs⟩ : ∃ s : Finset ℤ, |∑ k ∈ s, g k - ∑' k, g k| < η / 2 := by
    have hev := hg.hasSum.eventually (Metric.ball_mem_nhds (∑' k, g k) (by positivity : 0 < η / 2))
    obtain ⟨s, hs⟩ := hev.exists
    exact ⟨s, by simpa [Metric.mem_ball, Real.dist_eq] using hs⟩
  obtain ⟨htailS, htail⟩ := prep_tsum_tail g hg s
  have htail_lt : ∑' k, (if k ∈ s then 0 else g k) < η / 2 := by
    rw [htail]; have := (abs_lt.1 hs).1; linarith
  have hw1 := prep_one_le_actionWeight n
  have hw0 : 0 < actionWeight n := by linarith
  set c : ℝ := η / (4 * actionWeight n) with hc
  have hc0 : 0 < c := by positivity
  have hwc : actionWeight n * c = η / 4 := by rw [hc]; field_simp
  have hcle : c ≤ η / 4 := by
    rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set J : ℤ → ℝ := fun k => (if k ∈ insert n s then I k else 0) + (if k = n then c else 0)
    with hJdef
  have hJ0 : ∀ k, 0 ≤ J k := fun k => by
    simp only [hJdef]; split_ifs <;> linarith [hI.1 k]
  have hJsupp : ∀ k ∉ insert n s, J k = 0 := fun k hk => by
    have hkn : k ≠ n := fun h => hk (h ▸ Finset.mem_insert_self n s)
    simp only [hJdef, if_neg hk, if_neg hkn, add_zero]
  have hJn : J n = I n + c := by
    show (if n ∈ insert n s then I n else 0) + (if n = n then c else 0) = I n + c
    rw [if_pos (Finset.mem_insert_self n s), if_pos rfl]
  -- pointwise bounds
  have hpt : ∀ k, |J k - I k| = (if k = n then c else 0) +
      (if k ∈ insert n s then 0 else I k) := fun k => by
    by_cases hkn : k = n
    · subst hkn
      rw [hJn, if_pos rfl, if_pos (Finset.mem_insert_self k s)]
      rw [show I k + c - I k = c by ring, abs_of_pos hc0, add_zero]
    · by_cases hks : k ∈ insert n s
      · simp only [hJdef, if_pos hks, if_neg hkn, add_zero, sub_self, abs_zero]
      · simp only [hJdef, if_neg hks, if_neg hkn, add_zero, zero_add, zero_sub, abs_neg,
          abs_of_nonneg (hI.1 k)]
  have hbd1 : ∀ k, |J k - I k| ≤ (if k = n then c else 0) + (if k ∈ s then 0 else g k) :=
    fun k => by
      rw [hpt k]
      refine add_le_add le_rfl ?_
      by_cases hks : k ∈ insert n s
      · rw [if_pos hks]; split_ifs <;> simp [hg0 k]
      · have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
        rw [if_neg hks, if_neg hks']; exact hIg k
  have hbdw : ∀ k, |actionWeight k * J k - actionWeight k * I k| ≤
      (if k = n then actionWeight n * c else 0) + (if k ∈ s then 0 else g k) := fun k => by
    have hwk : 0 < actionWeight k := sobolevModeWeight_pos 1 k
    rw [← mul_sub, abs_mul, abs_of_pos hwk, hpt k, mul_add]
    refine add_le_add ?_ ?_
    · by_cases hkn : k = n
      · subst hkn; simp
      · simp [hkn]
    · by_cases hks : k ∈ insert n s
      · rw [if_pos hks, mul_zero]; split_ifs <;> simp [hg0 k]
      · have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
        rw [if_neg hks, if_neg hks']
  have hsing : ∀ a : ℝ, Summable (fun k : ℤ => if k = n then a else 0) := fun a =>
    summable_of_ne_finset_zero (s := {n}) (fun b hb => if_neg (by simpa using hb))
  have hR1 := (hsing c).add htailS
  have hRw := (hsing (actionWeight n * c)).add htailS
  have hsum1 : Summable (fun k => |J k - I k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbd1 hR1
  have hsumw : Summable (fun k => |actionWeight k * J k - actionWeight k * I k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbdw hRw
  have hT1 : ∑' k, ((if k = n then c else 0) + (if k ∈ s then 0 else g k)) =
      c + ∑' k, (if k ∈ s then 0 else g k) := by
    rw [Summable.tsum_add (hsing c) htailS, tsum_ite_eq n (fun _ => c)]
  have hTw : ∑' k, ((if k = n then actionWeight n * c else 0) + (if k ∈ s then 0 else g k)) =
      actionWeight n * c + ∑' k, (if k ∈ s then 0 else g k) := by
    rw [Summable.tsum_add (hsing _) htailS, tsum_ite_eq n (fun _ => actionWeight n * c)]
  refine ⟨J, hJ0, ⟨insert n s, hJsupp⟩, by rw [hJn]; linarith [hI.1 n], ?_, ?_⟩
  · calc ∑' k, |actionWeight k * J k - actionWeight k * I k|
        ≤ ∑' k, ((if k = n then actionWeight n * c else 0) + (if k ∈ s then 0 else g k)) :=
          hsumw.tsum_le_tsum hbdw hRw
      _ < η := by rw [hTw, hwc]; linarith
  · calc ∑' k, |J k - I k|
        ≤ ∑' k, ((if k = n then c else 0) + (if k ∈ s then 0 else g k)) :=
          hsum1.tsum_le_tsum hbd1 hR1
      _ < η := by rw [hT1]; linarith

theorem prep_positiveActionCone_of_finiteSupport (J : ℤ → ℝ) (hJ0 : ∀ k, 0 ≤ J k)
    (hJs : ∃ s : Finset ℤ, ∀ k ∉ s, J k = 0) : J ∈ positiveActionCone := by
  obtain ⟨s, hs⟩ := hJs
  exact ⟨hJ0, summable_of_ne_finset_zero (s := s) (fun k hk => by rw [hs k hk, mul_zero])⟩

/-- **Density extension.**  An `ℓ¹₊`-continuous function agreeing with `actualOmega n` on finitely
supported nonnegative data with positive `n`-th coordinate agrees with it on all of
`positiveActionCone`. -/
theorem prep_eq_actualOmega_of_dense (n : ℤ) (f : (ℤ → ℝ) → ℝ)
    (hf : ∀ I : ℤ → ℝ, ((∀ k, 0 ≤ I k) ∧ Summable I) →
      ∀ ε > 0, ∃ δ > 0, ∀ J : ℤ → ℝ, ((∀ k, 0 ≤ J k) ∧ Summable J) →
        ∑' k, |J k - I k| < δ → |f J - f I| < ε)
    (hD : ∀ J : ℤ → ℝ, (∀ k, 0 ≤ J k) → (∃ s : Finset ℤ, ∀ k ∉ s, J k = 0) → 0 < J n →
      f J = actualOmega n J) :
    ∀ I : ℤ → ℝ, I ∈ positiveActionCone → f I = actualOmega n I := by
  intro I hI
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  have hcont := (prep_actionFrequency_continuous n).continuousAt (x := rawActionToPositive I hI)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hf I (prep_l1Cone_of_positiveActionCone I hI) (ε / 2) (by positivity)
  obtain ⟨J, hJ0, hJs, hJn, hJw, hJ1⟩ :=
    prep_finiteSupport_approx n I hI (min δ1 δ2) (lt_min hδ1 hδ2)
  have hJc : J ∈ positiveActionCone := prep_positiveActionCone_of_finiteSupport J hJ0 hJs
  have hfJ := h2 J (prep_l1Cone_of_positiveActionCone J hJc)
    (lt_of_lt_of_le hJ1 (min_le_right _ _))
  have hd : dist (rawActionToPositive J hJc) (rawActionToPositive I hI) < δ1 := by
    rw [prep_dist_rawActionToPositive I J hI hJc]
    exact lt_of_lt_of_le hJw (min_le_left _ _)
  have hoJ := h1 hd
  rw [Real.dist_eq, ← prep_actualOmega_of_mem n J hJc, ← prep_actualOmega_of_mem n I hI,
    ← hD J hJ0 hJs hJn] at hoJ
  rw [Real.dist_eq]
  have htri := abs_sub_le (f I) (f J) (actualOmega n I)
  rw [abs_sub_comm (f I) (f J)] at htri
  linarith

/-- Composition: the rate candidate equals `actualOmega n` on the energy cone. -/
theorem prep_omegaOfRate_eq_actualOmega (rate : ℤ → (ℤ → ℝ) → ℝ) (n : ℤ)
    (hrate : ∀ q : ℤ → ℝ, ((∀ k, 0 ≤ q k) ∧ Summable (fun k => q k ^ 2)) →
      ∀ ε > 0, ∃ δ > 0, ∀ p : ℤ → ℝ, ((∀ k, 0 ≤ p k) ∧ Summable (fun k => p k ^ 2)) →
        ∑' k, (p k - q k) ^ 2 < δ → |rate n p - rate n q| < ε)
    (hD : ∀ J : ℤ → ℝ, (∀ k, 0 ≤ J k) → (∃ s : Finset ℤ, ∀ k ∉ s, J k = 0) → 0 < J n →
      rate n (prep_sqrtSection J) = actualOmega n J) :
    ∀ I : ℤ → ℝ, I ∈ positiveActionCone → prep_omegaOfRate rate n I = actualOmega n I := by
  refine prep_eq_actualOmega_of_dense n (prep_omegaOfRate rate n)
    (prep_omegaOfRate_continuous rate n hrate) (fun J hJ0 hJs hJn => ?_)
  have hJc := prep_l1Cone_of_positiveActionCone J (prep_positiveActionCone_of_finiteSupport J hJ0 hJs)
  rw [prep_omegaOfRate_of_mem rate n J hJc]
  exact hD J hJ0 hJs hJn

end NlsGge.ALLS.TransCPrep
