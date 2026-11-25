/- KST-023 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/KST023_FULL_01.lean (author proof development; independent review proof development/KST-023_PROOF_REVIEW01.md), byte-identical except this header and the removed `#print axioms` line.
   Target NlsGge/Atomic/KST/KST023.lean, namespace NlsGge.ThirdConsultation.KST. -/
import Mathlib
import NlsGge.Atomic.KSTPath

set_option autoImplicit false
noncomputable section
open scoped ENNReal
open NlsGge.Atomic.KSTPath

namespace NlsGge.ThirdConsultation.KST

theorem tsum_pi_fin_prod : ∀ (m : ℕ) (g : Fin m → ℤ → ℝ≥0∞),
    ∑' ℓ : Fin m → ℤ, ∏ i, g i (ℓ i) = ∏ i, ∑' z, g i z := by
  intro m
  induction m with
  | zero =>
    intro g
    simp
  | succ m ih =>
    intro g
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).tsum_eq]
    have e : ∀ p : ℤ × (Fin m → ℤ),
        ∏ i : Fin (m + 1), g i (((Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)) p) i) =
          g 0 p.1 * ∏ i : Fin m, g i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.consEquiv]
    simp_rw [e]
    have h2 : ∑' p : ℤ × (Fin m → ℤ), g 0 p.1 * ∏ i : Fin m, g i.succ (p.2 i) =
        ∑' z : ℤ, ∑' ℓ' : Fin m → ℤ, g 0 z * ∏ i : Fin m, g i.succ (ℓ' i) :=
      ENNReal.tsum_prod (f := fun (z : ℤ) (ℓ' : Fin m → ℤ) => g 0 z * ∏ i : Fin m, g i.succ (ℓ' i))
    rw [h2, Fin.prod_univ_succ]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih (fun i => g i.succ)]

/-- Telescoping bound `Σ_{j=k}^{J-1} 1/j² ≤ 1/(k-1/2) - 1/(J-1/2)`. -/
theorem sum_Ico_inv_sq_le (k : ℕ) (hk : 1 ≤ k) (J : ℕ) (hJ : k ≤ J) :
    ∑ j ∈ Finset.Ico k J, 1 / ((j : ℝ) ^ 2) ≤ 1 / ((k : ℝ) - 1 / 2) - 1 / ((J : ℝ) - 1 / 2) := by
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top hJ]
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast le_trans hk hJ
    have h1 : 1 / ((J : ℝ) ^ 2) ≤ 1 / ((J : ℝ) - 1 / 2) - 1 / (((J + 1 : ℕ) : ℝ) - 1 / 2) := by
      push_cast
      have hp : (0 : ℝ) < J - 1 / 2 := by linarith
      have hq : (0 : ℝ) < J + 1 - 1 / 2 := by linarith
      rw [div_sub_div _ _ hp.ne' hq.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith


theorem tail_sum_le (k : ℕ) (hk : 1 ≤ k) :
    ∑' m : ℤ, (if k ≤ m.natAbs then ENNReal.ofReal (1 / ((m.natAbs : ℝ) ^ 2)) else 0) ≤
      ENNReal.ofReal (2 / ((k : ℝ) - 1 / 2)) := by
  set F : ℕ → ℝ≥0∞ := fun j => if k ≤ j then ENNReal.ofReal (1 / ((j : ℝ) ^ 2)) else 0 with hFdef
  have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hF : ∀ n : ℕ, ∑ i ∈ Finset.range n, F i ≤ ENNReal.ofReal (1 / ((k : ℝ) - 1 / 2)) := by
    intro n
    have e : ∀ i : ℕ, F i = ENNReal.ofReal (if k ≤ i then 1 / ((i : ℝ) ^ 2) else 0) := by
      intro i; simp only [hFdef]; split_ifs <;> simp
    simp_rw [e]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range n).filter (fun i => k ≤ i) = Finset.Ico k n := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfilt]
    by_cases hn : k ≤ n
    · have := sum_Ico_inv_sq_le k hk n hn
      have hnn : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1 / 2) := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hk hn
        have : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
        positivity
      linarith
    · rw [Finset.Ico_eq_empty (by omega)]
      simp only [Finset.sum_empty]
      positivity
  have h1 : ∑' j, F j ≤ ENNReal.ofReal (1 / ((k : ℝ) - 1 / 2)) :=
    ENNReal.tsum_le_of_sum_range_le hF
  have h2 : ∑' j, F (j + 1) ≤ ENNReal.ofReal (1 / ((k : ℝ) - 1 / 2)) := by
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    refine le_trans ?_ (hF (n + 1))
    rw [Finset.sum_range_succ']
    exact le_self_add
  have hz : ∀ m : ℤ, (if k ≤ m.natAbs then ENNReal.ofReal (1 / ((m.natAbs : ℝ) ^ 2)) else 0) =
      F m.natAbs := fun m => rfl
  simp_rw [hz]
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have e1 : ∀ n : ℕ, F (n : ℤ).natAbs = F n := fun n => by simp
  have e2 : ∀ n : ℕ, F (-((n : ℤ) + 1)).natAbs = F (n + 1) := fun n => by
    rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]
  simp_rw [e1, e2]
  calc ∑' n : ℕ, F n + ∑' n : ℕ, F (n + 1)
      ≤ ENNReal.ofReal (1 / ((k : ℝ) - 1 / 2)) + ENNReal.ofReal (1 / ((k : ℝ) - 1 / 2)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 / ((k : ℝ) - 1 / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring


open Classical in
def denominatorPattern {k : ℕ} (n : ℤ) (σ : Pattern k) : ℝ≥0∞ :=
  ∑' ell : Path k, if admissiblePath n ell ∧
    (∀ i, nearFarBit n (ell i) = σ i) then
    ENNReal.ofReal (∏ i : Fin (2*k),
      (1 / ((ell i - n).natAbs : ℝ)^2)) else 0

/-- one-vertex factor -/
def gFac {k : ℕ} (n : ℤ) (σ : Pattern k) (i : Fin (2 * k)) (z : ℤ) : ℝ≥0∞ :=
  if (z ≠ n ∧ nearFarBit n z = σ i) then ENNReal.ofReal (1 / ((z - n).natAbs : ℝ) ^ 2) else 0

theorem denominatorPattern_eq {k : ℕ} (n : ℤ) (σ : Pattern k) :
    denominatorPattern n σ = ∏ i : Fin (2 * k), ∑' z : ℤ, gFac n σ i z := by
  rw [← tsum_pi_fin_prod (2 * k) (fun i z => gFac n σ i z)]
  unfold denominatorPattern
  refine tsum_congr fun ell => ?_
  by_cases h : admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i)
  · rw [if_pos h, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [gFac]
    rw [if_pos ⟨h.1 i, h.2 i⟩]
  · rw [if_neg h]
    have : ∃ i, ¬ (ell i ≠ n ∧ nearFarBit n (ell i) = σ i) := by
      by_contra hc
      push_neg at hc
      exact h ⟨fun i => (hc i).1, fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [gFac]
    rw [if_neg hi]

theorem gFac_shift {k : ℕ} (n : ℤ) (σ : Pattern k) (i : Fin (2 * k)) (m : ℤ) :
    gFac n σ i (m + n) =
      if (m ≠ 0 ∧ nearFarBit n (m + n) = σ i) then ENNReal.ofReal (1 / (m.natAbs : ℝ) ^ 2) else 0 := by
  have h : (m + n ≠ n) ↔ (m ≠ 0) := by
    constructor <;> intro h h' <;> apply h <;> omega
  unfold gFac
  rw [add_sub_cancel_right]
  simp only [h]

theorem gFac_tsum_near {k : ℕ} (n : ℤ) (σ : Pattern k) (i : Fin (2 * k)) :
    ∑' z : ℤ, gFac n σ i z ≤ ENNReal.ofReal 5 := by
  rw [← (Equiv.addRight n).tsum_eq]
  refine le_trans (ENNReal.tsum_le_tsum fun m => ?_) (le_trans (tail_sum_le 1 le_rfl) ?_)
  · show gFac n σ i (m + n) ≤ _
    rw [gFac_shift]
    by_cases h : m ≠ 0 ∧ nearFarBit n (m + n) = σ i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]; exact zero_le
  · apply ENNReal.ofReal_le_ofReal
    norm_num

theorem gFac_tsum_far {k : ℕ} (n : ℤ) (hn : n ≠ 0) (σ : Pattern k) (i : Fin (2 * k))
    (hσ : σ i = true) :
    ∑' z : ℤ, gFac n σ i z ≤ ENNReal.ofReal (5 / (n.natAbs : ℝ)) := by
  set N : ℕ := n.natAbs with hN
  have hNpos : 0 < N := Int.natAbs_pos.2 hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [← (Equiv.addRight n).tsum_eq]
  have hcond : ∀ m : ℤ, (m ≠ 0 ∧ nearFarBit n (m + n) = σ i) ↔ (N / 2 + 1 ≤ m.natAbs) := by
    intro m
    rw [hσ, nearFarBit_eq_true_iff, add_sub_cancel_right]
    constructor
    · rintro ⟨_, h⟩
      have h' : (N : ℝ) < 2 * (m.natAbs : ℝ) := by linarith
      have : N < 2 * m.natAbs := by exact_mod_cast h'
      omega
    · intro h
      have h' : N < 2 * m.natAbs := by omega
      refine ⟨fun h0 => ?_, ?_⟩
      · subst h0; simp at h'
      · have : (N : ℝ) < 2 * (m.natAbs : ℝ) := by exact_mod_cast h'
        linarith
  have hk : 1 ≤ N / 2 + 1 := by omega
  refine le_trans (le_of_eq ?_) (le_trans (tail_sum_le (N / 2 + 1) hk) ?_)
  · refine tsum_congr fun m => ?_
    show gFac n σ i (m + n) = _
    rw [gFac_shift]
    by_cases h : m ≠ 0 ∧ nearFarBit n (m + n) = σ i
    · rw [if_pos h, if_pos ((hcond m).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hcond m).2 h'))]
  · apply ENNReal.ofReal_le_ofReal
    have h2 : (N : ℝ) + 1 ≤ 2 * ((N / 2 + 1 : ℕ) : ℝ) := by
      have : N + 1 ≤ 2 * (N / 2 + 1) := by omega
      exact_mod_cast this
    have hden : (N : ℝ) / 2 ≤ ((N / 2 + 1 : ℕ) : ℝ) - 1 / 2 := by linarith
    have h3 : 2 / (((N / 2 + 1 : ℕ) : ℝ) - 1 / 2) ≤ 2 / ((N : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    refine le_trans h3 ?_
    rw [div_div_eq_mul_div, div_le_div_iff₀ hNr hNr]
    nlinarith

theorem kst023 (k : ℕ) (hk : 1 ≤ k) (n : ℤ) (hn : n ≠ 0)
    (σ : Pattern k) :
  denominatorPattern n σ < ⊤ ∧
  denominatorPattern n σ ≤ ENNReal.ofReal
    (5^(2*k) / (n.natAbs : ℝ)^(patternOnes σ)) := by
  have hNpos : 0 < n.natAbs := Int.natAbs_pos.2 hn
  have hNr : (0 : ℝ) < n.natAbs := by exact_mod_cast hNpos
  set c : Fin (2 * k) → ℝ := fun i => 5 * (if σ i then ((n.natAbs : ℝ))⁻¹ else 1) with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    simp only [hc]; split_ifs <;> positivity
  have hbound : denominatorPattern n σ ≤ ENNReal.ofReal (∏ i, c i) := by
    rw [denominatorPattern_eq, ENNReal.ofReal_prod_of_nonneg (fun i _ => hc0 i)]
    refine Finset.prod_le_prod' fun i _ => ?_
    by_cases hσ : σ i = true
    · refine le_trans (gFac_tsum_far n hn σ i hσ) (le_of_eq ?_)
      simp only [hc, hσ, if_true]
      rw [div_eq_mul_inv]
    · refine le_trans (gFac_tsum_near n σ i) (le_of_eq ?_)
      simp [hc, hσ]
  have hprod : ∏ i, c i = 5 ^ (2 * k) / (n.natAbs : ℝ) ^ (patternOnes σ) := by
    simp only [hc]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : ∏ i : Fin (2 * k), (if σ i then ((n.natAbs : ℝ))⁻¹ else 1) =
        ((n.natAbs : ℝ)⁻¹) ^ (patternOnes σ) := by
      unfold patternOnes
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [this, inv_pow, div_eq_mul_inv]
  rw [hprod] at hbound
  exact ⟨lt_of_le_of_lt hbound ENNReal.ofReal_lt_top, hbound⟩


end NlsGge.ThirdConsultation.KST
