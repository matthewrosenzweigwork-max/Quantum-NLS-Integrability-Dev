import Mathlib
import NlsGge.Atomic.KSTPath
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST023
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST025

/- KST-026 PRODUCTION01 (proof development landing kit; HELD; variant for landing AFTER KST-025, which hosts sourcePatternFourierEnergy/weightedCauchyPatternSum; defs removed). Source: proof development/KST026_P2_06.lean.txt (author proof development; independent review proof development/REVIEW_KST026_01.md), identical except this header and the removed #check/#print axioms lines. Target NlsGge/Atomic/KST/KST026.lean. Pro definitions sourcePatternFourierEnergy/weightedCauchyPatternSum are declared here (not in production yet). -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST

namespace NlsGge.ThirdConsultation.KST

namespace K026Aux

theorem vi_val {k : ℕ} (hk : 0 < k) (i : ℕ) (hi : i < 2 * k) :
    (vertexIndex hk i).val = i := by
  rw [vertexIndex_eq_mk hk hi]

theorem nonforced_witness {k : ℕ} (hk : 0 < k) (σ : Pattern k) (j : Fin (2*k+1))
    (hj : ¬ forcedAt hk σ j) :
    ∃ i : Fin (2*k), σ i = true ∧ (i.val = j.val ∨ i.val + 1 = j.val) := by
  unfold forcedAt at hj
  by_cases h0 : j.val = 0
  · rw [if_pos h0] at hj
    exact ⟨⟨0, by omega⟩, by simpa using hj, Or.inl h0.symm⟩
  · rw [if_neg h0] at hj
    by_cases h1 : j.val < 2 * k
    · rw [if_pos h1] at hj
      by_cases ha : σ (vertexIndex hk (j.val - 1)) = false
      · have hb : σ (vertexIndex hk j.val) = true := by
          by_contra hb
          exact hj ⟨ha, by simpa using hb⟩
        exact ⟨vertexIndex hk j.val, hb, Or.inl (vi_val hk _ h1)⟩
      · refine ⟨vertexIndex hk (j.val - 1), by simpa using ha, Or.inr ?_⟩
        rw [vi_val hk _ (by omega)]; omega
    · rw [if_neg h1] at hj
      refine ⟨vertexIndex hk (2 * k - 1), by simpa using hj, Or.inr ?_⟩
      rw [vi_val hk _ (by omega)]; omega

theorem forced_card_le {k : ℕ} (hk : 0 < k) (σ : Pattern k) :
    2 * k + 1 - forcedTailCount hk σ ≤ 2 * patternOnes σ := by
  classical
  have hcomp : 2 * k + 1 ≤ (Finset.univ.filter (forcedAt hk σ)).card +
      (Finset.univ.filter (fun j => ¬ forcedAt hk σ j)).card := by
    have hsub : (Finset.univ : Finset (Fin (2*k+1))) ⊆
        Finset.univ.filter (forcedAt hk σ) ∪ Finset.univ.filter (fun j => ¬ forcedAt hk σ j) := by
      intro j _
      by_cases hj : forcedAt hk σ j <;> simp [hj]
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa using this
  have hτ : forcedTailCount hk σ = (Finset.univ.filter (forcedAt hk σ)).card := by
    unfold forcedTailCount; congr
  have hones : patternOnes σ = (Finset.univ.filter (fun i : Fin (2*k) => σ i = true)).card := by
    unfold patternOnes
    rw [Finset.card_filter]
  set far := Finset.univ.filter (fun i : Fin (2*k) => σ i = true) with hfar
  have hsub : Finset.univ.filter (fun j => ¬ forcedAt hk σ j) ⊆
      far.image (fun i => (⟨i.val, by omega⟩ : Fin (2*k+1))) ∪
      far.image (fun i => (⟨i.val + 1, by omega⟩ : Fin (2*k+1))) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨i, hi, hij⟩ := nonforced_witness hk σ j hj.2
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases hij with h | h
    · left; exact ⟨i, by simp [hfar, hi], Fin.ext h⟩
    · right; exact ⟨i, by simp [hfar, hi], Fin.ext h⟩
  have hc := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le))
  omega

theorem near_nat (n z : ℤ) (h : nearFarBit n z = false) :
    2 * (z - n).natAbs ≤ n.natAbs := by
  have := (nearFarBit_eq_false_iff n z).1 h
  have h2 : (2 * (z - n).natAbs : ℝ) ≤ n.natAbs := by linarith
  exact_mod_cast h2

theorem forced_arg_large {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) (σ : Pattern k)
    (hσ : ∀ i, nearFarBit n (ℓ i) = σ i) (j : Fin (2*k+1)) (hj : forcedAt hk σ j) :
    n.natAbs ≤ (pathArgument hk n ℓ j).natAbs := by
  unfold forcedAt at hj
  unfold pathArgument
  by_cases h0 : j.val = 0
  · rw [if_pos h0] at hj ⊢
    have e0 : vertexIndex hk 0 = ⟨0, by omega⟩ := vertexIndex_eq_mk hk _
    rw [e0]
    have := near_nat n _ ((hσ _).trans hj)
    omega
  · rw [if_neg h0] at hj ⊢
    by_cases h1 : j.val < 2 * k
    · rw [if_pos h1] at hj ⊢
      have a := near_nat n _ ((hσ _).trans hj.1)
      have b := near_nat n _ ((hσ _).trans hj.2)
      omega
    · rw [if_neg h1] at hj ⊢
      have := near_nat n _ ((hσ _).trans hj)
      omega

theorem pathArgument_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (fun p : ℤ × Path k => fun j => pathArgument hk p.1 p.2 j) := by
  intro p q h0
  have h : ∀ j, pathArgument hk p.1 p.2 j = pathArgument hk q.1 q.2 j := fun j => congr_fun h0 j
  have hn : p.1 = q.1 := by
    have e1 := pathArgument_alt_sum hk p.1 p.2
    have e2 := pathArgument_alt_sum hk q.1 q.2
    have : (∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ j.val * pathArgument hk p.1 p.2 j) =
        ∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ j.val * pathArgument hk q.1 q.2 j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h j]
    omega
  have hl : ∀ i : ℕ, ∀ hi : i < 2 * k, p.2 ⟨i, hi⟩ = q.2 ⟨i, hi⟩ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h0 : i = 0
      · subst h0
        have e := h ⟨0, by omega⟩
        simp only [pathArgument_zero, hn] at e
        omega
      · have e := h ⟨i, by omega⟩
        simp only [pathArgument_interior hk _ _ ⟨i, by omega⟩ (by simp; omega) (by simpa using hi), hn] at e
        have := ih (i - 1) (by omega) (by omega)
        omega
  refine Prod.ext hn (funext fun i => ?_)
  exact hl i.val i.isLt


open Classical in
def slotG {k : ℕ} (hk : 0 < k) (w A : ℤ → ℝ) (N : ℕ) (σ : Pattern k)
    (j0 j : Fin (2*k+1)) (z : ℤ) : ℝ≥0∞ :=
  if j = j0 then (if N ≤ z.natAbs then ENNReal.ofReal (w z ^ 2 * A z ^ 2) else 0)
  else if forcedAt hk σ j then
    (ENNReal.ofReal (w (N : ℤ) ^ 2))⁻¹ *
      (if N ≤ z.natAbs then ENNReal.ofReal (w z ^ 2 * A z ^ 2) else 0)
  else ENNReal.ofReal (w z ^ 2 * A z ^ 2)

open Classical in
theorem slotG_tsum {k : ℕ} (hk : 0 < k) (w A : ℤ → ℝ) (N : ℕ) (σ : Pattern k)
    (j0 j : Fin (2*k+1)) :
    ∑' z, slotG hk w A N σ j0 j z =
      if j = j0 then scalarTailEnergy w A N
      else if forcedAt hk σ j then
        (ENNReal.ofReal (w (N : ℤ) ^ 2))⁻¹ * scalarTailEnergy w A N
      else scalarEnergy w A := by
  classical
  unfold slotG
  by_cases h1 : j = j0
  · simp only [if_pos h1]; rfl
  · by_cases h2 : forcedAt hk σ j
    · simp only [if_neg h1, if_pos h2]
      rw [ENNReal.tsum_mul_left]; rfl
    · simp only [if_neg h1, if_neg h2]; rfl

theorem slotG_ge {k : ℕ} (hk : 0 < k) {w : ℤ → ℝ} {Cw : ℝ} (hw : SlowWeight w Cw)
    (A : ℤ → ℝ) (N : ℕ) (σ : Pattern k) (j0 j : Fin (2*k+1)) (hj : j ≠ j0) (z : ℤ)
    (hz : forcedAt hk σ j → N ≤ z.natAbs) :
    ENNReal.ofReal (A z ^ 2) ≤ slotG hk w A N σ j0 j z := by
  classical
  unfold slotG
  rw [if_neg hj]
  by_cases h2 : forcedAt hk σ j
  · rw [if_pos h2, if_pos (hz h2)]
    have hwN : 0 < w (N : ℤ) := lt_of_lt_of_le zero_lt_one (hw.one_le _)
    have hwz : w (N : ℤ) ≤ w z := hw.radial_mono _ _ (by simpa using hz h2)
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have : w (N : ℤ) ^ 2 ≤ w z ^ 2 := pow_le_pow_left₀ hwN.le hwz 2
    nlinarith [mul_nonneg (sq_nonneg (A z)) (sub_nonneg.2 this)]
  · rw [if_neg h2]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ w z := hw.one_le z
    nlinarith [sq_nonneg (A z), mul_nonneg (sq_nonneg (A z)) (sub_nonneg.2 (one_le_pow₀ h1 : (1:ℝ) ≤ w z ^ 2))]

theorem forced_exists_of_pos {k : ℕ} (hk : 0 < k) (σ : Pattern k)
    (hτ : 1 ≤ forcedTailCount hk σ) : ∃ j0, forcedAt hk σ j0 := by
  classical
  by_contra h
  push_neg at h
  have : forcedTailCount hk σ = 0 := by
    unfold forcedTailCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _; exact h j
  omega

open Classical in
theorem forced_card_eq {k : ℕ} (hk : 0 < k) (σ : Pattern k) :
    (Finset.univ.filter (fun j => forcedAt hk σ j)).card = forcedTailCount hk σ ∧
    (Finset.univ.filter (fun j => ¬ forcedAt hk σ j)).card = 2*k+1 - forcedTailCount hk σ := by
  classical
  have h1 : (Finset.univ.filter (fun j => forcedAt hk σ j)).card = forcedTailCount hk σ := by
    unfold forcedTailCount; congr
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2*k+1))))
    (fun j => forcedAt hk σ j)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  refine ⟨h1, ?_⟩
  omega

open Classical in
theorem prod_slot_sum {k : ℕ} (hk : 0 < k) (σ : Pattern k) (j0 : Fin (2*k+1))
    (hj0 : forcedAt hk σ j0) (T W E : ℝ≥0∞) :
    ∏ j : Fin (2*k+1), (if j = j0 then T else if forcedAt hk σ j then W * T else E) =
      T * (W * T) ^ (forcedTailCount hk σ - 1) * E ^ (2*k+1 - forcedTailCount hk σ) := by
  classical
  obtain ⟨hf, hn⟩ := forced_card_eq hk σ
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0), if_pos rfl, mul_assoc]
  congr 1
  rw [Finset.prod_congr rfl (g := fun j => if forcedAt hk σ j then W * T else E)
    (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_erase,
    Finset.card_erase_of_mem (by simpa using hj0), hf]
  congr 2
  rw [Finset.filter_erase] 
  have : j0 ∉ Finset.univ.filter (fun j => ¬ forcedAt hk σ j) := by simp [hj0]
  rw [Finset.erase_eq_of_notMem this, hn]


theorem pointwise_bound {k : ℕ} (hk : 0 < k) {w : ℤ → ℝ} {Cw : ℝ} (hw : SlowWeight w Cw)
    (A : ℤ → ℝ) (N : ℕ) (σ : Pattern k) (j0 : Fin (2*k+1)) (hj0 : forcedAt hk σ j0)
    (n : ℤ) (hn : N ≤ n.natAbs) (ℓ : Path k) (hσ : ∀ i, nearFarBit n (ℓ i) = σ i) :
    ENNReal.ofReal (w (2*n) ^ 2) * ENNReal.ofReal (∏ j, A (pathArgument hk n ℓ j) ^ 2) ≤
      ENNReal.ofReal (Cw ^ 2) * ∏ j, slotG hk w A N σ j0 j (pathArgument hk n ℓ j) := by
  classical
  have hCw : 1 ≤ Cw := slowWeight_Cw_one_le hw
  have hlarge : ∀ j, forcedAt hk σ j → N ≤ (pathArgument hk n ℓ j).natAbs :=
    fun j hj => hn.trans (forced_arg_large hk n ℓ σ hσ j hj)
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => sq_nonneg _)]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun j => ENNReal.ofReal (A (pathArgument hk n ℓ j) ^ 2)) (Finset.mem_univ j0),
    ← Finset.mul_prod_erase Finset.univ
      (fun j => slotG hk w A N σ j0 j (pathArgument hk n ℓ j)) (Finset.mem_univ j0)]
  have hrest : ∏ j ∈ Finset.univ.erase j0, ENNReal.ofReal (A (pathArgument hk n ℓ j) ^ 2) ≤
      ∏ j ∈ Finset.univ.erase j0, slotG hk w A N σ j0 j (pathArgument hk n ℓ j) :=
    Finset.prod_le_prod' fun j hj =>
      slotG_ge hk hw A N σ j0 j (Finset.ne_of_mem_erase hj) _ (hlarge j)
  have h0 : ENNReal.ofReal (w (2*n) ^ 2) * ENNReal.ofReal (A (pathArgument hk n ℓ j0) ^ 2) ≤
      ENNReal.ofReal (Cw ^ 2) * slotG hk w A N σ j0 j0 (pathArgument hk n ℓ j0) := by
    have hN0 := hlarge j0 hj0
    have hnabs := forced_arg_large hk n ℓ σ hσ j0 hj0
    unfold slotG
    rw [if_pos rfl, if_pos hN0, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hwn : w n ≤ w (pathArgument hk n ℓ j0) := hw.radial_mono _ _ hnabs
    have hw2 : w (2*n) ≤ Cw * w (pathArgument hk n ℓ j0) :=
      (hw.doubling n).trans (mul_le_mul_of_nonneg_left hwn (by linarith))
    have hw0 : 0 ≤ w (2*n) := by linarith [hw.one_le (2*n)]
    have hsq : w (2*n) ^ 2 ≤ Cw ^ 2 * w (pathArgument hk n ℓ j0) ^ 2 := by
      calc w (2*n) ^ 2 ≤ (Cw * w (pathArgument hk n ℓ j0)) ^ 2 := pow_le_pow_left₀ hw0 hw2 2
        _ = _ := by ring
    calc w (2*n) ^ 2 * A (pathArgument hk n ℓ j0) ^ 2
        ≤ (Cw ^ 2 * w (pathArgument hk n ℓ j0) ^ 2) * A (pathArgument hk n ℓ j0) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = _ := by ring
  calc ENNReal.ofReal (w (2*n) ^ 2) *
        (ENNReal.ofReal (A (pathArgument hk n ℓ j0) ^ 2) *
          ∏ j ∈ Finset.univ.erase j0, ENNReal.ofReal (A (pathArgument hk n ℓ j) ^ 2))
      = (ENNReal.ofReal (w (2*n) ^ 2) * ENNReal.ofReal (A (pathArgument hk n ℓ j0) ^ 2)) *
          ∏ j ∈ Finset.univ.erase j0, ENNReal.ofReal (A (pathArgument hk n ℓ j) ^ 2) := by ring
    _ ≤ (ENNReal.ofReal (Cw ^ 2) * slotG hk w A N σ j0 j0 (pathArgument hk n ℓ j0)) *
          ∏ j ∈ Finset.univ.erase j0, slotG hk w A N σ j0 j (pathArgument hk n ℓ j) :=
        mul_le_mul' h0 hrest
    _ = _ := by ring

theorem ratio_bound (N p q : ℕ) (hN : 1 ≤ N) (hqp : q ≤ 2 * p) (m : ℕ) (hm : N ≤ m) :
    1 / (m : ℝ) ^ p ≤ (1 / Real.sqrt (N : ℝ)) ^ q := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hs : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.2 hNr
  have hspos : 0 < Real.sqrt (N : ℝ) := by linarith
  have h1 : (1 / Real.sqrt (N : ℝ)) ^ (2 * p) ≤ (1 / Real.sqrt (N : ℝ)) ^ q :=
    pow_le_pow_of_le_one (by positivity) (div_le_one_of_le₀ hs hspos.le) hqp
  have h2 : (1 / Real.sqrt (N : ℝ)) ^ 2 = 1 / (N : ℝ) := by
    rw [div_pow, Real.sq_sqrt hNpos.le]; simp
  have hmr : (N : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : 1 / (m : ℝ) ^ p ≤ (1 / Real.sqrt (N : ℝ)) ^ (2 * p) := by
    rw [pow_mul, h2, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hNpos hmr) p
  exact h3.trans h1

end K026Aux

open K026Aux

theorem kst026 (w A : ℤ → ℝ) (Cw : ℝ)
    (hw : SlowWeight w Cw) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy w A < ⊤) (N k : ℕ) (hN : 1 ≤ N)
    (hk : 0 < k) (σ : Pattern k) (hτ : 1 ≤ forcedTailCount hk σ) :
  weightedCauchyPatternSum hk w A N σ < ⊤ ∧
  weightedCauchyPatternSum hk w A N σ ≤ ENNReal.ofReal
    (5^(2*k) * Cw^2 * (scalarTailEnergy w A N).toReal *
      ((scalarTailEnergy w A N).toReal / w (N : ℤ)^2)^(forcedTailCount hk σ - 1) *
      ((scalarEnergy w A).toReal / Real.sqrt (N : ℝ))^
        (2*k+1-forcedTailCount hk σ)) := by
  classical
  obtain ⟨j0, hj0⟩ := forced_exists_of_pos hk σ hτ
  have hqp : 2 * k + 1 - forcedTailCount hk σ ≤ 2 * patternOnes σ := forced_card_le hk σ
  have hTE : scalarTailEnergy w A N ≤ scalarEnergy w A :=
    ENNReal.tsum_le_tsum fun j => by
      by_cases h : N ≤ j.natAbs <;> simp [h]
  have hEt : scalarEnergy w A ≠ ⊤ := hE.ne
  have hTt : scalarTailEnergy w A N ≠ ⊤ := ne_top_of_le_ne_top hEt hTE
  have hwN : 0 < w (N : ℤ) := lt_of_lt_of_le zero_lt_one (hw.one_le _)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by linarith)
  let c : ℝ≥0∞ := ENNReal.ofReal (5 ^ (2 * k) * (1 / Real.sqrt (N : ℝ)) ^
      (2 * k + 1 - forcedTailCount hk σ))
  let Hf : ℤ → Path k → ℝ≥0∞ := fun n ℓ =>
    if N ≤ n.natAbs ∧ (admissiblePath n ℓ ∧ ∀ i, nearFarBit n (ℓ i) = σ i) then
      ENNReal.ofReal (w (2*n) ^ 2) *
        ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j) ^ 2) else 0
  have hper : ∀ n : ℤ, (if N ≤ n.natAbs then
      ENNReal.ofReal (w (2*n)^2) * denominatorPattern n σ *
        sourcePatternFourierEnergy hk A n σ else 0) ≤ c * ∑' ℓ : Path k, Hf n ℓ := by
    intro n
    by_cases hn : N ≤ n.natAbs
    · rw [if_pos hn]
      have hn0 : n ≠ 0 := by
        intro h; subst h; simp at hn; omega
      obtain ⟨_, hD⟩ := kst023 k hk n hn0 σ
      have hDc : denominatorPattern n σ ≤ c := by
        refine hD.trans (ENNReal.ofReal_le_ofReal ?_)
        have := ratio_bound N (patternOnes σ) (2 * k + 1 - forcedTailCount hk σ) hN hqp
          n.natAbs hn
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have hB : ENNReal.ofReal (w (2*n)^2) * sourcePatternFourierEnergy hk A n σ =
          ∑' ℓ : Path k, Hf n ℓ := by
        unfold sourcePatternFourierEnergy
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ℓ => ?_
        by_cases h : admissiblePath n ℓ ∧ (∀ i, nearFarBit n (ℓ i) = σ i)
        · simp only [Hf, if_pos h, if_pos (And.intro hn h)]
        · have hc : ¬ (N ≤ n.natAbs ∧ (admissiblePath n ℓ ∧ ∀ i, nearFarBit n (ℓ i) = σ i)) :=
            fun h' => h h'.2
          simp only [Hf, if_neg h, if_neg hc, mul_zero]
      calc ENNReal.ofReal (w (2*n)^2) * denominatorPattern n σ *
            sourcePatternFourierEnergy hk A n σ
          = denominatorPattern n σ *
            (ENNReal.ofReal (w (2*n)^2) * sourcePatternFourierEnergy hk A n σ) := by ring
        _ ≤ c * ∑' ℓ : Path k, Hf n ℓ := by rw [hB]; exact mul_le_mul' hDc le_rfl
    · rw [if_neg hn]; exact zero_le
  have hHf : ∀ p : ℤ × Path k, Hf p.1 p.2 ≤ ENNReal.ofReal (Cw ^ 2) *
      ∏ j : Fin (2*k+1), slotG hk w A N σ j0 j
        ((fun p : ℤ × Path k => fun j => pathArgument hk p.1 p.2 j) p j) := by
    intro p
    by_cases h : N ≤ p.1.natAbs ∧ (admissiblePath p.1 p.2 ∧ ∀ i, nearFarBit p.1 (p.2 i) = σ i)
    · simp only [Hf, if_pos h]
      exact pointwise_bound hk hw A N σ j0 hj0 p.1 h.1 p.2 h.2.2
    · simp only [Hf, if_neg h]; exact zero_le
  have hsum1 : ∑' p : ℤ × Path k, Hf p.1 p.2 ≤ ENNReal.ofReal (Cw ^ 2) *
      ∏ j : Fin (2*k+1), ∑' z, slotG hk w A N σ j0 j z := by
    calc ∑' p : ℤ × Path k, Hf p.1 p.2
        ≤ ∑' p : ℤ × Path k, ENNReal.ofReal (Cw ^ 2) *
            (fun x : Fin (2*k+1) → ℤ => ∏ j : Fin (2*k+1), slotG hk w A N σ j0 j (x j))
              ((fun p : ℤ × Path k => fun j => pathArgument hk p.1 p.2 j) p) :=
          ENNReal.tsum_le_tsum hHf
      _ = ENNReal.ofReal (Cw ^ 2) *
          ∑' p : ℤ × Path k,
            (fun x : Fin (2*k+1) → ℤ => ∏ j : Fin (2*k+1), slotG hk w A N σ j0 j (x j))
              ((fun p : ℤ × Path k => fun j => pathArgument hk p.1 p.2 j) p) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (Cw ^ 2) *
          ∑' x : Fin (2*k+1) → ℤ, ∏ j : Fin (2*k+1), slotG hk w A N σ j0 j (x j) :=
          mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective (pathArgument_injective hk)
            (fun x : Fin (2*k+1) → ℤ => ∏ j : Fin (2*k+1), slotG hk w A N σ j0 j (x j)))
      _ = _ := by rw [tsum_pi_fin_prod (2*k+1) (fun j => slotG hk w A N σ j0 j)]
  have hprod : ∏ j : Fin (2*k+1), ∑' z, slotG hk w A N σ j0 j z =
      scalarTailEnergy w A N *
        ((ENNReal.ofReal (w (N : ℤ) ^ 2))⁻¹ * scalarTailEnergy w A N) ^
          (forcedTailCount hk σ - 1) *
        scalarEnergy w A ^ (2*k+1 - forcedTailCount hk σ) := by
    rw [← prod_slot_sum hk σ j0 hj0]
    exact Finset.prod_congr rfl fun j _ => slotG_tsum hk w A N σ j0 j
  have hmain : weightedCauchyPatternSum hk w A N σ ≤
      c * (ENNReal.ofReal (Cw ^ 2) *
        (scalarTailEnergy w A N *
        ((ENNReal.ofReal (w (N : ℤ) ^ 2))⁻¹ * scalarTailEnergy w A N) ^
          (forcedTailCount hk σ - 1) *
        scalarEnergy w A ^ (2*k+1 - forcedTailCount hk σ))) := by
    unfold weightedCauchyPatternSum
    calc _ ≤ ∑' n : ℤ, c * ∑' ℓ : Path k, Hf n ℓ := ENNReal.tsum_le_tsum hper
      _ = c * ∑' p : ℤ × Path k, Hf p.1 p.2 := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_prod (f := Hf)]
      _ ≤ _ := by
          rw [← hprod]; exact mul_le_mul' le_rfl hsum1
  set t := (scalarTailEnergy w A N).toReal with ht
  set e := (scalarEnergy w A).toReal with he
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have hT : scalarTailEnergy w A N = ENNReal.ofReal t := (ENNReal.ofReal_toReal hTt).symm
  have hE' : scalarEnergy w A = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEt).symm
  have hWT : (ENNReal.ofReal (w (N : ℤ) ^ 2))⁻¹ * scalarTailEnergy w A N =
      ENNReal.ofReal (t / w (N : ℤ) ^ 2) := by
    rw [hT, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
      inv_mul_eq_div]
  have hfin : weightedCauchyPatternSum hk w A N σ ≤ ENNReal.ofReal
      (5^(2*k) * Cw^2 * t * (t / w (N : ℤ)^2)^(forcedTailCount hk σ - 1) *
        (e / Real.sqrt (N : ℝ))^(2*k+1-forcedTailCount hk σ)) := by
    refine hmain.trans (le_of_eq ?_)
    rw [hWT, hT, hE']
    simp (disch := positivity) only [c, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul]
    congr 1
    rw [div_pow]
    ring
  exact ⟨lt_of_le_of_lt hfin ENNReal.ofReal_lt_top, hfin⟩

end NlsGge.ThirdConsultation.KST
