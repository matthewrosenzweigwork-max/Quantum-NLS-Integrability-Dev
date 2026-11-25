import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.Support.ContourChain

/- M-008 SUPPORT E0 (proof development, AUTHOR; not reviewed).  Bridge between the two landed notions of piecewise `C^1` path:
   the inductive `LIB042`/`ContourChain` notion (leaves and `Path.trans`) and the partition notion of the SlitContours library
   (`LIB079` `gap_cycle_period` is stated for the latter).  Every `ContourChain.Chain` path is `PiecewiseC1` in the SlitContours sense.
   Route: a closed-cell form `ClosedCellC1` (C^1 on each closed cell of a time partition) which is closed under `Path.trans`
   by explicit concatenation of the two partitions at the parameter `1/2`. -/
set_option autoImplicit false
open Set Filter Topology Metric
open scoped unitInterval
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

section Bridge

def ClosedCellC1 {a b : ℂ} (γ : Path a b) : Prop :=
  ∃ P : TimePartition, ∀ i : Fin P.n,
    ContDiffOn ℝ 1 γ.extend (Icc (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ))

theorem ClosedCellC1.piecewiseC1 {a b : ℂ} {γ : Path a b} (h : ClosedCellC1 γ) : PiecewiseC1 γ := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, fun i => ?_⟩
  set s : I := P.cut i.castSucc with hs
  set t : I := P.cut i.succ with ht
  have hst : (s : ℝ) ≤ (t : ℝ) :=
    Subtype.coe_le_coe.2 (P.strict (Fin.castSucc_lt_succ (i := i))).le
  have hmap : MapsTo (fun u : ℝ => (s : ℝ) + u * ((t : ℝ) - (s : ℝ))) (Icc (0 : ℝ) 1)
      (Icc (s : ℝ) (t : ℝ)) := by
    intro u hu
    constructor
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.2 hst)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hu.2) (sub_nonneg.2 hst)]
  have hc : ContDiffOn ℝ 1 (fun u : ℝ => γ.extend ((s : ℝ) + u * ((t : ℝ) - (s : ℝ)))) (Icc (0 : ℝ) 1) :=
    (hP i).comp (by fun_prop : ContDiff ℝ 1 fun u : ℝ => (s : ℝ) + u * ((t : ℝ) - (s : ℝ))).contDiffOn hmap
  exact hc.congr (fun u hu => subpath_extend_eq γ s t u hu)

theorem closedCell_of_contDiffOn {a b : ℂ} (γ : Path a b) (h : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) :
    ClosedCellC1 γ := by
  refine ⟨singlePartition, fun i => ?_⟩
  have hi : (i : ℕ) = 0 := by
    have h := i.isLt
    change (i : ℕ) < 1 at h
    omega
  have e0 : i.castSucc = 0 := Fin.ext (by simp [hi])
  have e1 : i.succ = Fin.last singlePartition.n :=
    Fin.ext (by rw [Fin.val_succ, hi, Fin.val_last]; rfl)
  rw [e0, e1, singlePartition.first, singlePartition.last]
  simpa using h

/-- Natural-number indexed cuts of a time partition (value `1` beyond the last index). -/
def cutR (P : TimePartition) (k : ℕ) : ℝ := if h : k < P.n + 1 then ((P.cut ⟨k, h⟩ : I) : ℝ) else 1

theorem cutR_mem (P : TimePartition) (k : ℕ) : cutR P k ∈ Icc (0 : ℝ) 1 := by
  unfold cutR
  split_ifs with h
  · exact (P.cut ⟨k, h⟩).2
  · exact ⟨zero_le_one, le_refl 1⟩

theorem cutR_zero (P : TimePartition) : cutR P 0 = 0 := by
  unfold cutR
  rw [dif_pos (Nat.succ_pos _)]
  have : (⟨0, Nat.succ_pos _⟩ : Fin (P.n + 1)) = 0 := rfl
  rw [this, P.first]
  simp

theorem cutR_last (P : TimePartition) : cutR P P.n = 1 := by
  unfold cutR
  rw [dif_pos (Nat.lt_succ_self _)]
  have : (⟨P.n, Nat.lt_succ_self _⟩ : Fin (P.n + 1)) = Fin.last P.n := rfl
  rw [this, P.last]
  simp

theorem partition_n_pos' (P : TimePartition) : 0 < P.n := by
  by_contra h
  have h0 : P.n = 0 := Nat.eq_zero_of_not_pos h
  have e : (Fin.last P.n : Fin (P.n + 1)) = 0 := Fin.ext (by simp [h0])
  have := P.last
  rw [e, P.first] at this
  exact zero_ne_one this

theorem cutR_lt (P : TimePartition) {k : ℕ} (hk : k < P.n) : cutR P k < cutR P (k + 1) := by
  unfold cutR
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact Subtype.coe_lt_coe.2 (P.strict (Fin.mk_lt_mk.2 (Nat.lt_succ_self k)))

/-- Cuts of the concatenated partition: `P` rescaled to `[0,1/2]`, then `Q` rescaled to `[1/2,1]`. -/
def transCut (P Q : TimePartition) (k : ℕ) : ℝ :=
  if k ≤ P.n then cutR P k / 2 else (cutR Q (k - P.n) + 1) / 2

theorem transCut_mem (P Q : TimePartition) (k : ℕ) : transCut P Q k ∈ Icc (0 : ℝ) 1 := by
  unfold transCut
  have h1 := cutR_mem P k
  have h2 := cutR_mem Q (k - P.n)
  split_ifs
  · constructor <;> linarith [h1.1, h1.2]
  · constructor <;> linarith [h2.1, h2.2]

theorem transCut_lt (P Q : TimePartition) {k : ℕ} (hk : k < P.n + Q.n) :
    transCut P Q k < transCut P Q (k + 1) := by
  have hQ := partition_n_pos' Q
  unfold transCut
  by_cases h1 : k + 1 ≤ P.n
  · rw [if_pos (by omega), if_pos h1]
    have := cutR_lt P (by omega : k < P.n)
    linarith
  · by_cases h2 : k = P.n
    · subst h2
      rw [if_pos le_rfl, if_neg h1, cutR_last, show P.n + 1 - P.n = 1 by omega]
      have := cutR_lt Q hQ
      rw [cutR_zero] at this
      linarith
    · rw [if_neg (by omega), if_neg h1,
        show k + 1 - P.n = (k - P.n) + 1 by omega]
      have := cutR_lt Q (by omega : k - P.n < Q.n)
      linarith

/-- Concatenation of two time partitions at `1/2`. -/
def transPartition (P Q : TimePartition) : TimePartition where
  n := P.n + Q.n
  cut := fun k => ⟨transCut P Q k.val, transCut_mem P Q k.val⟩
  first := by
    apply Subtype.ext
    show transCut P Q 0 = 0
    unfold transCut
    rw [if_pos (Nat.zero_le _), cutR_zero]
    norm_num
  last := by
    apply Subtype.ext
    show transCut P Q (P.n + Q.n) = 1
    have hQ := partition_n_pos' Q
    unfold transCut
    rw [if_neg (by omega), show P.n + Q.n - P.n = Q.n by omega, cutR_last]
    norm_num
  strict := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    exact Subtype.mk_lt_mk.2 (transCut_lt P Q i.isLt)

theorem closedCell_trans {a b c : ℂ} {γ : Path a b} {δ : Path b c}
    (hγ : ClosedCellC1 γ) (hδ : ClosedCellC1 δ) : ClosedCellC1 (γ.trans δ) := by
  obtain ⟨P, hP⟩ := hγ
  obtain ⟨Q, hQ⟩ := hδ
  refine ⟨transPartition P Q, fun i => ?_⟩
  have hc : ((transPartition P Q).cut i.castSucc : ℝ) = transCut P Q i.val := rfl
  have hs : ((transPartition P Q).cut i.succ : ℝ) = transCut P Q (i.val + 1) := rfl
  rw [hc, hs]
  by_cases hi : i.val < P.n
  · let i' : Fin P.n := ⟨i.val, hi⟩
    have e1 : transCut P Q i.val = (P.cut i'.castSucc : ℝ) / 2 := by
      unfold transCut
      rw [if_pos hi.le]
      unfold cutR
      rw [dif_pos (Nat.lt_succ_of_lt hi)]
      rfl
    have e2 : transCut P Q (i.val + 1) = (P.cut i'.succ : ℝ) / 2 := by
      unfold transCut
      rw [if_pos (Nat.succ_le_of_lt hi)]
      unfold cutR
      rw [dif_pos (by omega)]
      rfl
    rw [e1, e2]
    have hb := (P.cut i'.succ).2.2
    have hcd : ContDiffOn ℝ 1 (fun u : ℝ => γ.extend (2 * u))
        (Icc ((P.cut i'.castSucc : ℝ) / 2) ((P.cut i'.succ : ℝ) / 2)) :=
      (hP i').comp (contDiff_const.mul contDiff_id).contDiffOn
        (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    refine hcd.congr (fun u hu => ?_)
    exact Path.extend_trans_of_le_half γ δ (by linarith [hu.2])
  · have hi' : P.n ≤ i.val := not_lt.1 hi
    have hjlt : i.val - P.n < Q.n := by
      have := i.isLt
      change i.val < P.n + Q.n at this
      omega
    let j : Fin Q.n := ⟨i.val - P.n, hjlt⟩
    have e1 : transCut P Q i.val = ((Q.cut j.castSucc : ℝ) + 1) / 2 := by
      unfold transCut
      by_cases h : i.val ≤ P.n
      · have hv : i.val = P.n := le_antisymm h hi'
        rw [if_pos h]
        have hj0 : j.castSucc = 0 := Fin.ext (by simp [j, hv])
        rw [hj0, Q.first, hv, cutR_last]
        norm_num
      · rw [if_neg h]
        unfold cutR
        rw [dif_pos (by omega)]
        rfl
    have e2 : transCut P Q (i.val + 1) = ((Q.cut j.succ : ℝ) + 1) / 2 := by
      unfold transCut
      rw [if_neg (by omega)]
      unfold cutR
      rw [dif_pos (by omega)]
      have : (⟨i.val + 1 - P.n, by omega⟩ : Fin (Q.n + 1)) = j.succ := Fin.ext (by simp [j]; omega)
      rw [this]
    rw [e1, e2]
    have ha := (Q.cut j.castSucc).2.1
    have hb := (Q.cut j.succ).2.2
    have hcd : ContDiffOn ℝ 1 (fun u : ℝ => δ.extend (2 * u - 1))
        (Icc (((Q.cut j.castSucc : ℝ) + 1) / 2) (((Q.cut j.succ : ℝ) + 1) / 2)) :=
      (hQ j).comp ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffOn
        (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    refine hcd.congr (fun u hu => ?_)
    exact Path.extend_trans_of_half_le γ δ (by linarith [hu.1])

theorem chain_path_closedCell : ∀ {a b : ℂ} (c : NlsGge.Atomic.ContourChain.Chain a b),
    ClosedCellC1 c.path := by
  intro a b c
  induction c with
  | leaf γ hc => exact closedCell_of_contDiffOn γ hc
  | join p q hp hq => exact closedCell_trans hp hq

/-- Every `ContourChain` path is piecewise `C^1` in the SlitContours sense. -/
theorem chain_path_slit_piecewiseC1 {a b : ℂ} (c : NlsGge.Atomic.ContourChain.Chain a b) :
    PiecewiseC1 c.path :=
  (chain_path_closedCell c).piecewiseC1

end Bridge

end
end NlsGge.ThirdConsultation.MContour
