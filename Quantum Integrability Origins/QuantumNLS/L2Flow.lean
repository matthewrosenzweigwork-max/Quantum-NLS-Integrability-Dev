import QuantumNLS.L4Translate

/-!
# EXT-003, Route Y stage (v), part E: the global `L²` flow (R-AEE17FD6, physical part)

`ROOT_L2_extension.tex`, `thm:root-L2-flow`: "For `κ ≥ 0` and every `f ∈ L²(𝕋_L)` there is a unique
global Duhamel solution of `i∂_t u = −∂_x²u + 2κ|u|²u`, `u(0) = f`, in
`C(ℝ;L²) ∩ L⁴_loc(ℝ × 𝕋_L)`. The flow preserves the `L²` norm, agrees with the `H¹` flow of
Theorem F04:thm-global, and depends Lipschitz continuously on the initial datum on each bounded
`L²` ball over each fixed finite time interval, in both `C_tL²_x` and `L⁴_{t,x}`. Each time map is
a homeomorphism with inverse the map at the negative time."

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4); the quoted local input is
proved elementarily (LC1) and everything here rests on LS1/LS2, DD1, DDL1, SG1, DL4a/DL4b, LC1,
UQ1, HB1, GLU1, TR1 (read-only) and GL1 (`F04Global`, read-only).

The solution class (`IsFlow κ w`): `w ∈ C(ℝ; L²)` and on every time interval `J = (α, β]` of length
`≤ T_L` there is `u ∈ L⁴(J × 𝕋_L)` whose time slices are `w(t)` and which solves the cubic Duhamel
equation `w(t) = U(t − a) w(a) − 2iκ ∫_a^t U(t − s)(|u|²u)(s) ds` for all `a, t ∈ [α, β]`
(`Sol`). Every compact time set is covered by finitely many such intervals, so this is
`C(ℝ;L²) ∩ L⁴_loc` with the Duhamel formula between any two times.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.DuhamelL4 QuantumNLS.DuhamelL4Limit
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Uniqueness QuantumNLS.H1Bridge QuantumNLS.L4Gluing
  QuantumNLS.L4Translate

namespace QuantumNLS.L2Flow

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. The solution class and uniqueness -/

/-- **Global Duhamel solutions in `C(ℝ;L²) ∩ L⁴_loc`** of `i∂_t u = −∂_x²u + 2κ|u|²u`. -/
def IsFlow (κ : ℝ) (w : ℝ → HL L) : Prop :=
  Continuous w ∧ ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L),
    ∃ u : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u w

/-- Half of the admissible length `min(1, T_L)`. -/
def hh (L : ℝ) [Fact (0 < L)] : ℝ := min 1 (TL L) / 2

lemma hh_pos : 0 < hh L := by
  have := TL_pos (L := L)
  unfold hh
  have : 0 < min 1 (TL L) := lt_min one_pos this
  positivity

lemma two_hh_le_one : 2 * hh L ≤ 1 := by
  unfold hh; linarith [min_le_left 1 (TL L)]

lemma two_hh_le_TL : 2 * hh L ≤ TL L := by
  unfold hh; linarith [min_le_right 1 (TL L)]

/-- **Uniqueness in the class**: two global solutions equal at one time are equal. -/
theorem flow_unique {κ : ℝ} {w w' : ℝ → HL L} (hw : IsFlow κ w) (hw' : IsFlow κ w') {t₀ : ℝ}
    (h0 : w t₀ = w' t₀) : w = w' := by
  have hδ := hh_pos (L := L)
  have h1 := two_hh_le_one (L := L)
  have h2 := two_hh_le_TL (L := L)
  set A : Set ℝ := {t | w t = w' t} with hA
  have hcl : IsClosed A := isClosed_eq hw.1 hw'.1
  have hop : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hab : t - hh L ≤ t + hh L := by linarith
    have hl : t + hh L ≤ t - hh L + TL L := by linarith
    obtain ⟨u, hu⟩ := hw.2 _ _ hab hl
    obtain ⟨u', hu'⟩ := hw'.2 _ _ hab hl
    have e := (hu.unique (by linarith) (by linarith) hu' ⟨by linarith, by linarith⟩ ht).2
    exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith : t - hh L < t)
      (by linarith : t < t + hh L)) fun s hs => e s ⟨hs.1.le, hs.2.le⟩
  rcases isClopen_iff.1 ⟨hcl, hop⟩ with h | h
  · have : t₀ ∈ A := h0
    rw [h] at this
    exact absurd this (Set.notMem_empty _)
  · funext t
    have : t ∈ A := by rw [h]; trivial
    exact this

#print axioms flow_unique

/-! ## 2. Construction by restarting -/

/-- Forward data at the times `t₀ + n h`. -/
def fwdSeq (C : ℝ → HL L → ℝ → HL L) (h t₀ : ℝ) (g : HL L) : ℕ → HL L
  | 0 => g
  | n + 1 => C (t₀ + (n : ℝ) * h) (fwdSeq C h t₀ g n) (t₀ + (n : ℝ) * h + h)

/-- Backward data at the times `t₀ − n h`. -/
def bwdSeq (Cb : ℝ → HL L → ℝ → HL L) (h t₀ : ℝ) (g : HL L) : ℕ → HL L
  | 0 => g
  | n + 1 => Cb (t₀ - ((n : ℝ) + 1) * h) (bwdSeq Cb h t₀ g n) (t₀ - ((n : ℝ) + 1) * h)

/-- Data at the times `t₀ + k h`, `k ∈ ℤ`. -/
def dataZ (C Cb : ℝ → HL L → ℝ → HL L) (h t₀ : ℝ) (g : HL L) (k : ℤ) : HL L :=
  if 0 ≤ k then fwdSeq C h t₀ g k.toNat else bwdSeq Cb h t₀ g (-k).toNat

/-- The glued curve. -/
def glob (C Cb : ℝ → HL L → ℝ → HL L) (h t₀ : ℝ) (g : HL L) (t : ℝ) : HL L :=
  C (t₀ + (⌊(t - t₀) / h⌋ : ℝ) * h) (dataZ C Cb h t₀ g ⌊(t - t₀) / h⌋) t

lemma floor_eq_of_mem {h t₀ t : ℝ} (hh0 : 0 < h) {k : ℤ} (h1 : t₀ + k * h ≤ t)
    (h2 : t < t₀ + k * h + h) : ⌊(t - t₀) / h⌋ = k := by
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hh0]; linarith
  · rw [div_lt_iff₀ hh0]; linarith

lemma floor_mem (h t₀ t : ℝ) (hh0 : 0 < h) :
    t₀ + (⌊(t - t₀) / h⌋ : ℝ) * h ≤ t ∧ t < t₀ + (⌊(t - t₀) / h⌋ : ℝ) * h + h := by
  have a1 := Int.floor_le ((t - t₀) / h)
  have a2 := Int.lt_floor_add_one ((t - t₀) / h)
  rw [le_div_iff₀ hh0] at a1
  rw [div_lt_iff₀ hh0] at a2
  constructor <;> nlinarith

/-- **Existence with conserved norm** (`κ ≥ 0`), for data `g` at any time `t₀`. -/
theorem flow_exists {κ : ℝ} (hκ : 0 ≤ κ) (t₀ : ℝ) (g : HL L) :
    ∃ w : ℝ → HL L, IsFlow κ w ∧ w t₀ = g ∧ ∀ t, ‖w t‖ = ‖g‖ := by
  set h := hh L with hhdef
  have hpos : 0 < h := hh_pos
  have h1 : 2 * h ≤ 1 := two_hh_le_one
  have h2 : 2 * h ≤ TL L := two_hh_le_TL
  have hp : ∀ s : ℝ, s ≤ s + h := fun s => by linarith
  have hl : ∀ s : ℝ, s + h ≤ s + TL L := fun s => by linarith
  have E : ∀ (s : ℝ) (g' : HL L), ∃ (u : Lp ℂ 4 (μJ (L := L) s (s + h))) (c : ℝ → HL L),
      Sol (hp s) (hl s) (cNLS κ) u c ∧ c s = g' ∧ ∀ t ∈ Set.Icc s (s + h), ‖c t‖ = ‖g'‖ :=
    fun s g' => exists_sol hκ (hp s) (hl s) ⟨le_rfl, hp s⟩ g'
  have Eb : ∀ (s : ℝ) (g' : HL L), ∃ (u : Lp ℂ 4 (μJ (L := L) s (s + h))) (c : ℝ → HL L),
      Sol (hp s) (hl s) (cNLS κ) u c ∧ c (s + h) = g' ∧ ∀ t ∈ Set.Icc s (s + h), ‖c t‖ = ‖g'‖ :=
    fun s g' => exists_sol hκ (hp s) (hl s) ⟨hp s, le_rfl⟩ g'
  choose U C hS hC0 hCm using E
  choose Ub Cb hSb hCb0 hCbm using Eb
  set D := dataZ C Cb h t₀ g with hD
  set w := glob C Cb h t₀ g with hw
  -- the data
  have hD0 : D 0 = g := by simp [hD, dataZ, fwdSeq]
  have hDnat : ∀ n : ℕ, D n = fwdSeq C h t₀ g n := fun n => by
    simp only [hD, dataZ, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]
  have hDneg : ∀ n : ℕ, D (-((n : ℤ) + 1)) = bwdSeq Cb h t₀ g (n + 1) := fun n => by
    simp only [hD, dataZ, show ¬ (0 ≤ -((n : ℤ) + 1)) by omega, ↓reduceIte]
    congr 1
  have hDneg' : ∀ n : ℕ, D (-(n : ℤ)) = bwdSeq Cb h t₀ g n := fun n => by
    cases n with
    | zero => simp [hD, dataZ, fwdSeq, bwdSeq]
    | succ n =>
      have := hDneg n
      rw [show -((n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) by push_cast; ring]
      exact this
  -- junctions
  have hJ : ∀ k : ℤ, C (t₀ + (k : ℝ) * h) (D k) (t₀ + (k : ℝ) * h + h) = D (k + 1) := by
    intro k
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [hDnat n, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, hDnat (n + 1),
        fwdSeq]
      push_cast
      rfl
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
      subst hn
      rw [hDneg n, show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, hDneg' n]
      set s := t₀ + ((-((n : ℤ) + 1) : ℤ) : ℝ) * h with hs
      have hs' : s = t₀ - ((n : ℝ) + 1) * h := by rw [hs]; push_cast; ring
      have hb : bwdSeq Cb h t₀ g (n + 1) = Cb s (bwdSeq Cb h t₀ g n) s := by
        rw [bwdSeq, hs']
      have hu := (hS s (bwdSeq Cb h t₀ g (n + 1))).unique (by linarith) (by linarith)
        (hSb s (bwdSeq Cb h t₀ g n)) ⟨le_rfl, hp s⟩
        (by rw [hC0, ← hb])
      rw [hu.2 (s + h) ⟨hp s, le_rfl⟩, hCb0]
  -- mass of the data
  have hDm : ∀ k : ℤ, ‖D k‖ = ‖g‖ := by
    have hf : ∀ n : ℕ, ‖fwdSeq C h t₀ g n‖ = ‖g‖ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [fwdSeq, hCm _ _ _ ⟨hp _, le_rfl⟩, ih]
    have hb : ∀ n : ℕ, ‖bwdSeq Cb h t₀ g n‖ = ‖g‖ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [bwdSeq, hCbm _ _ _ ⟨le_rfl, hp _⟩, ih]
    intro k
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [hDnat]; exact hf n
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
      subst hn
      rw [hDneg]; exact hb _
  -- the glued curve on each piece
  have hwk : ∀ k : ℤ, ∀ t ∈ Set.Icc (t₀ + (k : ℝ) * h) (t₀ + (k : ℝ) * h + h),
      C (t₀ + (k : ℝ) * h) (D k) t = w t := by
    intro k t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · rw [hw, glob, floor_eq_of_mem hpos ht.1 hlt]
    · have hk1 : ⌊(t - t₀) / h⌋ = k + 1 := by
        refine floor_eq_of_mem hpos ?_ ?_ <;> push_cast <;> linarith
      rw [hw, glob, hk1, heq, hJ k]
      have e : t₀ + (((k + 1 : ℤ)) : ℝ) * h = t₀ + (k : ℝ) * h + h := by push_cast; ring
      rw [e, hC0]
  have hP : ∀ k : ℤ, Sol (hp (t₀ + (k : ℝ) * h)) (hl _) (cNLS κ) (U (t₀ + (k : ℝ) * h) (D k)) w :=
    fun k => (hS _ _).congr (hwk k)
  -- continuity
  have hPc : ∀ k : ℤ, ContinuousOn w (Set.Icc (t₀ + (k : ℝ) * h) (t₀ + (k : ℝ) * h + h)) := by
    intro k
    obtain ⟨-, hDw⟩ := (hP k).base (b := t₀ + (k : ℝ) * h) ⟨le_rfl, hp _⟩
    exact (continuous_Dcurve _ _ _ _ _ _).continuousOn.congr fun t ht => (hDw t ht).symm
  have hcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨a1, a2⟩ := floor_mem h t₀ t hpos
    set m := ⌊(t - t₀) / h⌋
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · rcases a1.lt_or_eq with hlt | heq
      · exact ((hPc m).continuousWithinAt ⟨a1, a2.le⟩).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset (Icc_mem_nhdsLE hlt) (Set.Icc_subset_Icc le_rfl a2.le))
      · have e : t₀ + (((m - 1 : ℤ)) : ℝ) * h + h = t := by push_cast; linarith
        have hm1 := hPc (m - 1)
        rw [e] at hm1
        have hlt : t₀ + (((m - 1 : ℤ)) : ℝ) * h < t := by linarith
        exact (hm1.continuousWithinAt ⟨hlt.le, le_rfl⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE hlt)
    · exact ((hPc m).continuousWithinAt ⟨a1, a2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE a2) (Set.Icc_subset_Icc a1 le_rfl))
  -- short intervals
  have hshort : ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), β - α ≤ h →
      ∃ u : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u w := by
    intro α β hαβ hlen hβh
    obtain ⟨a1, a2⟩ := floor_mem h t₀ α hpos
    set m := ⌊(α - t₀) / h⌋
    set s := t₀ + (m : ℝ) * h
    by_cases hβ : β ≤ s + h
    · exact ⟨_, sol_restr (hP m) a1 hβ hαβ hlen⟩
    · push Not at hβ
      have e : t₀ + (((m + 1 : ℤ)) : ℝ) * h = s + h := by push_cast; ring
      obtain ⟨u₂, hu₂⟩ := sol_cast e (by rw [e]) (hp (s + h)) (hl (s + h)) (hP (m + 1))
      have hu₁ := sol_restr (hP m) a1 le_rfl a2.le (by linarith)
      have hu₂' := sol_restr hu₂ le_rfl (by linarith : β ≤ s + h + h) hβ.le (by linarith)
      exact ⟨_, sol_glue a2.le hβ.le hαβ hlen (by linarith) (by linarith) hu₁ hu₂'⟩
  have hflow : IsFlow κ w := by
    refine ⟨hcont, fun α β hαβ hlen => ?_⟩
    have hind : ∀ n : ℕ, ∀ β' (h1' : α ≤ β') (h2' : β' ≤ β), β' - α ≤ n * h →
        ∃ u : Lp ℂ 4 (μJ (L := L) α β'), Sol h1' (h2'.trans hlen) (cNLS κ) u w := by
      intro n
      induction n with
      | zero =>
        intro β' h1' h2' hn
        simp only [CharP.cast_eq_zero, zero_mul] at hn
        exact hshort α β' h1' _ (by linarith)
      | succ n ih =>
        intro β' h1' h2' hn
        set γ := max α (β' - h) with hγ
        have hγ1 : α ≤ γ := le_max_left _ _
        have hγ2 : γ ≤ β' := max_le h1' (by linarith)
        have hγn : γ - α ≤ n * h := by
          rcases le_total α (β' - h) with hh' | hh'
          · rw [hγ, max_eq_right hh']; push_cast at hn; linarith
          · rw [hγ, max_eq_left hh', sub_self]; positivity
        obtain ⟨u₁, hu₁⟩ := ih γ hγ1 (hγ2.trans h2') hγn
        obtain ⟨u₂, hu₂⟩ := hshort γ β' hγ2 (by linarith [h2'.trans hlen])
          (by rw [hγ]; linarith [le_max_right α (β' - h)])
        exact ⟨_, sol_glue hγ1 hγ2 h1' (h2'.trans hlen) (hγ2.trans (h2'.trans hlen))
          (by linarith [h2'.trans hlen]) hu₁ hu₂⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ((β - α) / h)
    exact hind n β hαβ le_rfl (by have := (div_lt_iff₀ hpos).1 hn; linarith)
  refine ⟨w, hflow, ?_, fun t => ?_⟩
  · have hm : ⌊(t₀ - t₀) / h⌋ = 0 := by simp
    rw [hw, glob, hm, Int.cast_zero, zero_mul, add_zero,
      show dataZ C Cb h t₀ g 0 = g from hD0, hC0]
  · obtain ⟨a1, a2⟩ := floor_mem h t₀ t hpos
    rw [← hwk _ t ⟨a1, a2.le⟩, hCm _ _ t ⟨a1, a2.le⟩, hDm]

#print axioms flow_exists

/-! ## 3. The flow map -/

section Main

variable {κ : ℝ} (hκ : 0 ≤ κ)

/-- `S_t f`: the global solution with `u(0) = f`, at time `t`. -/
def flowMap (f : HL L) : ℝ → HL L := Classical.choose (flow_exists (L := L) hκ 0 f)

lemma flowMap_spec (f : HL L) :
    IsFlow κ (flowMap hκ f) ∧ flowMap hκ f 0 = f ∧ ∀ t, ‖flowMap hκ f t‖ = ‖f‖ :=
  Classical.choose_spec (flow_exists (L := L) hκ 0 f)

lemma flowMap_unique (f : HL L) {w : ℝ → HL L} (hw : IsFlow κ w) (h0 : w 0 = f) :
    w = flowMap hκ f :=
  flow_unique hw (flowMap_spec hκ f).1 (h0.trans (flowMap_spec hκ f).2.1.symm)

/-- **Autonomy**: time translates of solutions are solutions. -/
lemma isFlow_shift {w : ℝ → HL L} (hw : IsFlow κ w) (s : ℝ) : IsFlow κ (fun t => w (t + s)) := by
  refine ⟨hw.1.comp (continuous_id.add continuous_const), fun α β hαβ hlen => ?_⟩
  obtain ⟨u, hu⟩ := hw.2 (α + s) (β + s) (by linarith) (by linarith)
  exact sol_cast (by ring) (by ring) hαβ hlen (sol_tr hu s)

/-- **Flow law** `S_s ∘ S_t = S_{s+t}`. -/
theorem flowMap_comp (f : HL L) (s t : ℝ) :
    flowMap hκ (flowMap hκ f t) s = flowMap hκ f (s + t) := by
  have e := flowMap_unique hκ (flowMap hκ f t) (isFlow_shift (flowMap_spec hκ f).1 t)
    (by rw [zero_add])
  exact (congrFun e s).symm

theorem flowMap_neg_left (f : HL L) (t : ℝ) : flowMap hκ (flowMap hκ f t) (-t) = f := by
  rw [flowMap_comp, neg_add_cancel, (flowMap_spec hκ f).2.1]

theorem flowMap_neg_right (f : HL L) (t : ℝ) : flowMap hκ (flowMap hκ f (-t)) t = f := by
  rw [flowMap_comp, add_neg_cancel, (flowMap_spec hκ f).2.1]

/-- **Agreement with the `H¹` flow of F04:thm-global.** -/
theorem flowMap_H1 (g : QuantumNLS.Sobolev.h04 L 1) (t : ℝ) :
    flowMap hκ (emb g) t =
      emb (QuantumNLS.LocalWellPosednessFull.umax (le_refl (1 : ℝ)) κ g t) := by
  set v := QuantumNLS.LocalWellPosednessFull.umax (le_refl (1 : ℝ)) κ g
  have hv : Continuous v := (QuantumNLS.F04Global.thm_global (L := L) hκ g).2.1
  have hflow : IsFlow κ (fun t => emb (v t)) := by
    refine ⟨emb.continuous.comp hv, fun α β hαβ hlen => ?_⟩
    obtain ⟨U, hU, hUw, -⟩ := bridge_gen hαβ hlen hv α (umax_duhamel hκ g α) ⟨le_rfl, hαβ⟩
    exact ⟨U, α, ⟨le_rfl, hαβ⟩, hU, hUw⟩
  have h0 : (fun t => emb (v t)) 0 = emb g := by
    show emb (v 0) = emb g
    rw [show v 0 = g from (QuantumNLS.F04Global.thm_global (L := L) hκ g).1.at_zero]
  exact (congrFun (flowMap_unique hκ (emb g) hflow h0) t).symm

/-- One short step of the `C_tL²` Lipschitz bound. -/
lemma step_lip (R : ℝ) (hR : 0 ≤ R) :
    ∃ τ K₁ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ ≤ TL L ∧ 1 ≤ K₁ ∧
      ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R → ∀ s t : ℝ, |t - s| ≤ τ →
        ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K₁ * ‖flowMap hκ f s - flowMap hκ g s‖ := by
  obtain ⟨τ, B, A, hτ, hτ1, hτL, hB, hA, H⟩ := ext003_local_input (L := L) κ R hR
  have hC := CL_nonneg (L := L)
  refine ⟨τ, 1 + 6 * |κ| * CL L * B ^ 2 * A, hτ, hτ1, hτL, by
    have : 0 ≤ 6 * |κ| * CL L * B ^ 2 * A := by positivity
    linarith, fun f g hf hg s t hst => ?_⟩
  set Wf := flowMap hκ f
  set Wg := flowMap hκ g
  have hWf := flowMap_spec hκ f
  have hWg := flowMap_spec hκ g
  by_cases hts : t = s
  · subst hts
    have : 0 ≤ 6 * |κ| * CL L * B ^ 2 * A := by positivity
    nlinarith [norm_nonneg (Wf t - Wg t)]
  set α := min s t
  set β := max s t
  have hαβ : α ≤ β := min_le_max
  have hlt : α < β := by
    rcases lt_or_gt_of_ne hts with h | h
    · simp only [α, β, min_eq_right h.le, max_eq_left h.le]; exact h
    · simp only [α, β, min_eq_left h.le, max_eq_right h.le]; exact h
  have hβα : β - α ≤ τ := by
    have : β - α = |t - s| := by
      rcases le_total s t with h | h
      · simp only [α, β, min_eq_left h, max_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      · simp only [α, β, min_eq_right h, max_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
    rw [this]; exact hst
  have hlen : β ≤ α + TL L := by linarith
  have hs : s ∈ Set.Icc α β := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht : t ∈ Set.Icc α β := ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨c1, -, -, c4, -⟩ := H α β hαβ hlen hlt (by linarith) s
  obtain ⟨uf, huf⟩ := hWf.1.2 α β hαβ hlen
  obtain ⟨ug, hug⟩ := hWg.1.2 α β hαβ hlen
  obtain ⟨hDf, hwf⟩ := huf.base hs
  obtain ⟨hDg, hwg⟩ := hug.base hs
  have hRf : ‖Wf s‖ ≤ R := by rw [hWf.2.2 s]; exact hf
  have hRg : ‖Wg s‖ ≤ R := by rw [hWg.2.2 s]; exact hg
  obtain ⟨uf', hbf, hDf'⟩ := c1 _ hRf
  obtain ⟨ug', hbg, hDg'⟩ := c1 _ hRg
  have e1 := duhamel_unique hαβ hlen (by linarith) hlt _ s hs _ hDf hDf'
  have e2 := duhamel_unique hαβ hlen (by linarith) hlt _ s hs _ hDg hDg'
  subst e1; subst e2
  have := c4 _ _ uf ug hRf hRg hbf hbg hDf hDg t
  rw [hwf t ht, hwg t ht] at this
  exact this

/-- **Lipschitz dependence in `C_tL²`** on bounded `L²` balls over `[−T, T]`. -/
theorem flow_lipschitz (R T : ℝ) (hR : 0 ≤ R) (_hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R → ∀ t ∈ Set.Icc (-T) T,
      ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K * ‖f - g‖ := by
  obtain ⟨τ, K₁, hτ, -, -, hK₁, H⟩ := step_lip (L := L) hκ R hR
  obtain ⟨N, hN⟩ := exists_nat_gt (T / τ)
  have hNτ : T ≤ N * τ := by have := (div_lt_iff₀ hτ).1 hN; linarith
  refine ⟨K₁ ^ N, by positivity, fun f g hf hg t ht => ?_⟩
  have h0 : flowMap hκ f 0 - flowMap hκ g 0 = f - g := by
    rw [(flowMap_spec hκ f).2.1, (flowMap_spec hκ g).2.1]
  have hfwd : ∀ n : ℕ, ∀ t, 0 ≤ t → t ≤ n * τ →
      ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K₁ ^ n * ‖f - g‖ := by
    intro n
    induction n with
    | zero =>
      intro t h1 h2
      simp only [CharP.cast_eq_zero, zero_mul] at h2
      have : t = 0 := le_antisymm h2 h1
      rw [this, h0, pow_zero, one_mul]
    | succ n ih =>
      intro t h1 h2
      by_cases htn : t ≤ n * τ
      · calc _ ≤ K₁ ^ n * ‖f - g‖ := ih t h1 htn
          _ ≤ K₁ ^ (n + 1) * ‖f - g‖ := by
            gcongr; first | exact hK₁ | exact Nat.le_succ n
      · push Not at htn
        have hs := ih (n * τ) (by positivity) le_rfl
        have hst : |t - n * τ| ≤ τ := by
          rw [abs_of_nonneg (by linarith)]; push_cast at h2; linarith
        calc _ ≤ K₁ * ‖flowMap hκ f (n * τ) - flowMap hκ g (n * τ)‖ := H f g hf hg _ t hst
          _ ≤ K₁ * (K₁ ^ n * ‖f - g‖) := by gcongr
          _ = K₁ ^ (n + 1) * ‖f - g‖ := by ring
  have hbwd : ∀ n : ℕ, ∀ t, t ≤ 0 → -(n * τ) ≤ t →
      ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K₁ ^ n * ‖f - g‖ := by
    intro n
    induction n with
    | zero =>
      intro t h1 h2
      simp only [CharP.cast_eq_zero, zero_mul, neg_zero] at h2
      have : t = 0 := le_antisymm h1 h2
      rw [this, h0, pow_zero, one_mul]
    | succ n ih =>
      intro t h1 h2
      by_cases htn : -(n * τ) ≤ t
      · calc _ ≤ K₁ ^ n * ‖f - g‖ := ih t h1 htn
          _ ≤ K₁ ^ (n + 1) * ‖f - g‖ := by
            gcongr; first | exact hK₁ | exact Nat.le_succ n
      · push Not at htn
        have hs := ih (-(n * τ)) (by have : 0 ≤ (n : ℝ) * τ := by positivity
                                     linarith) le_rfl
        have hst : |t - -(n * τ)| ≤ τ := by
          rw [abs_of_nonpos (by linarith)]; push_cast at h2; linarith
        calc _ ≤ K₁ * ‖flowMap hκ f (-(n * τ)) - flowMap hκ g (-(n * τ))‖ := H f g hf hg _ t hst
          _ ≤ K₁ * (K₁ ^ n * ‖f - g‖) := by gcongr
          _ = K₁ ^ (n + 1) * ‖f - g‖ := by ring
  rcases le_total 0 t with h | h
  · exact hfwd N t h (ht.2.trans hNτ)
  · exact hbwd N t h (by linarith [ht.1])

/-- **Lipschitz dependence in `L⁴_{t,x}`**: on every time interval `J ⊆ [−T, T]` of length `≤ T_L`,
the `L⁴(J × 𝕋_L)` classes of the solutions satisfy `‖u_f − u_g‖ ≤ K ‖f − g‖₂` (`[−T, T]` is a
finite union of such intervals). -/
theorem flow_lipschitz_L4 (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), -T ≤ α → β ≤ T →
        ∀ u v : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u (flowMap hκ f) →
          Sol hαβ hlen (cNLS κ) v (flowMap hκ g) → ‖u - v‖ ≤ K * ‖f - g‖ := by
  obtain ⟨K₀, hK₀, HK⟩ := flow_lipschitz (L := L) hκ R T hR hT
  obtain ⟨τ, B, A, hτ, hτ1, hτL, hB, hA, H⟩ := ext003_local_input (L := L) κ R hR
  obtain ⟨N, hN⟩ := exists_nat_gt (TL L / τ)
  have hNτ : TL L ≤ N * τ := by have := (div_lt_iff₀ hτ).1 hN; linarith
  refine ⟨N * (A * K₀), by positivity, fun f g hf hg α β hαβ hlen hTα hβT u v hu hv => ?_⟩
  -- one piece
  have hpiece : ∀ c d (hc : α ≤ c) (hcd : c ≤ d) (hd : d ≤ β), d - c ≤ τ →
      ‖ind c d (u - v)‖ ≤ A * K₀ * ‖f - g‖ := by
    intro c d hc hcd hd hdc
    rcases hcd.lt_or_eq with hlt | heq
    · have hlen' : d ≤ c + TL L := by linarith
      have hu' := sol_restr hu hc hd hcd hlen'
      have hv' := sol_restr hv hc hd hcd hlen'
      obtain ⟨hDu, -⟩ := hu'.base (b := c) ⟨le_rfl, hcd⟩
      obtain ⟨hDv, -⟩ := hv'.base (b := c) ⟨le_rfl, hcd⟩
      obtain ⟨c1, -, c3, -, -⟩ := H c d hcd hlen' hlt (by linarith) c
      have hRf : ‖flowMap hκ f c‖ ≤ R := by rw [(flowMap_spec hκ f).2.2]; exact hf
      have hRg : ‖flowMap hκ g c‖ ≤ R := by rw [(flowMap_spec hκ g).2.2]; exact hg
      obtain ⟨u', hbu, hDu'⟩ := c1 _ hRf
      obtain ⟨v', hbv, hDv'⟩ := c1 _ hRg
      have e1 := duhamel_unique hcd hlen' (by linarith) hlt _ c ⟨le_rfl, hcd⟩ _ hDu hDu'
      have e2 := duhamel_unique hcd hlen' (by linarith) hlt _ c ⟨le_rfl, hcd⟩ _ hDv hDv'
      rw [← norm_restr hc hd, restr_sub, e1, e2]
      refine (c3 _ _ u' v' hRf hRg hbu hbv hDu' hDv').trans ?_
      rw [mul_assoc]
      gcongr
      exact HK f g hf hg c ⟨by linarith, by linarith⟩
    · subst heq
      rw [norm_ind_empty]
      positivity
  have hind : ∀ n : ℕ, ∀ β' (h1 : α ≤ β') (h2 : β' ≤ β), β' - α ≤ n * τ →
      ‖ind α β' (u - v)‖ ≤ n * (A * K₀ * ‖f - g‖) := by
    intro n
    induction n with
    | zero =>
      intro β' h1 h2 hn
      simp only [CharP.cast_eq_zero, zero_mul] at hn
      have : β' = α := by linarith
      rw [this, norm_ind_empty]; simp
    | succ n ih =>
      intro β' h1 h2 hn
      set γ := max α (β' - τ) with hγ
      have hγ1 : α ≤ γ := le_max_left _ _
      have hγ2 : γ ≤ β' := max_le h1 (by linarith)
      have hγn : γ - α ≤ n * τ := by
        rcases le_total α (β' - τ) with hh' | hh'
        · rw [hγ, max_eq_right hh']; push_cast at hn; linarith
        · rw [hγ, max_eq_left hh', sub_self]; positivity
      rw [ind_split hγ1 hγ2]
      calc ‖ind α γ (u - v) + ind γ β' (u - v)‖ ≤ ‖ind α γ (u - v)‖ + ‖ind γ β' (u - v)‖ :=
            norm_add_le _ _
        _ ≤ n * (A * K₀ * ‖f - g‖) + A * K₀ * ‖f - g‖ :=
            add_le_add (ih γ hγ1 (hγ2.trans h2) hγn)
              (hpiece γ β' hγ1 hγ2 h2 (by rw [hγ]; linarith [le_max_right α (β' - τ)]))
        _ = ((n + 1 : ℕ) : ℝ) * (A * K₀ * ‖f - g‖) := by push_cast; ring
  have := hind N β hαβ le_rfl (by linarith)
  rw [ind_self] at this
  calc ‖u - v‖ ≤ N * (A * K₀ * ‖f - g‖) := this
    _ = N * (A * K₀) * ‖f - g‖ := by ring

/-- Each time map is continuous. -/
lemma continuous_flowMap (t : ℝ) : Continuous fun f : HL L => flowMap hκ f t := by
  rw [Metric.continuous_iff]
  intro f₀ ε hε
  obtain ⟨K, hK, HK⟩ := flow_lipschitz (L := L) hκ (‖f₀‖ + 1) |t| (by positivity) (abs_nonneg t)
  refine ⟨min 1 (ε / (K + 1)), by positivity, fun f hf => ?_⟩
  rw [dist_eq_norm] at hf ⊢
  have h1 : ‖f - f₀‖ < 1 := lt_of_lt_of_le hf (min_le_left _ _)
  have h2 : ‖f - f₀‖ < ε / (K + 1) := lt_of_lt_of_le hf (min_le_right _ _)
  have hfR : ‖f‖ ≤ ‖f₀‖ + 1 := by
    have := norm_le_insert' f f₀; linarith [norm_sub_rev f f₀]
  have := HK f f₀ hfR (by linarith) t ⟨neg_abs_le t, le_abs_self t⟩
  calc ‖flowMap hκ f t - flowMap hκ f₀ t‖ ≤ K * ‖f - f₀‖ := this
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Each time map is a homeomorphism with inverse the map at the negative time.** -/
def timeHomeomorph (t : ℝ) : HL L ≃ₜ HL L where
  toFun f := flowMap hκ f t
  invFun f := flowMap hκ f (-t)
  left_inv f := flowMap_neg_left hκ f t
  right_inv f := flowMap_neg_right hκ f t
  continuous_toFun := continuous_flowMap hκ t
  continuous_invFun := continuous_flowMap hκ (-t)

/-- **R-AEE17FD6, `thm:root-L2-flow`, first paragraph** (the flow; `κ ≥ 0`). For every
`f ∈ L²(𝕋_L)`: the global Duhamel solution of `i∂_t u = −∂_x²u + 2κ|u|²u`, `u(0) = f`, exists in
`C(ℝ;L²) ∩ L⁴_loc` and is unique there; it preserves the `L²` norm; it agrees with the `H¹` flow of
F04:thm-global; it depends Lipschitz continuously on the datum on each bounded `L²` ball over each
finite time interval in `C_tL²_x` and in `L⁴_{t,x}`; each time map is a homeomorphism with inverse
the map at the negative time. -/
theorem thm_root_L2_flow :
    (∀ f : HL L, IsFlow κ (flowMap hκ f) ∧ flowMap hκ f 0 = f) ∧
    (∀ f : HL L, ∀ w : ℝ → HL L, IsFlow κ w → w 0 = f → w = flowMap hκ f) ∧
    (∀ f : HL L, ∀ t, ‖flowMap hκ f t‖ = ‖f‖) ∧
    (∀ (g : QuantumNLS.Sobolev.h04 L 1) (t : ℝ), flowMap hκ (emb g) t =
      emb (QuantumNLS.LocalWellPosednessFull.umax (le_refl (1 : ℝ)) κ g t)) ∧
    (∀ R T : ℝ, 0 ≤ R → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ t ∈ Set.Icc (-T) T, ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K * ‖f - g‖) ∧
    (∀ R T : ℝ, 0 ≤ R → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), -T ≤ α → β ≤ T →
        ∀ u v : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u (flowMap hκ f) →
          Sol hαβ hlen (cNLS κ) v (flowMap hκ g) → ‖u - v‖ ≤ K * ‖f - g‖) ∧
    (∀ s t : ℝ, ∀ f : HL L, flowMap hκ (flowMap hκ f t) s = flowMap hκ f (s + t)) ∧
    (∀ t : ℝ, ∃ e : HL L ≃ₜ HL L, (∀ f, e f = flowMap hκ f t) ∧ ∀ f, e.symm f = flowMap hκ f (-t)) :=
  ⟨fun f => ⟨(flowMap_spec hκ f).1, (flowMap_spec hκ f).2.1⟩,
    fun f _ hw h0 => flowMap_unique hκ f hw h0,
    fun f t => (flowMap_spec hκ f).2.2 t,
    fun g t => flowMap_H1 hκ g t,
    fun R T hR hT => flow_lipschitz hκ R T hR hT,
    fun R T hR hT => flow_lipschitz_L4 hκ R T hR hT,
    fun s t f => flowMap_comp hκ f s t,
    fun t => ⟨timeHomeomorph hκ t, fun _ => rfl, fun _ => rfl⟩⟩

end Main

#print axioms thm_root_L2_flow

end QuantumNLS.L2Flow
