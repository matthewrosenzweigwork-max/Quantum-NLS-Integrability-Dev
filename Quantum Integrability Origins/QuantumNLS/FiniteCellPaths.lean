import QuantumNLS.FiniteCellPartition
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Chain

/-! R-D8BB052C group C: the first cell vertex and deterministic monotone steps.
The fixed order is the increasing integer order on the selected finite set. -/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace QuantumNLS.FiniteCellPaths
open Occupation OccupationHilbert FiniteCellPartition
variable {N : ℕ}

def selectedList (I : Finset ℤ) (m : Arr N) : List ℕ := (I.sort (· ≤ ·)).map (fun c => m.1 c)

theorem selectedList_injective (I : Finset ℤ) (K ell : ℕ) (m : Arr N) :
    Function.Injective (fun n : Vertices I K ell m => selectedList I n.1) := by
  intro n p h
  apply selected_counts_injective I K ell m
  funext c
  have hh := List.map_inj_left.mp h
  exact hh c (by simp)

/-- Lexicographic order on the actual finite selected count vectors. -/
@[instance_reducible]
def vertexOrder (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : LinearOrder (Vertices I K ell m) :=
  LinearOrder.lift' (fun n : Vertices I K ell m => selectedList I n.1) (selectedList_injective I K ell m)

/-- The root is the first actual cell vertex, chosen before any vector or target. -/
def root (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : Vertices I K ell m := by
  let _ := verticesFintype I K ell m
  let _ := vertexOrder I K ell m
  exact Finset.univ.min' ⟨⟨m, cell_mem I K ell m⟩, Finset.mem_univ _⟩

theorem root_le (I : Finset ℤ) (K ell : ℕ) (m : Arr N) (n : Vertices I K ell m) :
    selectedList I (root I K ell m).1 ≤ selectedList I n.1 := by
  let _ := verticesFintype I K ell m
  let _ := vertexOrder I K ell m
  exact Finset.min'_le Finset.univ n (Finset.mem_univ n)

/-- Equal complete totals rule out pointwise domination unless arrays coincide. -/
theorem array_eq_of_le {m n : Arr N} (hle : m.1 ≤ n.1) : m = n := by
  have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add] at he
  have ht : m.1.degree = n.1.degree := m.2.trans n.2.symm
  have hz : (n.1 - m.1).degree = 0 := by omega
  have hzero : n.1 - m.1 = 0 := (Finsupp.degree_eq_zero_iff _).mp hz
  exact Subtype.ext (le_antisymm hle (tsub_eq_zero_iff_le.mp hzero))

/-- Until the root, both a surplus and a deficit selected coordinate exist. -/
theorem above_below_exist (I : Finset ℤ) (K ell : ℕ) {m n : Arr N}
    (hc : SameCell I K ell m n) (hne : m ≠ n) :
    (∃ a ∈ I, n.1 a < m.1 a) ∧ (∃ b ∈ I, m.1 b < n.1 b) := by
  constructor
  · by_contra h
    push Not at h
    apply hne
    apply array_eq_of_le
    intro c
    by_cases hi : c ∈ I
    · exact h c hi
    · exact (hc.1 c hi).le
  · by_contra h
    push Not at h
    apply hne
    symm
    apply array_eq_of_le
    intro c
    by_cases hi : c ∈ I
    · exact h c hi
    · exact (hc.1 c hi).symm.le

/-- An active count stays in the same quotient block when moved towards a cell mate. -/
theorem div_eq_between {ell lo hi x : ℕ} (hlh : lo / ell = hi / ell)
    (hlo : lo ≤ x) (hhi : x ≤ hi) : x / ell = lo / ell := by
  exact le_antisymm (hlh ▸ Nat.div_le_div_right hhi) (Nat.div_le_div_right hlo)

/-- Any surplus-to-deficit step towards a cell mate stays in the exact cell. -/
theorem step_sameCell (I : Finset ℤ) (K ell : ℕ) {m n : Arr N}
    (hc : SameCell I K ell m n) {a b : ℤ} (ha : a ∈ I) (hb : b ∈ I)
    (habove : n.1 a < m.1 a) (hbelow : m.1 b < n.1 b) :
    SameCell I K ell m (shiftArr a b m (by unfold DonorOK; omega)) := by
  have hab : a ≠ b := by intro he; subst b; omega
  have haS : a ∈ active I K m := by
    by_contra h
    have he := hc.2.2.1 a ha h
    omega
  have hbS : b ∈ active I K m := by
    by_contra h
    have he := hc.2.2.1 b hb h
    omega
  have hnaS : a ∈ active I K n := hc.2.1 ▸ haS
  have hna : K ≤ n.1 a := (show a ∈ I ∧ K ≤ n.1 a from
    by simpa only [active, Finset.mem_filter] using hnaS).2
  have hmb : K ≤ m.1 b := (show b ∈ I ∧ K ≤ m.1 b from
    by simpa only [active, Finset.mem_filter] using hbS).2
  have hd : DonorOK a m.1 := by unfold DonorOK; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hi
    exact (shift_apply_exterior m.1 (by aesop) (by aesop)).symm
  · ext c
    simp only [active, Finset.mem_filter]
    by_cases hca : c = a
    · subst c
      rw [show (shiftArr a b m hd).1 a = m.1 a - 1 from shift_apply_donor m.1 hab]
      have hma : K ≤ m.1 a := (show a ∈ I ∧ K ≤ m.1 a from
        by simpa only [active, Finset.mem_filter] using haS).2
      simp only [ha, true_and]
      omega
    · by_cases hcb : c = b
      · subst c
        rw [show (shiftArr a b m hd).1 b = m.1 b + 1 from shift_apply_receiver m.1 hab]
        simp only [hb, true_and]
        omega
      · rw [show (shiftArr a b m hd).1 c = m.1 c from shift_apply_exterior m.1 hca hcb]
  · intro c hi hS
    exact (shift_apply_exterior m.1 (by aesop) (by aesop)).symm
  · intro c hS
    by_cases hca : c = a
    · subst c
      change m.1 a / ell = (shift a b m.1 a) / ell
      rw [shift_apply_donor m.1 hab]
      exact (div_eq_between (hc.2.2.2 a haS).symm (by omega) (by omega)).trans
        (hc.2.2.2 a haS).symm |>.symm
    · by_cases hcb : c = b
      · subst c
        change m.1 b / ell = (shift a b m.1 b) / ell
        rw [shift_apply_receiver m.1 hab]
        exact (div_eq_between (hc.2.2.2 b hbS) (by omega) (by omega)).symm
      · exact congrArg (fun x : ℕ => x / ell)
          (shift_apply_exterior m.1 hca hcb).symm

/-- First above/below coordinates in the fixed selected order. -/
def aboveSet (I : Finset ℤ) (m n : Arr N) := I.filter (fun a => n.1 a < m.1 a)
def belowSet (I : Finset ℤ) (m n : Arr N) := I.filter (fun b => m.1 b < n.1 b)

def firstAbove (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) : ℤ :=
  (aboveSet I m n).min' (by
    obtain ⟨a, ha, hlt⟩ := (above_below_exist I K ell hc hne).1
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hlt⟩⟩)

def firstBelow (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) : ℤ :=
  (belowSet I m n).min' (by
    obtain ⟨b, hb, hlt⟩ := (above_below_exist I K ell hc hne).2
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hlt⟩⟩)

theorem firstAbove_spec (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) :
    firstAbove I K ell m n hc hne ∈ I ∧ n.1 (firstAbove I K ell m n hc hne) <
      m.1 (firstAbove I K ell m n hc hne) :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

theorem firstBelow_spec (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) :
    firstBelow I K ell m n hc hne ∈ I ∧ m.1 (firstBelow I K ell m n hc hne) <
      n.1 (firstBelow I K ell m n hc hne) :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

/-- Canonical roots agree whenever complete arrays lie in the same cell. -/
theorem root_eq_of_sameCell (I : Finset ℤ) (K ell : ℕ) {m n : Arr N}
    (hc : SameCell I K ell m n) : (root I K ell m).1 = (root I K ell n).1 := by
  let rn : Vertices I K ell m := ⟨(root I K ell n).1,
    sameCell_trans I K ell hc (root I K ell n).2⟩
  let rm : Vertices I K ell n := ⟨(root I K ell m).1,
    sameCell_trans I K ell (sameCell_symm I K ell hc) (root I K ell m).2⟩
  have hh : selectedList I (root I K ell m).1 = selectedList I rn.1 :=
    le_antisymm (root_le I K ell m rn) (root_le I K ell n rm)
  exact congrArg Subtype.val (selectedList_injective I K ell m hh)

/-- Number of monotone surplus particles still to be moved. -/
def distance (I : Finset ℤ) (target m : Arr N) : ℕ := ∑ c ∈ I, (m.1 c - target.1 c)

theorem distance_zero_iff (I : Finset ℤ) (K ell : ℕ) {m n : Arr N}
    (hc : SameCell I K ell m n) : distance I n m = 0 ↔ m = n := by
  constructor
  · intro hzero
    apply array_eq_of_le
    intro c
    by_cases hi : c ∈ I
    · have hh := (Finset.sum_eq_zero_iff.mp (show (∑ c ∈ I, (m.1 c - n.1 c)) = 0 from hzero)) c hi
      exact Nat.le_of_sub_eq_zero hh
    · exact (hc.1 c hi).le
  · intro he
    subst n
    simp [distance]

/-- One legal step decreases the surplus measure by exactly one. -/
theorem distance_step (I : Finset ℤ) {m n : Arr N} {a b : ℤ}
    (ha : a ∈ I) (hb : b ∈ I) (habove : n.1 a < m.1 a) (hbelow : m.1 b < n.1 b) :
    distance I n (shiftArr a b m (by unfold DonorOK; omega)) + 1 = distance I n m := by
  have hab : a ≠ b := by intro he; subst b; omega
  have hh : ∀ c ∈ I, (shift a b m.1 c - n.1 c) + (if c = a then 1 else 0) = m.1 c - n.1 c := by
    intro c _
    by_cases hca : c = a
    · subst c
      rw [shift_apply_donor m.1 hab]
      rw [ite_eq_left (show a = a from rfl)]
      omega
    · by_cases hcb : c = b
      · subst c
        rw [shift_apply_receiver m.1 hab]
        simp only [ite_eq_right hca]
        omega
      · rw [shift_apply_exterior m.1 hca hcb, ite_eq_right hca, add_zero]
  have hs := Finset.sum_congr rfl hh
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left ha, distance, shiftArr] using hs

/-- Each coordinate surplus is bounded by one quotient block's length. -/
theorem surplus_lt_ell (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) {m n : Arr N}
    (hc : SameCell I K ell m n) (c : ℤ) (hi : c ∈ I) : m.1 c - n.1 c < ell := by
  by_cases hS : c ∈ active I K m
  · have hq := hc.2.2.2 c hS
    have hm := Nat.mod_add_div (m.1 c) ell
    have hn := Nat.mod_add_div (n.1 c) ell
    have hrm := Nat.mod_lt (m.1 c) hell
    have hrn := Nat.mod_lt (n.1 c) hell
    rw [hq] at hm
    omega
  · rw [hc.2.2.1 c hi hS, Nat.sub_self]
    exact hell

theorem distance_le (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) {m n : Arr N}
    (hc : SameCell I K ell m n) : distance I n m ≤ I.card * ell := by
  calc
    distance I n m ≤ ∑ _c ∈ I, ell :=
      Finset.sum_le_sum (fun c hi => (surplus_lt_ell I K ell hell hc c hi).le)
    _ = I.card * ell := by simp

/-- A step always chooses the least surplus and least deficit selected labels. -/
def next (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) : Arr N :=
  shiftArr (firstAbove I K ell m n hc hne) (firstBelow I K ell m n hc hne) m
    (by have h := (firstAbove_spec I K ell m n hc hne).2; unfold DonorOK; omega)

theorem next_sameCell (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) : SameCell I K ell (next I K ell m n hc hne) n := by
  have ha := firstAbove_spec I K ell m n hc hne
  have hb := firstBelow_spec I K ell m n hc hne
  exact sameCell_trans I K ell (sameCell_symm I K ell
    (step_sameCell I K ell hc ha.1 hb.1 ha.2 hb.2)) hc

theorem distance_next (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) :
    distance I n (next I K ell m n hc hne) + 1 = distance I n m := by
  exact distance_step I (firstAbove_spec I K ell m n hc hne).1
    (firstBelow_spec I K ell m n hc hne).1
    (firstAbove_spec I K ell m n hc hne).2 (firstBelow_spec I K ell m n hc hne).2

/-- The vertex list is computed with finite fuel, the actual surplus count. -/
def walk (I : Finset ℤ) (K ell : ℕ) :
    ℕ → (m n : Arr N) → SameCell I K ell m n → List (Arr N)
  | 0, m, _, _ => [m]
  | fuel + 1, m, n, hc =>
      if he : m = n then [m]
      else m :: walk I K ell fuel (next I K ell m n hc he) n (next_sameCell I K ell m n hc he)

/-- A path's consecutive vertices are actual first-above/first-below transfers. -/
def Step (I : Finset ℤ) (K ell : ℕ) (n : Arr N) (x y : Arr N) : Prop :=
  ∃ (hc : SameCell I K ell x n) (hne : x ≠ n), y = next I K ell x n hc hne

/-- Fuel at least the surplus measure guarantees that the list reaches the target. -/
theorem walk_last (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hf : distance I n m ≤ fuel) :
    (walk I K ell fuel m n hc).getLast? = some n := by
  induction fuel generalizing m with
  | zero =>
    have he := (distance_zero_iff I K ell hc).mp (by omega)
    simp [walk, he]
  | succ fuel ih =>
    rw [walk]
    split_ifs with he
    · simp [he]
    · have hd := distance_next I K ell m n hc he
      have hh := ih (next I K ell m n hc he) (next_sameCell I K ell m n hc he) (by omega)
      rw [List.getLast?_cons, hh]
      rfl

/-- Path length counts edges, and is no greater than the initial surplus measure. -/
theorem walk_length (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) :
    (walk I K ell fuel m n hc).length ≤ distance I n m + 1 := by
  induction fuel generalizing m with
  | zero => simp [walk]
  | succ fuel ih =>
    rw [walk]
    split_ifs with he
    · simp
    · have hd := distance_next I K ell m n hc he
      have hh := ih (next I K ell m n hc he) (next_sameCell I K ell m n hc he)
      simp only [List.length_cons]
      omega

/-- Canonical deterministic path on every complete occupation array. -/
def path (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : List (Arr N) :=
  walk I K ell (distance I (root I K ell m).1 m) m (root I K ell m).1 (root I K ell m).2

theorem path_last (I : Finset ℤ) (K ell : ℕ) (m : Arr N) :
    (path I K ell m).getLast? = some (root I K ell m).1 :=
  walk_last I K ell _ _ _ (root I K ell m).2 le_rfl

theorem path_length (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (m : Arr N) :
    (path I K ell m).length - 1 ≤ I.card * ell := by
  have hh := walk_length I K ell (distance I (root I K ell m).1 m) m _ (root I K ell m).2
  have hd := distance_le I K ell hell (root I K ell m).2
  change (walk I K ell _ m _ _).length - 1 ≤ _
  omega

theorem walk_head (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) : (walk I K ell fuel m n hc).head? = some m := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [walk]; split_ifs <;> rfl

theorem walk_nonempty (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) : walk I K ell fuel m n hc ≠ [] := by
  intro h
  have hh := walk_head I K ell fuel m n hc
  rw [h] at hh
  contradiction

/-- Every consecutive edge of the computed walk is its prescribed legal step. -/
theorem walk_chain (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) : (walk I K ell fuel m n hc).IsChain (Step I K ell n) := by
  induction fuel generalizing m with
  | zero => simp [walk]
  | succ fuel ih =>
    rw [walk]
    split_ifs with he
    · exact List.IsChain.singleton _
    · apply (ih _ (next_sameCell I K ell m n hc he)).cons
      intro y hy
      rw [walk_head] at hy
      have hey : next I K ell m n hc he = y := Option.mem_some_iff.mp hy
      exact ⟨hc, he, hey.symm⟩

/-- Every vertex belongs to the same exact complete-array cell. -/
theorem walk_mem_cell (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) :
    ∀ x ∈ walk I K ell fuel m n hc, SameCell I K ell n x := by
  induction fuel generalizing m with
  | zero =>
    intro x hx
    have he : x = m := by simpa only [walk, List.mem_singleton] using hx
    subst x
    exact sameCell_symm I K ell hc
  | succ fuel ih =>
    rw [walk]
    split_ifs with he
    · intro x hx
      have hh : x = m := List.mem_singleton.mp hx
      subst x
      exact sameCell_symm I K ell hc
    · intro x hx
      rcases List.mem_cons.mp hx with hh | hh
      · subst x
        exact sameCell_symm I K ell hc
      · exact ih _ (next_sameCell I K ell m n hc he) x hh

/-- The complete group-C path certificate, before any test vector or target coordinates. -/
theorem path_spec (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (m : Arr N) :
    (path I K ell m).head? = some m ∧
    (path I K ell m).getLast? = some (root I K ell m).1 ∧
    (path I K ell m).IsChain (Step I K ell (root I K ell m).1) ∧
    (∀ x ∈ path I K ell m, SameCell I K ell m x) ∧
    (path I K ell m).length - 1 ≤ I.card * ell := by
  refine ⟨walk_head I K ell _ _ _ _, path_last I K ell m, walk_chain I K ell _ _ _ _, ?_,
    path_length I K ell hell m⟩
  intro x hx
  exact sameCell_trans I K ell (root I K ell m).2 (walk_mem_cell I K ell _ _ _ _ x hx)

/-- Each step moves both changed counts towards the root, within the same intervals. -/
theorem next_between (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) (c : ℤ) :
    min (m.1 c) (n.1 c) ≤ (next I K ell m n hc hne).1 c ∧
    (next I K ell m n hc hne).1 c ≤ max (m.1 c) (n.1 c) := by
  have ha := (firstAbove_spec I K ell m n hc hne).2
  have hb := (firstBelow_spec I K ell m n hc hne).2
  have hab : firstAbove I K ell m n hc hne ≠ firstBelow I K ell m n hc hne := by
    intro he
    rw [he] at ha
    omega
  change min (m.1 c) (n.1 c) ≤
    shift (firstAbove I K ell m n hc hne) (firstBelow I K ell m n hc hne) m.1 c ∧
    shift (firstAbove I K ell m n hc hne) (firstBelow I K ell m n hc hne) m.1 c ≤
      max (m.1 c) (n.1 c)
  by_cases hca : c = firstAbove I K ell m n hc hne
  · subst c
    rw [shift_apply_donor m.1 hab]
    omega
  · by_cases hcb : c = firstBelow I K ell m n hc hne
    · subst c
      rw [shift_apply_receiver m.1 hab]
      omega
    · rw [shift_apply_exterior m.1 hca hcb]
      exact ⟨min_le_left _ _, le_max_left _ _⟩

theorem firstAbove_le (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) (a : ℤ) (ha : a ∈ I)
    (hlt : n.1 a < m.1 a) : firstAbove I K ell m n hc hne ≤ a :=
  Finset.min'_le _ a (Finset.mem_filter.mpr ⟨ha, hlt⟩)

theorem firstBelow_le (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) (b : ℤ) (hb : b ∈ I)
    (hlt : m.1 b < n.1 b) : firstBelow I K ell m n hc hne ≤ b :=
  Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hb, hlt⟩)

end QuantumNLS.FiniteCellPaths

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellPaths.selectedList
#print axioms QuantumNLS.FiniteCellPaths.selectedList_injective
#print axioms QuantumNLS.FiniteCellPaths.vertexOrder
#print axioms QuantumNLS.FiniteCellPaths.root
#print axioms QuantumNLS.FiniteCellPaths.root_le
#print axioms QuantumNLS.FiniteCellPaths.array_eq_of_le
#print axioms QuantumNLS.FiniteCellPaths.above_below_exist
#print axioms QuantumNLS.FiniteCellPaths.div_eq_between
#print axioms QuantumNLS.FiniteCellPaths.step_sameCell
#print axioms QuantumNLS.FiniteCellPaths.aboveSet
#print axioms QuantumNLS.FiniteCellPaths.belowSet
#print axioms QuantumNLS.FiniteCellPaths.firstAbove
#print axioms QuantumNLS.FiniteCellPaths.firstBelow
#print axioms QuantumNLS.FiniteCellPaths.firstAbove_spec
#print axioms QuantumNLS.FiniteCellPaths.firstBelow_spec
#print axioms QuantumNLS.FiniteCellPaths.root_eq_of_sameCell
#print axioms QuantumNLS.FiniteCellPaths.distance
#print axioms QuantumNLS.FiniteCellPaths.distance_zero_iff
#print axioms QuantumNLS.FiniteCellPaths.distance_step
#print axioms QuantumNLS.FiniteCellPaths.surplus_lt_ell
#print axioms QuantumNLS.FiniteCellPaths.distance_le
#print axioms QuantumNLS.FiniteCellPaths.next
#print axioms QuantumNLS.FiniteCellPaths.next_sameCell
#print axioms QuantumNLS.FiniteCellPaths.distance_next
#print axioms QuantumNLS.FiniteCellPaths.walk
#print axioms QuantumNLS.FiniteCellPaths.Step
#print axioms QuantumNLS.FiniteCellPaths.walk_last
#print axioms QuantumNLS.FiniteCellPaths.walk_length
#print axioms QuantumNLS.FiniteCellPaths.path
#print axioms QuantumNLS.FiniteCellPaths.path_last
#print axioms QuantumNLS.FiniteCellPaths.path_length
#print axioms QuantumNLS.FiniteCellPaths.walk_head
#print axioms QuantumNLS.FiniteCellPaths.walk_nonempty
#print axioms QuantumNLS.FiniteCellPaths.walk_chain
#print axioms QuantumNLS.FiniteCellPaths.walk_mem_cell
#print axioms QuantumNLS.FiniteCellPaths.path_spec
#print axioms QuantumNLS.FiniteCellPaths.next_between
#print axioms QuantumNLS.FiniteCellPaths.firstAbove_le
#print axioms QuantumNLS.FiniteCellPaths.firstBelow_le

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellPaths.selectedList,
    ``QuantumNLS.FiniteCellPaths.selectedList_injective,
    ``QuantumNLS.FiniteCellPaths.vertexOrder,
    ``QuantumNLS.FiniteCellPaths.root,
    ``QuantumNLS.FiniteCellPaths.root_le,
    ``QuantumNLS.FiniteCellPaths.array_eq_of_le,
    ``QuantumNLS.FiniteCellPaths.above_below_exist,
    ``QuantumNLS.FiniteCellPaths.div_eq_between,
    ``QuantumNLS.FiniteCellPaths.step_sameCell,
    ``QuantumNLS.FiniteCellPaths.aboveSet,
    ``QuantumNLS.FiniteCellPaths.belowSet,
    ``QuantumNLS.FiniteCellPaths.firstAbove,
    ``QuantumNLS.FiniteCellPaths.firstBelow,
    ``QuantumNLS.FiniteCellPaths.firstAbove_spec,
    ``QuantumNLS.FiniteCellPaths.firstBelow_spec,
    ``QuantumNLS.FiniteCellPaths.root_eq_of_sameCell,
    ``QuantumNLS.FiniteCellPaths.distance,
    ``QuantumNLS.FiniteCellPaths.distance_zero_iff,
    ``QuantumNLS.FiniteCellPaths.distance_step,
    ``QuantumNLS.FiniteCellPaths.surplus_lt_ell,
    ``QuantumNLS.FiniteCellPaths.distance_le,
    ``QuantumNLS.FiniteCellPaths.next,
    ``QuantumNLS.FiniteCellPaths.next_sameCell,
    ``QuantumNLS.FiniteCellPaths.distance_next,
    ``QuantumNLS.FiniteCellPaths.walk,
    ``QuantumNLS.FiniteCellPaths.Step,
    ``QuantumNLS.FiniteCellPaths.walk_last,
    ``QuantumNLS.FiniteCellPaths.walk_length,
    ``QuantumNLS.FiniteCellPaths.path,
    ``QuantumNLS.FiniteCellPaths.path_last,
    ``QuantumNLS.FiniteCellPaths.path_length,
    ``QuantumNLS.FiniteCellPaths.walk_head,
    ``QuantumNLS.FiniteCellPaths.walk_nonempty,
    ``QuantumNLS.FiniteCellPaths.walk_chain,
    ``QuantumNLS.FiniteCellPaths.walk_mem_cell,
    ``QuantumNLS.FiniteCellPaths.path_spec,
    ``QuantumNLS.FiniteCellPaths.next_between,
    ``QuantumNLS.FiniteCellPaths.firstAbove_le,
    ``QuantumNLS.FiniteCellPaths.firstBelow_le]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellPaths aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
