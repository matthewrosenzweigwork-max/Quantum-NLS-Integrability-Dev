import QuantumNLS.FiniteCellSupport
import Mathlib.Data.Fintype.BigOperators

/-! R-D8BB052C group B. Cells are equivalence classes of COMPLETE arrays.
Exterior occupations are fixed by equality, never enumerated by a supplied finite list. -/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace QuantumNLS.FiniteCellPartition
open Occupation OccupationHilbert
variable {N : ℕ}

/-- K will later be ceil(N/ell); the partition itself works for every K. -/
def active (I : Finset ℤ) (K : ℕ) (m : Arr N) : Finset ℤ := I.filter (fun c => K ≤ m.1 c)

/-- Literal cell data: exterior, active set, inactive counts and active quotients. -/
def SameCell (I : Finset ℤ) (K ell : ℕ) (m n : Arr N) : Prop :=
  (∀ c, c ∉ I → m.1 c = n.1 c) ∧
  active I K m = active I K n ∧
  (∀ c, c ∈ I → c ∉ active I K m → m.1 c = n.1 c) ∧
  (∀ c, c ∈ active I K m → m.1 c / ell = n.1 c / ell)

theorem sameCell_refl (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : SameCell I K ell m m :=
  ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem sameCell_symm (I : Finset ℤ) (K ell : ℕ) {m n : Arr N}
    (h : SameCell I K ell m n) : SameCell I K ell n m := by
  refine ⟨fun c hc => (h.1 c hc).symm, h.2.1.symm, ?_, ?_⟩
  · intro c hc hn
    exact (h.2.2.1 c hc (h.2.1.symm ▸ hn)).symm
  · intro c hc
    exact (h.2.2.2 c (h.2.1.symm ▸ hc)).symm

theorem sameCell_trans (I : Finset ℤ) (K ell : ℕ) {m n p : Arr N}
    (hmn : SameCell I K ell m n) (hnp : SameCell I K ell n p) : SameCell I K ell m p := by
  refine ⟨fun c hc => (hmn.1 c hc).trans (hnp.1 c hc), hmn.2.1.trans hnp.2.1, ?_, ?_⟩
  · intro c hc hn
    exact (hmn.2.2.1 c hc hn).trans (hnp.2.2.1 c hc (hmn.2.1 ▸ hn))
  · intro c hc
    exact (hmn.2.2.2 c hc).trans (hnp.2.2.2 c (hmn.2.1 ▸ hc))

def cellSetoid (I : Finset ℤ) (K ell : ℕ) : Setoid (Arr N) where
  r := SameCell I K ell
  iseqv := ⟨sameCell_refl I K ell, sameCell_symm I K ell, sameCell_trans I K ell⟩

/-- Each complete array belongs to its actual equivalence class. -/
def cell (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : Set (Arr N) :=
  {n | SameCell I K ell m n}

abbrev Vertices (I : Finset ℤ) (K ell : ℕ) (m : Arr N) := ↥(cell I K ell m)

theorem cell_mem (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : m ∈ cell I K ell m :=
  sameCell_refl I K ell m

theorem mem_cell_iff (I : Finset ℤ) (K ell : ℕ) (m n : Arr N) :
    n ∈ cell I K ell m ↔
      (∀ c, c ∉ I → m.1 c = n.1 c) ∧
      active I K m = active I K n ∧
      (∀ c, c ∈ I → c ∉ active I K m → m.1 c = n.1 c) ∧
      (∀ c, c ∈ active I K m → m.1 c / ell = n.1 c / ell) := Iff.rfl

theorem cell_eq_of_mem (I : Finset ℤ) (K ell : ℕ) {m n : Arr N}
    (h : n ∈ cell I K ell m) : cell I K ell m = cell I K ell n := by
  ext p
  exact ⟨fun hp => sameCell_trans I K ell (sameCell_symm I K ell h) hp,
    fun hp => sameCell_trans I K ell h hp⟩

theorem cell_eq_or_disjoint (I : Finset ℤ) (K ell : ℕ) (m n : Arr N) :
    cell I K ell m = cell I K ell n ∨ Disjoint (cell I K ell m) (cell I K ell n) := by
  by_cases h : ∃ p, p ∈ cell I K ell m ∧ p ∈ cell I K ell n
  · obtain ⟨p, hm, hn⟩ := h
    exact Or.inl ((cell_eq_of_mem I K ell hm).trans (cell_eq_of_mem I K ell hn).symm)
  · right
    exact Set.disjoint_left.mpr (fun p hm hn => h ⟨p, hm, hn⟩)

theorem cell_cover (I : Finset ℤ) (K ell : ℕ) :
    (⋃ m : Arr N, cell I K ell m) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro m
  exact Set.mem_iUnion.mpr ⟨m, cell_mem I K ell m⟩

/-- Equality of selected counts and the fixed exterior determines a complete array. -/
theorem selected_counts_injective (I : Finset ℤ) (K ell : ℕ) (m : Arr N) :
    Function.Injective (fun n : Vertices I K ell m => fun c : I => n.1.1 c) := by
  intro n p h
  apply Subtype.ext; apply Subtype.ext
  ext c
  by_cases hc : c ∈ I
  · exact congrFun h ⟨c, hc⟩
  · exact (n.2.1 c hc).symm.trans (p.2.1 c hc)

/-- Finite enumeration follows from 0<=m_c<=N for selected counts alone. -/
def selectedCode (I : Finset ℤ) (K ell : ℕ) (m : Arr N) (n : Vertices I K ell m) :
    I → Fin (N + 1) := fun c => ⟨n.1.1 c, by
      have h := occ_le_total c n.1.1
      have hn : total n.1.1 = N := n.1.2
      omega⟩

theorem selectedCode_injective (I : Finset ℤ) (K ell : ℕ) (m : Arr N) :
    Function.Injective (selectedCode I K ell m) := by
  intro n p h
  apply selected_counts_injective I K ell m
  funext c
  exact congrArg Fin.val (congrFun h c)

theorem verticesFinite (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : Finite (Vertices I K ell m) :=
  Finite.of_injective (selectedCode I K ell m) (selectedCode_injective I K ell m)

attribute [instance] verticesFinite

/-- This is derived, not a list of full exteriors postulated as input. -/
@[instance_reducible]
def verticesFintype (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : Fintype (Vertices I K ell m) :=
  Fintype.ofFinite _

theorem inactive_cell_singleton (I : Finset ℤ) (K ell : ℕ) (m : Arr N)
    (h : active I K m = ∅) : cell I K ell m = {m} := by
  ext n
  constructor
  · intro hn
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    ext c
    by_cases hc : c ∈ I
    · exact (hn.2.2.1 c hc (by simp [h])).symm
    · exact (hn.1 c hc).symm
  · intro hn
    rw [Set.mem_singleton_iff] at hn
    rw [hn]
    exact cell_mem I K ell m

/-- All but one coordinate, together with the complete total, determine the last. -/
theorem array_ext_except (p : ℤ) {m n : Arr N} (h : ∀ c, c ≠ p → m.1 c = n.1 c) : m = n := by
  have he : m.1.erase p = n.1.erase p := by
    ext c
    by_cases hc : c = p
    · subst c; simp
    · simp only [Finsupp.erase_ne hc]; exact h c hc
  have hm := congrArg total (Finsupp.erase_add_single p m.1)
  have hn := congrArg total (Finsupp.erase_add_single p n.1)
  simp only [total, map_add, Finsupp.degree_single] at hm hn
  have hd : m.1.degree = n.1.degree := m.2.trans n.2.symm
  have hp : m.1 p = n.1 p := by rw [he] at hm; omega
  apply Subtype.ext
  ext c
  by_cases hc : c = p
  · subst c; exact hp
  · exact h c hc

/-- The sharp code stores only active remainders except one pivot. -/
def remainderCode (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (m : Arr N) (p : ℤ)
    (n : Vertices I K ell m) : (active I K m).erase p → Fin ell :=
  fun c => ⟨n.1.1 c % ell, Nat.mod_lt _ hell⟩

theorem remainderCode_injective (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell)
    (m : Arr N) (p : ℤ) : Function.Injective (remainderCode I K ell hell m p) := by
  intro n t h
  apply Subtype.ext
  apply array_ext_except p
  intro c hcp
  by_cases ha : c ∈ active I K m
  · have hc : c ∈ (active I K m).erase p := Finset.mem_erase.mpr ⟨hcp, ha⟩
    have hr : n.1.1 c % ell = t.1.1 c % ell := congrArg Fin.val (congrFun h ⟨c, hc⟩)
    have hq := (n.2.2.2.2 c ha).symm.trans (t.2.2.2.2 c ha)
    have hn := Nat.mod_add_div (n.1.1 c) ell
    have ht := Nat.mod_add_div (t.1.1 c) ell
    rw [hr, hq] at hn
    omega
  · by_cases hc : c ∈ I
    · exact (n.2.2.2.1 c hc ha).symm.trans (t.2.2.2.1 c hc ha)
    · exact (n.2.1 c hc).symm.trans (t.2.1 c hc)

/-- Exact source cardinality: ell^(h-1) for every cell with at least one active coordinate. -/
theorem active_cell_card (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (m : Arr N)
    (hactive : (active I K m).Nonempty) :
    Nat.card (Vertices I K ell m) ≤ ell ^ ((active I K m).card - 1) := by
  let _ := verticesFintype I K ell m
  obtain ⟨p, hp⟩ := hactive
  have h := Fintype.card_le_of_injective (remainderCode I K ell hell m p)
    (remainderCode_injective I K ell hell m p)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Finset.card_erase_of_mem hp] using h

end QuantumNLS.FiniteCellPartition

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellPartition.active
#print axioms QuantumNLS.FiniteCellPartition.SameCell
#print axioms QuantumNLS.FiniteCellPartition.sameCell_refl
#print axioms QuantumNLS.FiniteCellPartition.sameCell_symm
#print axioms QuantumNLS.FiniteCellPartition.sameCell_trans
#print axioms QuantumNLS.FiniteCellPartition.cellSetoid
#print axioms QuantumNLS.FiniteCellPartition.cell
#print axioms QuantumNLS.FiniteCellPartition.Vertices
#print axioms QuantumNLS.FiniteCellPartition.cell_mem
#print axioms QuantumNLS.FiniteCellPartition.mem_cell_iff
#print axioms QuantumNLS.FiniteCellPartition.cell_eq_of_mem
#print axioms QuantumNLS.FiniteCellPartition.cell_eq_or_disjoint
#print axioms QuantumNLS.FiniteCellPartition.cell_cover
#print axioms QuantumNLS.FiniteCellPartition.selected_counts_injective
#print axioms QuantumNLS.FiniteCellPartition.selectedCode
#print axioms QuantumNLS.FiniteCellPartition.selectedCode_injective
#print axioms QuantumNLS.FiniteCellPartition.verticesFinite
#print axioms QuantumNLS.FiniteCellPartition.verticesFintype
#print axioms QuantumNLS.FiniteCellPartition.inactive_cell_singleton
#print axioms QuantumNLS.FiniteCellPartition.array_ext_except
#print axioms QuantumNLS.FiniteCellPartition.remainderCode
#print axioms QuantumNLS.FiniteCellPartition.remainderCode_injective
#print axioms QuantumNLS.FiniteCellPartition.active_cell_card

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellPartition.active,
    ``QuantumNLS.FiniteCellPartition.SameCell,
    ``QuantumNLS.FiniteCellPartition.sameCell_refl,
    ``QuantumNLS.FiniteCellPartition.sameCell_symm,
    ``QuantumNLS.FiniteCellPartition.sameCell_trans,
    ``QuantumNLS.FiniteCellPartition.cellSetoid,
    ``QuantumNLS.FiniteCellPartition.cell,
    ``QuantumNLS.FiniteCellPartition.Vertices,
    ``QuantumNLS.FiniteCellPartition.cell_mem,
    ``QuantumNLS.FiniteCellPartition.mem_cell_iff,
    ``QuantumNLS.FiniteCellPartition.cell_eq_of_mem,
    ``QuantumNLS.FiniteCellPartition.cell_eq_or_disjoint,
    ``QuantumNLS.FiniteCellPartition.cell_cover,
    ``QuantumNLS.FiniteCellPartition.selected_counts_injective,
    ``QuantumNLS.FiniteCellPartition.selectedCode,
    ``QuantumNLS.FiniteCellPartition.selectedCode_injective,
    ``QuantumNLS.FiniteCellPartition.verticesFinite,
    ``QuantumNLS.FiniteCellPartition.verticesFintype,
    ``QuantumNLS.FiniteCellPartition.inactive_cell_singleton,
    ``QuantumNLS.FiniteCellPartition.array_ext_except,
    ``QuantumNLS.FiniteCellPartition.remainderCode,
    ``QuantumNLS.FiniteCellPartition.remainderCode_injective,
    ``QuantumNLS.FiniteCellPartition.active_cell_card]
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
  Lean.logInfo m!"FiniteCellPartition aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
