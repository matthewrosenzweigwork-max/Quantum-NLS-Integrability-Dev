import QuantumNLS.BetheGeneratedEndpoints

/-! Physical output promotion at a mixed internal face. The ambient physical
labels are retained, so insertion/deletion never silently renumbers a spectator.
This is a partial cross-degree checkpoint: global generated corner/chart
regrouping and cyclic matching remain separate obligations. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheNeighborPromotion
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheInternalFaces

abbrev MarkedLow (N m : ℕ) :=
  {p : Finset (Fin N) × Fin N // p.1.card = m ∧ p.2 ∉ p.1}
abbrev MarkedHigh (N m : ℕ) :=
  {p : Finset (Fin N) × Fin N // p.1.card = m+1 ∧ p.2 ∈ p.1}

/-- Promote precisely the marked physical spectator; inverse: delete that
same physical output. This is a bijection of marked subsets, not yet a
bijection of the generated endpoint/chart labels. -/
def promotionEquiv (N m : ℕ) : MarkedLow N m ≃ MarkedHigh N m where
  toFun p := ⟨(insert p.1.2 p.1.1, p.1.2), by simp [p.2.1, p.2.2]⟩
  invFun p := ⟨(p.1.1.erase p.1.2, p.1.2), by simp [Finset.card_erase_of_mem p.2.2, p.2.1]⟩
  left_inv p := by apply Subtype.ext; simp [Finset.erase_insert p.2.2]
  right_inv p := by apply Subtype.ext; simp [Finset.insert_erase p.2.2]

/-- a is the selected output immediately before t (plus), or immediately
after t (minus). The marked t is still a spectator in the lower degree. -/
def internalGap {N : ℕ} (A : Finset (Fin N)) (a t : Fin N) (b : Bool) : Prop :=
  a ∈ A ∧ t ∉ A ∧ if b then t < a ∧ ∀ k ∈ A, t < k → a ≤ k
    else a < t ∧ ∀ k ∈ A, k < t → k ≤ a

/-- Literal closed alternating support in physical output labels.
All comparisons are included; the sorted-coordinate equivalence below
identifies this with the original adjacent rectangle. -/
def physicalDomain {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (A : Finset (Fin N))
    (y : Fin N → ℝ) (b : Bool) : Prop :=
  ∀ a ∈ A, if b then x a ≤ y a ∧ y a ≤ L ∧ ∀ k ∈ A, k < a → y a ≤ x k
    else 0 ≤ y a ∧ y a ≤ x a ∧ ∀ k ∈ A, a < k → x k ≤ y a

/-- Exact all-pairs description of the source's adjacent rectangle. -/
theorem closedRectangle_iff_allPairs {m : ℕ} (L : ℝ) (X Y : Fin m → ℝ)
    (hX : Antitone X) (hb : ∀ i, X i ∈ Icc 0 L) (b : Bool) :
    Y ∈ closedRectangle L X b ↔
      ∀ i, if b then X i ≤ Y i ∧ Y i ≤ L ∧ ∀ j, j < i → Y i ≤ X j
        else 0 ≤ Y i ∧ Y i ≤ X i ∧ ∀ j, i < j → X j ≤ Y i := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro h i
      have hlo := (h i).1
      have hu : Y i ≤ X i := (h i).2
      refine ⟨?_, hu, ?_⟩
      · simp only [rectangleLower, Bool.false_eq_true, ite_false, BetheFiniteNAction.lower] at hlo
        split_ifs at hlo with hi
        · exact (hb _).1.trans hlo
        · exact hlo
      · intro j hij
        have hi : i.val+1 < m := by have := j.isLt; change i.val < j.val at hij; omega
        have hk : (⟨i.val+1, hi⟩ : Fin m) ≤ j := by change i.val+1 ≤ j.val; change i.val < j.val at hij; omega
        have hl : X ⟨i.val+1, hi⟩ ≤ Y i := by
          simpa [rectangleLower, BetheFiniteNAction.lower, hi] using hlo
        exact (hX hk).trans hl
    · intro h i
      refine ⟨?_, (h i).2.1⟩
      simp only [rectangleLower, Bool.false_eq_true, ite_false, BetheFiniteNAction.lower]
      split_ifs with hi
      · exact (h i).2.2 _ (by change i.val < i.val+1; omega)
      · exact (h i).1
  · simp only [ite_true]
    constructor
    · intro h i
      have hl : X i ≤ Y i := (h i).1
      have hu := (h i).2
      refine ⟨hl, ?_, ?_⟩
      · simp only [rectangleUpper, ite_true, BetheFiniteNAction.upper] at hu
        split_ifs at hu with hi
        · exact hu.trans (hb _).2
        · exact hu
      · intro j hji
        have hi : 0 < i.val := by change j.val < i.val at hji; omega
        have hk : j ≤ (⟨i.val-1, by omega⟩ : Fin m) := by change j.val ≤ i.val-1; change j.val < i.val at hji; omega
        have hh : Y i ≤ X ⟨i.val-1, by omega⟩ := by
          simpa [rectangleUpper, BetheFiniteNAction.upper, hi] using hu
        exact hh.trans (hX hk)
    · intro h i
      refine ⟨(h i).1, ?_⟩
      simp only [rectangleUpper, ite_true, BetheFiniteNAction.upper]
      split_ifs with hi
      · exact (h i).2.2 _ (by change i.val-1 < i.val; omega)
      · exact (h i).2.1

/-- The physical-label support is the actual rectangle on the selected
ordered outputs, including empty and collapsed faces. -/
theorem physicalDomain_iff_rectangle {N m : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (hb : ∀ i, x i ∈ Icc 0 L)
    (A : Finset (Fin N)) (hA : A.card = m) (b : Bool) :
    physicalDomain L x A y b ↔
      (fun i => y (A.orderEmbOfFin hA i)) ∈ closedRectangle L
        (fun i => x (A.orderEmbOfFin hA i)) b := by
  rw [closedRectangle_iff_allPairs L _ _ (fun _ _ hij => hx ((A.orderEmbOfFin hA).monotone hij))
    (fun i => hb _) b]
  have hex (k : Fin N) (hk : k ∈ A) : ∃ i : Fin m, A.orderEmbOfFin hA i = k := by
    exact ⟨(A.orderIsoOfFin hA).symm ⟨k,hk⟩,
      congrArg Subtype.val ((A.orderIsoOfFin hA).apply_symm_apply ⟨k,hk⟩)⟩
  constructor
  · intro h i
    have hi := h _ (A.orderEmbOfFin_mem hA i)
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hi ⊢
    · exact ⟨hi.1, hi.2.1, fun j hj => hi.2.2 _ (A.orderEmbOfFin_mem hA j)
        ((A.orderEmbOfFin hA).strictMono hj)⟩
    · exact ⟨hi.1, hi.2.1, fun j hj => hi.2.2 _ (A.orderEmbOfFin_mem hA j)
        ((A.orderEmbOfFin hA).strictMono hj)⟩
  · intro h a ha
    obtain ⟨i, rfl⟩ := hex a ha
    have hi := h i
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hi ⊢
    · refine ⟨hi.1, hi.2.1, ?_⟩
      intro k hk hik
      obtain ⟨j, rfl⟩ := hex k hk
      exact hi.2.2 j ((A.orderEmbOfFin hA).strictMono.lt_iff_lt.mp hik)
    · refine ⟨hi.1, hi.2.1, ?_⟩
      intro k hk hki
      obtain ⟨j, rfl⟩ := hex k hk
      exact hi.2.2 j ((A.orderEmbOfFin hA).strictMono.lt_iff_lt.mp hki)

/-- Promote the spectator value without changing any other original label. -/
def promoteTuple {N : ℕ} (x y : Fin N → ℝ) (t : Fin N) : Fin N → ℝ :=
  Function.update y t (x t)

/-- Full domain matching for the two adjacent face constraints. The same
ambient physical labels parametrize both residual domains. -/
theorem physicalDomain_promote_iff {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (hb : ∀ i, x i ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t) :
    physicalDomain L x (insert t A) (promoteTuple x y t) b ↔
      physicalDomain L x A y b := by
  classical
  have ht : t ∉ A := hg.2.1
  have hat : a ≠ t := fun h => ht (h ▸ hg.1)
  have hy (k : Fin N) (hk : k ∈ A) : promoteTuple x y t k = y k := by
    exact Function.update_of_ne (fun (h : k = t) => ht (h ▸ hk)) _ _
  cases b
  · have gap : a < t ∧ ∀ k ∈ A, k < t → k ≤ a := hg.2.2
    constructor
    · intro h k hk
      have hh := h k (Finset.mem_insert_of_mem hk)
      simp only [Bool.false_eq_true, ite_false, hy k hk] at hh
      exact ⟨hh.1, hh.2.1, fun j hj hjk => hh.2.2 j (Finset.mem_insert_of_mem hj) hjk⟩
    · intro h k hk
      simp only [physicalDomain, Bool.false_eq_true, ite_false] at h ⊢
      rcases Finset.mem_insert.mp hk with hkt | hk
      · subst k
        simp only [promoteTuple, Function.update_self]
        refine ⟨(hb t).1, le_rfl, ?_⟩
        intro j _ htj
        exact hx htj.le
      · rw [hy k hk]
        refine ⟨(h k hk).1, (h k hk).2.1, ?_⟩
        intro j hj hkj
        rcases Finset.mem_insert.mp hj with hjt | hj
        · rw [hjt] at hkj ⊢
          have hka := gap.2 k hk hkj
          rcases lt_or_eq_of_le hka with hka | rfl
          · exact (hx gap.1.le).trans ((h k hk).2.2 a hg.1 hka)
          · exact le_of_eq he.symm
        · exact (h k hk).2.2 j hj hkj
  · have gap : t < a ∧ ∀ k ∈ A, t < k → a ≤ k := hg.2.2
    constructor
    · intro h k hk
      have hh := h k (Finset.mem_insert_of_mem hk)
      simp only [ite_true, hy k hk] at hh
      exact ⟨hh.1, hh.2.1, fun j hj hjk => hh.2.2 j (Finset.mem_insert_of_mem hj) hjk⟩
    · intro h k hk
      simp only [physicalDomain, ite_true] at h ⊢
      rcases Finset.mem_insert.mp hk with hkt | hk
      · subst k
        simp only [promoteTuple, Function.update_self]
        refine ⟨le_rfl, (hb t).2, ?_⟩
        intro j _ hjt
        exact hx hjt.le
      · rw [hy k hk]
        refine ⟨(h k hk).1, (h k hk).2.1, ?_⟩
        intro j hj hjk
        rcases Finset.mem_insert.mp hj with hjt | hj
        · rw [hjt] at hjk ⊢
          have hak := gap.2 k hk hjk
          rcases lt_or_eq_of_le hak with hak | rfl
          · exact ((h k hk).2.2 a hg.1 hak).trans (hx gap.1.le)
          · exact le_of_eq he
        · exact (h k hk).2.2 j hj hjk

/-- The marked output is now selected; a,t are adjacent in that selected
set, with their physical order fixed by the literal kernel branch. -/
def promotedGap {N : ℕ} (B : Finset (Fin N)) (a t : Fin N) (b : Bool) : Prop :=
  a ∈ B ∧ t ∈ B ∧ if b then t < a ∧ ∀ k ∈ B, t < k → a ≤ k
    else a < t ∧ ∀ k ∈ B, k < t → k ≤ a

theorem promotedGap_insert_iff {N : ℕ} (A : Finset (Fin N)) (a t : Fin N)
    (ht : t ∉ A) (b : Bool) :
    promotedGap (insert t A) a t b ↔ internalGap A a t b := by
  classical
  by_cases hat : a = t
  · subst a
    cases b <;> simp [promotedGap, internalGap]
  · cases b <;> simp [promotedGap, internalGap, hat, ht]

theorem internalGap_erase_iff {N : ℕ} (B : Finset (Fin N)) (a t : Fin N)
    (ht : t ∈ B) (b : Bool) :
    internalGap (B.erase t) a t b ↔ promotedGap B a t b := by
  have hh := promotedGap_insert_iff (B.erase t) a t (Finset.notMem_erase t B) b
  simpa [Finset.insert_erase ht] using hh.symm

/-- Actual marked physical gap labels have multiplicity one in each
direction. Endpoint assignments and input-chart labels are not included. -/
def internalPromotionEquiv (N m : ℕ) (a : Fin N) (b : Bool) :
    {p : MarkedLow N m // internalGap p.1.1 a p.1.2 b} ≃
      {p : MarkedHigh N m // promotedGap p.1.1 a p.1.2 b} where
  toFun p := ⟨promotionEquiv N m p.1,
    (promotedGap_insert_iff _ _ _ p.1.2.2 b).mpr p.2⟩
  invFun p := ⟨(promotionEquiv N m).symm p.1,
    (internalGap_erase_iff _ _ _ p.1.2.2 b).mpr p.2⟩
  left_inv p := by apply Subtype.ext; exact (promotionEquiv N m).left_inv p.1
  right_inv p := by apply Subtype.ext; exact (promotionEquiv N m).right_inv p.1

/-- Assemble moving values and the literal fixed output spectators. -/
def physicalInput {N : ℕ} (x y : Fin N → ℝ) (A : Finset (Fin N)) : Fin N → ℝ :=
  fun k => if k ∈ A then y k else x k

/-- Promotion preserves the entire unsorted input, not only its collision
coordinate. Therefore every common sorting permutation has the same tuple. -/
theorem physicalInput_promote {N : ℕ} (x y : Fin N → ℝ) (A : Finset (Fin N))
    (t : Fin N) (ht : t ∉ A) :
    physicalInput x (promoteTuple x y t) (insert t A) = physicalInput x y A := by
  classical
  funext k
  by_cases hkt : k = t
  · subst k
    simp [physicalInput, promoteTuple, ht]
  · simp [physicalInput, promoteTuple, hkt]

/-- The complete branch displacement: minus retains its extra L. -/
def physicalOffset {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (b : Bool) : ℝ :=
  (if b then L else 0) + ∑ k ∈ A, (x k - y k)

theorem physicalOffset_promote {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (t : Fin N) (ht : t ∉ A) (b : Bool) :
    physicalOffset L x (promoteTuple x y t) (insert t A) b =
      physicalOffset L x y A b := by
  classical
  unfold physicalOffset
  rw [Finset.sum_insert ht]
  simp only [promoteTuple, Function.update_self, sub_self, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (fun (h : k = t) => ht (h ▸ hk))]

/-- Equality of the actual lower and higher degree rectangle supports,
using the respective ordered output subsets rather than a stipulated domain. -/
theorem promoted_rectangles_iff {N m : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (hA : A.card = m) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t) :
    let B := insert t A
    let hB : B.card = m+1 := by simp [B, hg.2.1, hA]
    (fun i => promoteTuple x y t (B.orderEmbOfFin hB i)) ∈
        closedRectangle L (fun i => x (B.orderEmbOfFin hB i)) b ↔
      (fun i => y (A.orderEmbOfFin hA i)) ∈
        closedRectangle L (fun i => x (A.orderEmbOfFin hA i)) b := by
  dsimp only
  rw [← physicalDomain_iff_rectangle L x _ hx hb,
    physicalDomain_promote_iff L x y hx hb A a t b hg he,
    physicalDomain_iff_rectangle L x y hx hb A hA b]

/-- Ordinary per-subset coefficients match after the BIF1 contact factor.
BPR1 has already derived these coefficients from the source (N)_m. -/
theorem ordered_subset_coefficients (c : ℝ) (m : ℕ) :
    (c : ℂ)^m * (c : ℂ) = (c : ℂ)^(m+1) := (pow_succ _ _).symm

def physicalOrientation {N : ℕ} (A : Finset (Fin N)) (ε : Fin N → Bool) : ℂ :=
  ∏ k ∈ A, if ε k then 1 else -1

/-- Ordinary signs for both marked endpoint choices in every assignment,
with all remaining endpoint signs kept. No orbit factor is inserted. -/
theorem promoted_orientation {N : ℕ} (A : Finset (Fin N)) (a t : Fin N)
    (ha : a ∈ A) (ht : t ∉ A) (ε : Fin N → Bool) (b : Bool)
    (hea : ε a = b) (het : ε t = !b) :
    physicalOrientation (insert t A) ε = -physicalOrientation (A.erase a) ε := by
  classical
  unfold physicalOrientation
  rw [Finset.prod_insert ht, ← Finset.mul_prod_erase A _ ha]
  rw [hea, het]
  cases b <;> simp

/-- These are exactly BGE1's generated signs after sorting selected output
labels. The finite embedding transports the whole endpoint assignment. -/
theorem orientation_ordered {N m : ℕ} (A : Finset (Fin N)) (hA : A.card = m)
    (ε : Fin N → Bool) :
    orientation (fun i => ε (A.orderEmbOfFin hA i)) = physicalOrientation A ε := by
  classical
  unfold orientation physicalOrientation
  conv_rhs => rw [← A.image_orderEmbOfFin_univ hA]
  rw [Finset.prod_image (fun _ _ _ _ h => (A.orderEmbOfFin hA).injective h)]

/-- A fixed common ordering transports the pending denominator labels.
For the second lower incidence a and t are exchanged. -/
def integratedRanks {N : ℕ} (π : Equiv.Perm (Fin N)) (A : Finset (Fin N)) :
    Finset (Fin N) := A.image π

theorem integratedRanks_insert {N : ℕ} (π : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) (t : Fin N) :
    integratedRanks π (insert t A) = insert (π t) (integratedRanks π A) := by
  classical
  exact Finset.image_insert _ _ _

theorem rank_absent {N : ℕ} (π : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) (t : Fin N) (ht : t ∉ A) :
    π t ∉ integratedRanks π A := by
  classical
  simpa [integratedRanks, Finset.mem_image, π.injective.eq_iff] using ht

/-- Local signed neighboring-degree balance on the preserved physical
input, with complete pending sets, both branch orientations, the full
branch phase, exact ordered-subset coefficients and all other corner signs.
Adjacency in the common input ordering is an explicit geometric hypothesis;
no global generated-chart correspondence is asserted here. -/
theorem source_promoted_face_balance {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x y : Fin N → ℝ) (A : Finset (Fin N)) (a t : Fin N)
    (ha : a ∈ A) (ht : t ∉ A) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (b : Bool)
    (hadj : if b then (π a).val = (π t).val+1 else (π t).val = (π a).val+1)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (ε : Fin N → Bool) (hea : ε a = b) (het : ε t = !b) :
    let r := BetheSmooth.sourceRoots L n c
    let w := physicalInput x y A ∘ π.symm
    let P := fun D => primitive c r w z (integratedRanks π D)
    let phase := Complex.exp (Complex.I*z*(physicalOffset L x y A b : ℂ))
    (c : ℂ)^A.card * phase * physicalOrientation (A.erase a) ε *
        (if b then P A - P (insert t (A.erase a))
          else P (insert t (A.erase a)) - P A) +
      (c : ℂ)^(A.card+1) * phase * physicalOrientation (insert t A) ε *
        P (insert t A) = 0 := by
  classical
  dsimp only
  have hset : insert a (A.erase a) = A := Finset.insert_erase ha
  have han := rank_absent π (A.erase a) a (Finset.notMem_erase _ _)
  have htn := rank_absent π (A.erase a) t (fun h => ht (Finset.mem_of_mem_erase h))
  have hwa : (physicalInput x y A ∘ π.symm) (π a) = y a := by
    simp [physicalInput, ha]
  have hwt : (physicalInput x y A ∘ π.symm) (π t) = x t := by
    simp [physicalInput, ht]
  have hwall : (physicalInput x y A ∘ π.symm) (π a) =
      (physicalInput x y A ∘ π.symm) (π t) := hwa.trans (he.trans hwt.symm)
  have hins : integratedRanks π A = insert (π a) (integratedRanks π (A.erase a)) := by
    rw [← integratedRanks_insert, hset]
  have hhins : integratedRanks π (insert t A) =
      insert (π a) (insert (π t) (integratedRanks π (A.erase a))) := by
    rw [integratedRanks_insert, hins, Finset.insert_comm]
  have hface :
      (if b then primitive c (BetheSmooth.sourceRoots L n c) (physicalInput x y A ∘ π.symm) z
            (integratedRanks π A) -
          primitive c (BetheSmooth.sourceRoots L n c) (physicalInput x y A ∘ π.symm) z
            (integratedRanks π (insert t (A.erase a)))
        else primitive c (BetheSmooth.sourceRoots L n c) (physicalInput x y A ∘ π.symm) z
            (integratedRanks π (insert t (A.erase a))) -
          primitive c (BetheSmooth.sourceRoots L n c) (physicalInput x y A ∘ π.symm) z
            (integratedRanks π A)) =
        (c : ℂ) * primitive c (BetheSmooth.sourceRoots L n c) (physicalInput x y A ∘ π.symm) z
          (integratedRanks π (insert t A)) := by
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hadj ⊢
      rw [integratedRanks_insert, hins, hhins]
      exact source_primitive_internal_face hL hc hn _ z hz _ hadj han htn hwall
    · simp only [ite_true] at hadj ⊢
      rw [integratedRanks_insert, hins, hhins, Finset.insert_comm (π a) (π t)]
      exact source_primitive_internal_face hL hc hn _ z hz _ hadj htn han hwall.symm
  rw [hface, pow_succ, promoted_orientation A a t ha ht ε b hea het]
  ring

/-- Physical gap adjacency is adjacency in the ordered higher output;
there is no unspecified numerical multiplicity in this rank statement. -/
theorem promotedGap_adjacent {N m : ℕ} (B : Finset (Fin N)) (hB : B.card = m+1)
    (a t : Fin N) (b : Bool) (hg : promotedGap B a t b)
    (ia it : Fin (m+1)) (ha : B.orderEmbOfFin hB ia = a)
    (ht : B.orderEmbOfFin hB it = t) :
    if b then ia.val = it.val+1 else it.val = ia.val+1 := by
  have hmono := (B.orderEmbOfFin hB).strictMono
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    have gap : a < t ∧ ∀ k ∈ B, k < t → k ≤ a := hg.2.2
    have hi : ia < it := hmono.lt_iff_lt.mp (by simpa [ha, ht] using gap.1)
    have hn : ia.val+1 ≤ it.val := by change ia.val < it.val at hi; omega
    by_contra hne
    have hj : ia.val+1 < m+1 := by omega
    let j : Fin (m+1) := ⟨ia.val+1, hj⟩
    have hjt : j < it := by change ia.val+1 < it.val; omega
    have hle := gap.2 _ (B.orderEmbOfFin_mem hB j)
      (by simpa [ht] using hmono hjt)
    have hji : j ≤ ia := hmono.le_iff_le.mp (by simpa [ha] using hle)
    change ia.val+1 ≤ ia.val at hji
    omega
  · simp only [ite_true]
    have gap : t < a ∧ ∀ k ∈ B, t < k → a ≤ k := hg.2.2
    have hi : it < ia := hmono.lt_iff_lt.mp (by simpa [ha, ht] using gap.1)
    have hn : it.val+1 ≤ ia.val := by change it.val < ia.val at hi; omega
    by_contra hne
    have hj : it.val+1 < m+1 := by omega
    let j : Fin (m+1) := ⟨it.val+1, hj⟩
    have htj : it < j := by change it.val < it.val+1; omega
    have hle := gap.2 _ (B.orderEmbOfFin_mem hB j)
      (by simpa [ht] using hmono htj)
    have hij : ia ≤ j := hmono.le_iff_le.mp (by simpa [ha] using hle)
    change ia.val ≤ it.val+1 at hij
    omega

/-- The image is the actual doubly fixed rectangle face. The plus image
uses a-lower/t-upper, the minus image a-upper/t-lower. -/
theorem promoted_rectangle_faces {N m : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (hA : A.card = m) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (ia it : Fin (m+1))
    (ha : (insert t A).orderEmbOfFin (by simp [hg.2.1, hA]) ia = a)
    (ht : (insert t A).orderEmbOfFin (by simp [hg.2.1, hA]) it = t) :
    let hB : (insert t A).card = m+1 := by simp [hg.2.1, hA]
    let X := fun i => x ((insert t A).orderEmbOfFin hB i)
    let Y := fun i => promoteTuple x y t ((insert t A).orderEmbOfFin hB i)
    rectangleFaceEquation L X Y b (ia,b) ∧
      rectangleFaceEquation L X Y b (it,!b) := by
  classical
  dsimp only
  have hat : a ≠ t := fun h => hg.2.1 (h ▸ hg.1)
  have hay : promoteTuple x y t a = x t := by
    rw [promoteTuple, Function.update_of_ne hat, he]
  have hty : promoteTuple x y t t = x t := by simp [promoteTuple]
  have hadj := promotedGap_adjacent (insert t A) (by simp [hg.2.1, hA]) a t b
    ((promotedGap_insert_iff A a t hg.2.1 b).mpr hg) ia it ha ht
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hadj
    have hi : ia.val+1 < m+1 := by omega
    have hie : (⟨ia.val+1,hi⟩ : Fin (m+1)) = it := Fin.ext hadj.symm
    constructor
    · simp [rectangleFaceEquation, rectangleLower, BetheFiniteNAction.lower,
        hi, hie, ha, ht, hay]
    · simp [rectangleFaceEquation, rectangleUpper, ht, hty]
  · simp only [ite_true] at hadj
    have hi : 0 < ia.val := by omega
    have hie : (⟨ia.val-1,by omega⟩ : Fin (m+1)) = it := by apply Fin.ext; change ia.val-1 = it.val; omega
    constructor
    · simp [rectangleFaceEquation, rectangleUpper, BetheFiniteNAction.upper,
        hi, hie, ha, ht, hay]
    · simp [rectangleFaceEquation, rectangleLower, ht, hty]

/-- At any actual chart incidence an original rectangle endpoint that
belongs to the cell is also its clipped endpoint. This is a pointwise
boundary statement and uses no restriction of an ambient a.e. identity. -/
theorem clipped_endpoint_of_rectangle_face {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (hX : X ∈ BetheWavefunctions.chamber m L) (hs : Antitone s)
    (hb : ∀ j, s j ∈ Icc 0 L) (hy : y ∈ BetheChartFiberSteps.closedPhysicalCell L X s b S)
    (i : Fin m) (e : Bool) (hf : rectangleFaceEquation L X y b (i,e)) :
    (if e then clipUpper L X s b S i else clipLower X s b S i) = y i := by
  have hbox := hy
  rw [closedPhysicalCell_eq_box L X s b S hX hs hb] at hbox
  cases e
  · have hlo : rectangleLower X b i ≤ clipLower X s b S i :=
      ((clipLower_le_iff X s b S i _).mp le_rfl).1
    have he : y i = rectangleLower X b i := hf
    exact le_antisymm (hbox.1 i) (he ▸ hlo)
  · have hup : clipUpper L X s b S i ≤ rectangleUpper L X b i :=
      ((le_clipUpper_iff L X s b S i _).mp le_rfl).1
    have he : y i = rectangleUpper L X b i := hf
    exact le_antisymm (he ▸ hup) (hbox.2 i)

/-- Every remaining original endpoint label is retained once. The two
marked higher endpoints have the signs forced by the branch orientation. -/
def extendFaceAssignment {N : ℕ} (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (ε : (A.erase a) → Bool) (k : ↥(insert t A : Finset (Fin N))) : Bool :=
  if hka : k.val = a then b else if hkt : k.val = t then !b else
    ε ⟨k.val, Finset.mem_erase.mpr ⟨hka, (Finset.mem_insert.mp k.2).resolve_left hkt⟩⟩

/-- Explicit inverse on endpoint assignments, before identifying coincident
geometric values. This counts labelled generated corners, including collisions. -/
def faceAssignmentEquiv {N : ℕ} (A : Finset (Fin N)) (a t : Fin N)
    (ha : a ∈ A) (ht : t ∉ A) (b : Bool) :
    ((A.erase a) → Bool) ≃
      {ε : ↥(insert t A : Finset (Fin N)) → Bool //
        ε ⟨a, Finset.mem_insert_of_mem ha⟩ = b ∧
        ε ⟨t, Finset.mem_insert_self _ _⟩ = !b} := by
  classical
  have hat : a ≠ t := fun h => ht (h ▸ ha)
  refine { toFun := fun ε => ⟨extendFaceAssignment A a t b ε, ?_⟩
           invFun := fun ε k => ε.1 ⟨k.val, Finset.mem_insert_of_mem (Finset.mem_of_mem_erase k.2)⟩
           left_inv := ?_
           right_inv := ?_ }
  · simp [extendFaceAssignment, hat.symm]
  · intro ε
    funext k
    have hka := (Finset.mem_erase.mp k.2).1
    have hkt : k.val ≠ t := fun h => ht (h ▸ Finset.mem_of_mem_erase k.2)
    simp [extendFaceAssignment, hka, hkt]
  · intro ε
    apply Subtype.ext
    funext k
    by_cases hka : k.val = a
    · have hk : k = ⟨a, Finset.mem_insert_of_mem ha⟩ := Subtype.ext hka
      simp [extendFaceAssignment, hk, ε.2.1]
    · by_cases hkt : k.val = t
      · have hk : k = ⟨t, Finset.mem_insert_self _ _⟩ := Subtype.ext hkt
        simp [extendFaceAssignment, hk, hat.symm, ε.2.2]
      · simp [extendFaceAssignment, hka, hkt]

theorem card_faceAssignments {N : ℕ} (A : Finset (Fin N)) (a t : Fin N)
    (ha : a ∈ A) (ht : t ∉ A) (b : Bool) :
    Fintype.card {ε : ↥(insert t A : Finset (Fin N)) → Bool //
      ε ⟨a, Finset.mem_insert_of_mem ha⟩ = b ∧
      ε ⟨t, Finset.mem_insert_self _ _⟩ = !b} = 2^(A.card-1) := by
  classical
  rw [← Fintype.card_congr (faceAssignmentEquiv A a t ha ht b)]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_erase_of_mem ha]

end QuantumNLS.BetheNeighborPromotion

#print axioms QuantumNLS.BetheNeighborPromotion.MarkedLow
#print axioms QuantumNLS.BetheNeighborPromotion.MarkedHigh
#print axioms QuantumNLS.BetheNeighborPromotion.promotionEquiv
#print axioms QuantumNLS.BetheNeighborPromotion.internalGap
#print axioms QuantumNLS.BetheNeighborPromotion.physicalDomain
#print axioms QuantumNLS.BetheNeighborPromotion.closedRectangle_iff_allPairs
#print axioms QuantumNLS.BetheNeighborPromotion.physicalDomain_iff_rectangle
#print axioms QuantumNLS.BetheNeighborPromotion.promoteTuple
#print axioms QuantumNLS.BetheNeighborPromotion.physicalDomain_promote_iff
#print axioms QuantumNLS.BetheNeighborPromotion.promotedGap
#print axioms QuantumNLS.BetheNeighborPromotion.promotedGap_insert_iff
#print axioms QuantumNLS.BetheNeighborPromotion.internalGap_erase_iff
#print axioms QuantumNLS.BetheNeighborPromotion.internalPromotionEquiv
#print axioms QuantumNLS.BetheNeighborPromotion.physicalInput
#print axioms QuantumNLS.BetheNeighborPromotion.physicalInput_promote
#print axioms QuantumNLS.BetheNeighborPromotion.physicalOffset
#print axioms QuantumNLS.BetheNeighborPromotion.physicalOffset_promote
#print axioms QuantumNLS.BetheNeighborPromotion.promoted_rectangles_iff
#print axioms QuantumNLS.BetheNeighborPromotion.ordered_subset_coefficients
#print axioms QuantumNLS.BetheNeighborPromotion.physicalOrientation
#print axioms QuantumNLS.BetheNeighborPromotion.promoted_orientation
#print axioms QuantumNLS.BetheNeighborPromotion.orientation_ordered
#print axioms QuantumNLS.BetheNeighborPromotion.integratedRanks
#print axioms QuantumNLS.BetheNeighborPromotion.integratedRanks_insert
#print axioms QuantumNLS.BetheNeighborPromotion.rank_absent
#print axioms QuantumNLS.BetheNeighborPromotion.source_promoted_face_balance
#print axioms QuantumNLS.BetheNeighborPromotion.promotedGap_adjacent
#print axioms QuantumNLS.BetheNeighborPromotion.promoted_rectangle_faces
#print axioms QuantumNLS.BetheNeighborPromotion.clipped_endpoint_of_rectangle_face
#print axioms QuantumNLS.BetheNeighborPromotion.extendFaceAssignment
#print axioms QuantumNLS.BetheNeighborPromotion.faceAssignmentEquiv
#print axioms QuantumNLS.BetheNeighborPromotion.card_faceAssignments

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheNeighborPromotion.internalPromotionEquiv,
    ``QuantumNLS.BetheNeighborPromotion.promoted_rectangles_iff,
    ``QuantumNLS.BetheNeighborPromotion.promoted_rectangle_faces,
    ``QuantumNLS.BetheNeighborPromotion.clipped_endpoint_of_rectangle_face,
    ``QuantumNLS.BetheNeighborPromotion.physicalInput_promote,
    ``QuantumNLS.BetheNeighborPromotion.physicalOffset_promote,
    ``QuantumNLS.BetheNeighborPromotion.orientation_ordered,
    ``QuantumNLS.BetheNeighborPromotion.source_promoted_face_balance,
    ``QuantumNLS.BetheNeighborPromotion.card_faceAssignments,
    ``QuantumNLS.BetheGeneratedEndpoints.source_transferTerm_corners_ae]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[
    ``QuantumNLS.BetheNeighborPromotion.promotionEquiv,
    ``QuantumNLS.BetheNeighborPromotion.physicalDomain_iff_rectangle,
    ``QuantumNLS.BetheNeighborPromotion.physicalDomain_promote_iff,
    ``QuantumNLS.BetheNeighborPromotion.promotedGap_adjacent,
    ``QuantumNLS.BetheNeighborPromotion.promoted_orientation,
    ``QuantumNLS.BetheNeighborPromotion.faceAssignmentEquiv,
    ``QuantumNLS.BetheGeneratedEndpoints.closedPhysicalCell_eq_box,
    ``QuantumNLS.BetheGeneratedEndpoints.integral_ansatz_box_corners,
    ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Neighbor promotion aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Neighbor promotion aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Neighbor promotion aggregate audit PASS: {seen.size} transitive constants across separate roots. Physical marked output/gap bijection, original rectangle domain matching, actual double endpoint faces, clipped endpoint identification, complete phase/input preservation, residual endpoint assignment bijection and local signed positive-c primitive balance. The BGE1 physical corner action is a separate root. Complete generated input-chart/corner matching and global cancellation/eigenrelation remain OPEN."
