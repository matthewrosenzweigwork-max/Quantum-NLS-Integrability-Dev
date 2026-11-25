import QuantumNLS.BethePhysicalFaceCharts

/-! Pointwise closed-cell incidence. Unlike an a.e. integral partition these
identities include boundary values. At a single moving/spectator collision
there are exactly two merged charts, with the same literal source tuple.
Higher intersections and successive primitive integration remain separate. -/
noncomputable section
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheRectangleIncidence
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts

/-- Input labels, rather than chamber ranks. -/
def selectedRank {m q : ℕ} (S : PlacementSubset m q) (i : Fin m) : Fin (m+q) :=
  mergePermutation S (Fin.castAdd q i)

def spectatorRank {m q : ℕ} (S : PlacementSubset m q) (j : Fin q) : Fin (m+q) :=
  mergePermutation S (Fin.natAdd m j)

theorem mergeChart_selected {m q : ℕ} (S : PlacementSubset m q)
    (y : Fin m → ℝ) (s : Fin q → ℝ) (i : Fin m) :
    mergeChart S y s (selectedRank S i) = y i := by
  simp [mergeChart, selectedRank]

theorem mergeChart_spectator {m q : ℕ} (S : PlacementSubset m q)
    (y : Fin m → ℝ) (s : Fin q → ℝ) (j : Fin q) :
    mergeChart S y s (spectatorRank S j) = s j := by
  simp [mergeChart, spectatorRank]

/-- Every mixed chamber inequality, with its actual orientation. -/
def crossConstraints {m q : ℕ} (S : PlacementSubset m q)
    (y : Fin m → ℝ) (s : Fin q → ℝ) : Prop :=
  ∀ i j, (selectedRank S i ≤ spectatorRank S j → s j ≤ y i) ∧
    (spectatorRank S j ≤ selectedRank S i → y i ≤ s j)

theorem chartSet_iff {m q : ℕ} (S : PlacementSubset m q)
    (y : Fin m → ℝ) (s : Fin q → ℝ) :
    y ∈ chartSet S s ↔ Antitone y ∧ Antitone s ∧ crossConstraints S y s := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have hr : selectedRank S i ≤ selectedRank S j := by
        simpa [selectedRank, mergePermutation_selected] using (S.1.orderEmbOfFin S.2).monotone hij
      simpa only [mergeChart_selected] using h hr
    · intro i j hij
      have hr : spectatorRank S i ≤ spectatorRank S j := by
        simpa [spectatorRank, mergePermutation_spectator] using
          (S.1ᶜ.orderEmbOfFin (complement_card S)).monotone hij
      simpa only [mergeChart_spectator] using h hr
    · intro i j
      constructor <;> intro hr
      · simpa only [mergeChart_selected, mergeChart_spectator] using h hr
      · simpa only [mergeChart_selected, mergeChart_spectator] using h hr
  · rintro ⟨hy, hs, hc⟩ a b hab
    obtain ⟨a, rfl⟩ := (mergePermutation S).surjective a
    obtain ⟨b, rfl⟩ := (mergePermutation S).surjective b
    revert hab
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) b <;> intro hab
    · have hij : i ≤ j := by
        simpa only [mergePermutation_selected, OrderEmbedding.le_iff_le] using hab
      simpa [mergeChart] using hy hij
    · simpa [mergeChart] using (hc i j).1 hab
    · simpa [mergeChart] using (hc j i).2 hab
    · have hij : i ≤ j := by
        simpa only [mergePermutation_spectator, OrderEmbedding.le_iff_le] using hab
      simpa [mergeChart] using hs hij

theorem closedRectangle_antitone {m : ℕ} (L : ℝ) (X y : Fin m → ℝ) (b : Bool)
    (hy : y ∈ closedRectangle L X b) : Antitone y := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ r =>
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    cases b
    · have hl := (hy j.castSucc).1
      have hu := (hy j.succ).2
      have hj : j.val+1 < r+1 := by omega
      simp only [rectangleLower, Bool.false_eq_true, ite_false, BetheFiniteNAction.lower, Fin.val_castSucc,
        dite_eq_left hj] at hl
      simp only [rectangleUpper, Bool.false_eq_true, ite_false] at hu
      exact hu.trans hl
    · have hl := (hy j.castSucc).1
      have hu := (hy j.succ).2
      have hj : 0 < j.succ.val := by simp
      simp only [rectangleLower, ite_true] at hl
      simp only [rectangleUpper, ite_true, BetheFiniteNAction.upper, dite_eq_left hj] at hu
      exact hu.trans hl

/-- An exact closed rectangle/chart intersection; no null-set deletion. -/
theorem closedCell_iff {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (hs : Antitone s) :
    (y ∈ closedRectangle L X b ∧ y ∈ chartSet S s) ↔
      y ∈ closedRectangle L X b ∧ crossConstraints S y s := by
  rw [chartSet_iff]
  exact ⟨fun h => ⟨h.1,h.2.2.2⟩,
    fun h => ⟨h.1,closedRectangle_antitone L X y b h.1,hs,h.2⟩⟩

abbrev CellFace (m q : ℕ) := RectangleFace m ⊕ (Fin m × Fin q)

def cellFaceEquation {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) : CellFace m q → Prop
  | Sum.inl f => rectangleFaceEquation L X y b f
  | Sum.inr (i,j) => y i = s j

theorem card_cellFace (m q : ℕ) : Fintype.card (CellFace m q) = 2*m + m*q := by
  simp [CellFace, Nat.mul_comm]

/-- Exhaustion includes every corner. Labels may be redundant on empty or
lower dimensional cells; this is not a count of nondegenerate facets. -/
theorem closedCell_interior_or_face {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (hX : X ∈ BetheWavefunctions.chamber m L) (hs : StrictAnti s)
    (hy : y ∈ closedRectangle L X b) (hchart : y ∈ chartSet S s) :
    (y ∈ openRectangle L X b ∧ StrictAnti (mergeChart S y s)) ∨
      ∃ f, cellFaceEquation L X y s b f := by
  classical
  by_cases hf : ∃ f, cellFaceEquation L X y s b f
  · exact Or.inr hf
  · left
    have ho : y ∈ openRectangle L X b := by
      rcases rectangle_interior_or_face L X y b hy with h | ⟨f,hf'⟩
      · exact h
      · exact False.elim (hf ⟨Sum.inl f,hf'⟩)
    have ha : StrictAnti y := by
      cases b
      · exact BetheFiniteNAction.plusOrder_input_strictAnti ((plusOrder_openRectangle hX y).mpr ho)
      · exact BetheFiniteNAction.minusOrder_input_strictAnti ((minusOrder_openRectangle hX y).mpr ho)
    have hne : ∀ i j, y i ≠ s j := fun i j he => hf ⟨Sum.inr (i,j),he⟩
    exact ⟨ho,hchart.strictAnti_of_injective
      ((append_injective y s ha.injective hs.injective hne).comp (mergePermutation S).symm.injective)⟩

/-- At a shared closed face, both charts evaluate the identical tuple. This
is a pointwise statement suitable for primitive traces. -/
theorem chart_trace_eq {m q : ℕ} (S T : PlacementSubset m q)
    (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hS : y ∈ chartSet S s) (hT : y ∈ chartSet T s) :
    mergeChart S y s = mergeChart T y s :=
  Tuple.unique_antitone hS hT

/-- A permutation preserving a function with just one possible double
fiber is exactly the identity or the transposition of that fiber. -/
theorem preserving_perm_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a b : α) (hab : a ≠ b)
    (hf : ∀ i j, f i = f j → i = j ∨ (i = a ∧ j = b) ∨ (i = b ∧ j = a))
    (π : Equiv.Perm α) (hπ : ∀ i, f (π i) = f i) :
    π = 1 ∨ π = Equiv.swap a b := by
  have hfix (i : α) (hia : i ≠ a) (hib : i ≠ b) : π i = i := by
    rcases hf (π i) i (hπ i) with h | h | h
    · exact h
    · exact False.elim (hib h.2)
    · exact False.elim (hia h.2)
  by_cases ha : π a = a
  · left
    apply Equiv.ext
    intro i
    by_cases hia : i = a
    · simpa [hia] using ha
    by_cases hib : i = b
    · subst i
      rcases hf (π b) b (hπ b) with h | h | h
      · exact h
      · exact False.elim (hab (π.injective (ha.trans h.1.symm)))
      · exact False.elim (hab h.2.symm)
    · exact hfix i hia hib
  · right
    have ha' : π a = b := by
      rcases hf (π a) a (hπ a) with h | h | h
      · exact False.elim (ha h)
      · exact False.elim (hab h.2)
      · exact h.1
    have hb' : π b = a := by
      rcases hf (π b) b (hπ b) with h | h | h
      · exact False.elim (hab (π.injective (ha'.trans h.symm)))
      · exact h.1
      · exact False.elim (hab h.2.symm)
    apply Equiv.ext
    intro i
    by_cases hia : i = a
    · simpa [hia] using ha'
    by_cases hib : i = b
    · simpa [hib] using hb'
    · simpa [Equiv.swap_apply_of_ne_of_ne hia hib] using hfix i hia hib

/-- Existence of a merged chart does not require cross-block distinctness.
Strict order within each block is enough, including at mixed faces. -/
theorem exists_mergeChart {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) :
    ∃ S : PlacementSubset m q, y ∈ chartSet S s := by
  classical
  let x := Fin.append y s
  let τ := Tuple.sort (α := ℝᵒᵈ) x
  let σ := τ.symm
  have hsort : Antitone (x ∘ τ) := BetheExtension.decreasing_antitone x
  have hm : StrictMono (fun i : Fin m => σ (Fin.castAdd q i)) := by
    intro i j hij
    by_contra h
    have hv := hsort (le_of_not_gt h)
    simp only [Function.comp_apply, σ, Equiv.apply_symm_apply, x, Fin.append_left] at hv
    exact (not_le_of_gt (hy hij)) hv
  have hq : StrictMono (fun i : Fin q => σ (Fin.natAdd m i)) := by
    intro i j hij
    by_contra h
    have hv := hsort (le_of_not_gt h)
    simp only [Function.comp_apply, σ, Equiv.apply_symm_apply, x, Fin.append_right] at hv
    exact (not_le_of_gt (hs hij)) hv
  let S := placementSubsetOfPerm (p := m) (q := q) σ
  have he := mergePermutation_unique S σ rfl hm hq
  refine ⟨S,?_⟩
  change Antitone (x ∘ (mergePermutation S).symm)
  rw [← he]
  exact hsort

/-- Any permutation producing a closed merged chamber is the unique
order-preserving representative of its selected-image subset. -/
theorem sorting_perm_merge {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (σ : Equiv.Perm (Fin (m+q)))
    (hσ : Antitone (Fin.append y s ∘ σ.symm)) :
    σ = mergePermutation (placementSubsetOfPerm (p := m) (q := q) σ) := by
  apply mergePermutation_unique _ σ rfl
  · intro i j hij
    by_contra h
    have hv := hσ (le_of_not_gt h)
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Fin.append_left] at hv
    exact (not_le_of_gt (hy hij)) hv
  · intro i j hij
    by_contra h
    have hv := hσ (le_of_not_gt h)
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Fin.append_right] at hv
    exact (not_le_of_gt (hs hij)) hv

/-- The only ambiguity of sorting a tuple with one double fiber is the
transposition of those two original input labels. -/
theorem sorting_perm_eq_or_swap {N : ℕ} (f : Fin N → ℝ) (a b : Fin N) (hab : a ≠ b)
    (hf : ∀ i j, f i = f j → i = j ∨ (i = a ∧ j = b) ∨ (i = b ∧ j = a))
    (σ τ : Equiv.Perm (Fin N)) (hσ : Antitone (f ∘ σ.symm))
    (hτ : Antitone (f ∘ τ.symm)) : τ = σ ∨ τ = σ * Equiv.swap a b := by
  have he : f ∘ σ.symm = f ∘ τ.symm := Tuple.unique_antitone hσ hτ
  let π : Equiv.Perm (Fin N) := τ.trans σ.symm
  have hp : ∀ i, f (π i) = f i := by
    intro i
    simpa [π, Function.comp_apply] using congrFun he (τ i)
  rcases preserving_perm_eq f a b hab hf π hp with h | h
  · left
    apply Equiv.ext
    intro i
    have hi := congrArg (fun e : Equiv.Perm (Fin N) => σ (e i)) h
    simpa [π] using hi
  · right
    apply Equiv.ext
    intro i
    have hi := congrArg (fun e : Equiv.Perm (Fin N) => σ (e i)) h
    simpa [π, Equiv.Perm.mul_apply] using hi

/-- Explicit geometric hypothesis: only the displayed mixed pair coincides.
It excludes higher corners, without supplying any cancellation identity. -/
def singleCollision {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (i : Fin m) (j : Fin q) : Prop :=
  y i = s j ∧ ∀ k l, y k = s l → k = i ∧ l = j

theorem append_single_fiber {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (i : Fin m) (j : Fin q)
    (hc : singleCollision y s i j) :
    ∀ a b, Fin.append y s a = Fin.append y s b →
      a = b ∨ (a = Fin.castAdd q i ∧ b = Fin.natAdd m j) ∨
        (a = Fin.natAdd m j ∧ b = Fin.castAdd q i) := by
  intro a b
  refine Fin.addCases (fun k => ?_) (fun k => ?_) a <;>
    refine Fin.addCases (fun l => ?_) (fun l => ?_) b <;> intro h
  · exact Or.inl (congrArg (Fin.castAdd q) (hy.injective (by simpa using h)))
  · obtain ⟨rfl,rfl⟩ := hc.2 k l (by simpa using h)
    exact Or.inr (Or.inl ⟨rfl,rfl⟩)
  · obtain ⟨rfl,rfl⟩ := hc.2 l k (by simpa using h.symm)
    exact Or.inr (Or.inr ⟨rfl,rfl⟩)
  · exact Or.inl (congrArg (Fin.natAdd m) (hs.injective (by simpa using h)))

/-- Exactly two actual merged chart incidences at a simple mixed face.
The second chart is obtained by swapping the original colliding labels,
not by attaching an assumed multiplicity to an abstract face. -/
theorem singleCollision_charts {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (i : Fin m) (j : Fin q)
    (hc : singleCollision y s i j) :
    ∃ S T : PlacementSubset m q, S ≠ T ∧
      (∀ U, y ∈ chartSet U s ↔ U = S ∨ U = T) ∧
      mergePermutation T = mergePermutation S * Equiv.swap (Fin.castAdd q i) (Fin.natAdd m j) := by
  classical
  obtain ⟨S,hS⟩ := exists_mergeChart y s hy hs
  let a := Fin.castAdd q i
  let b := Fin.natAdd m j
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a,b] at this; omega
  let f := Fin.append y s
  have hf : f a = f b := by simpa [f,a,b] using hc.1
  have hswap : f ∘ Equiv.swap a b = f := by
    ext k
    by_cases hka : k = a
    · simpa [hka] using hf.symm
    by_cases hkb : k = b
    · simpa [hkb] using hf
    · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hka hkb]
  let τ := mergePermutation S * Equiv.swap a b
  have hτ : Antitone (f ∘ τ.symm) := by
    have he : f ∘ τ.symm = f ∘ (mergePermutation S).symm := by
      ext k
      change f (Equiv.swap a b ((mergePermutation S).symm k)) = _
      exact congrFun hswap ((mergePermutation S).symm k)
    rw [he]
    exact hS
  let T := placementSubsetOfPerm (p := m) (q := q) τ
  have hTperm : mergePermutation T = τ := (sorting_perm_merge y s hy hs τ hτ).symm
  have hne : S ≠ T := by
    intro h
    have he : mergePermutation S = τ := (congrArg mergePermutation h).trans hTperm
    have hv : mergePermutation S a = mergePermutation S b := by
      simpa only [τ,Equiv.Perm.mul_apply,Equiv.swap_apply_left] using
        congrArg (fun e : Equiv.Perm (Fin (m+q)) => e a) he
    exact hab ((mergePermutation S).injective hv)
  refine ⟨S,T,hne,?_,hTperm⟩
  intro U
  constructor
  · intro hU
    rcases sorting_perm_eq_or_swap f a b hab (append_single_fiber y s hy hs i j hc)
      (mergePermutation S) (mergePermutation U) hS hU with he | he
    · left
      exact (mergePermutation_image U).symm.trans
        ((congrArg (placementSubsetOfPerm (p := m) (q := q)) he).trans (mergePermutation_image S))
    · right
      have hp : mergePermutation U = mergePermutation T := he.trans hTperm.symm
      exact (mergePermutation_image U).symm.trans
        ((congrArg (placementSubsetOfPerm (p := m) (q := q)) hp).trans (mergePermutation_image T))
  · rintro (rfl | rfl)
    · exact hS
    · change Antitone (f ∘ (mergePermutation T).symm)
      rw [hTperm]
      exact hτ

def incidentCharts {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ) :
    Finset (PlacementSubset m q) := by
  classical
  exact Finset.univ.filter (fun S => y ∈ chartSet S s)

/-- Closed-chart multiplicity two, including the actual boundary point. -/
theorem card_singleCollision_charts {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (i : Fin m) (j : Fin q)
    (hc : singleCollision y s i j) :
    (incidentCharts y s).card = 2 := by
  classical
  obtain ⟨S,T,hne,hST,_⟩ := singleCollision_charts y s hy hs i j hc
  apply Finset.card_eq_two.mpr
  refine ⟨S,T,hne,?_⟩
  ext U
  simpa only [incidentCharts,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton] using hST U

/-- Interior (no mixed collision) chart multiplicity is one. -/
theorem card_noCollision_charts {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (hne : ∀ i j, y i ≠ s j) :
    (incidentCharts y s).card = 1 := by
  classical
  obtain ⟨S,hS,hu⟩ := exists_unique_mergeChart y s hy hs
    (append_injective y s hy.injective hs.injective hne)
  apply Finset.card_eq_one.mpr
  refine ⟨S,?_⟩
  ext T
  simp only [incidentCharts,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  exact ⟨fun h => hu T h,fun h => h ▸ hS⟩

def rectangleEndpoint {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool)
    (f : RectangleFace m) : ℝ :=
  if f.2 then rectangleUpper L X b f.1 else rectangleLower X b f.1

/-- All endpoint values are selected output values or the physical 0/L
boundary; there is no unlisted endpoint value. -/
theorem rectangleEndpoint_values {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool)
    (f : RectangleFace m) :
    (∃ i, rectangleEndpoint L X b f = X i) ∨
      rectangleEndpoint L X b f = 0 ∨ rectangleEndpoint L X b f = L := by
  simp only [rectangleEndpoint,rectangleUpper,rectangleLower]
  unfold BetheFiniteNAction.upper BetheFiniteNAction.lower
  split_ifs
  · left; exact ⟨_,rfl⟩
  · right; right; rfl
  · left; exact ⟨_,rfl⟩
  · left; exact ⟨_,rfl⟩
  · left; exact ⟨_,rfl⟩
  · right; left; rfl

/-- Physical selected-output endpoints never equal a spectator output,
including the adjacent selected endpoints and the two exterior ones. -/
theorem physical_endpoint_ne_spectator {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : x ∈ BetheWavefunctions.chamber (m+q) L) (S : PlacementSubset m q)
    (b : Bool) (f : RectangleFace m) (j : Fin q) :
    rectangleEndpoint L (fun i => x (selectedRank S i)) b f ≠ x (spectatorRank S j) := by
  have hne (i : Fin m) : selectedRank S i ≠ spectatorRank S j := by
    intro h
    have he := congrArg Fin.val ((mergePermutation S).injective h)
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he
    omega
  rcases rectangleEndpoint_values L (fun i => x (selectedRank S i)) b f with ⟨i,he⟩ | he | he
  · rw [he]
    exact fun h => hne i (hx.1.injective h)
  · rw [he]
    exact ne_of_lt (hx.2 _).1
  · rw [he]
    exact ne_of_gt (hx.2 _).2

/-- A double value of an antitone tuple occupies adjacent ranks. -/
theorem double_fiber_adjacent {N : ℕ} (x : Fin N → ℝ) (hx : Antitone x)
    (a b : Fin N) (hab : a < b) (he : x a = x b)
    (hf : ∀ k, x k = x a → k = a ∨ k = b) : b.val = a.val+1 := by
  have ha : a.val+1 < N := by have := b.isLt; change a.val < b.val at hab; omega
  let k : Fin N := ⟨a.val+1,ha⟩
  have hak : a ≤ k := by change a.val ≤ a.val+1; omega
  have hkb : k ≤ b := by change a.val+1 ≤ b.val; change a.val < b.val at hab; omega
  have hk : x k = x a := le_antisymm (hx hak) (he ▸ hx hkb)
  rcases hf k hk with h | h
  · have hv := congrArg Fin.val h
    dsimp [k] at hv
    omega
  · have hv := congrArg Fin.val h
    exact hv.symm

/-- The two colliding input labels occupy precisely an adjacent chamber
face, in one of its two orientations. No adjacency is assumed. -/
theorem singleCollision_adjacent {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (i : Fin m) (j : Fin q)
    (hc : singleCollision y s i j) (S : PlacementSubset m q)
    (hS : y ∈ chartSet S s) :
    (spectatorRank S j).val = (selectedRank S i).val+1 ∨
      (selectedRank S i).val = (spectatorRank S j).val+1 := by
  let a := selectedRank S i
  let b := spectatorRank S j
  let x := mergeChart S y s
  have he : x a = x b := by simpa [x,a,b,mergeChart_selected,mergeChart_spectator] using hc.1
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val ((mergePermutation S).injective h)
    change i.val = m+j.val at hv
    omega
  have hf : ∀ k, x k = x a → k = a ∨ k = b := by
    intro k hk
    have hk' : Fin.append y s ((mergePermutation S).symm k) = Fin.append y s (Fin.castAdd q i) := by
      simpa [x,a,mergeChart,selectedRank] using hk
    rcases append_single_fiber y s hy hs i j hc _ _ hk' with h | h | h
    · left
      simpa [a,selectedRank] using congrArg (mergePermutation S) h
    · have hv := congrArg Fin.val h.2
      simp at hv
      omega
    · right
      simpa [b,spectatorRank] using congrArg (mergePermutation S) h.1
  rcases lt_or_gt_of_ne hab with h | h
  · exact Or.inl (double_fiber_adjacent x hS a b h he hf)
  · right
    apply double_fiber_adjacent x hS b a h he.symm
    intro k hk
    exact (hf k (hk.trans he.symm)).symm

end QuantumNLS.BetheRectangleIncidence

#print axioms QuantumNLS.BetheRectangleIncidence.selectedRank
#print axioms QuantumNLS.BetheRectangleIncidence.spectatorRank
#print axioms QuantumNLS.BetheRectangleIncidence.mergeChart_selected
#print axioms QuantumNLS.BetheRectangleIncidence.mergeChart_spectator
#print axioms QuantumNLS.BetheRectangleIncidence.crossConstraints
#print axioms QuantumNLS.BetheRectangleIncidence.chartSet_iff
#print axioms QuantumNLS.BetheRectangleIncidence.closedRectangle_antitone
#print axioms QuantumNLS.BetheRectangleIncidence.closedCell_iff
#print axioms QuantumNLS.BetheRectangleIncidence.CellFace
#print axioms QuantumNLS.BetheRectangleIncidence.cellFaceEquation
#print axioms QuantumNLS.BetheRectangleIncidence.card_cellFace
#print axioms QuantumNLS.BetheRectangleIncidence.closedCell_interior_or_face
#print axioms QuantumNLS.BetheRectangleIncidence.chart_trace_eq
#print axioms QuantumNLS.BetheRectangleIncidence.preserving_perm_eq
#print axioms QuantumNLS.BetheRectangleIncidence.exists_mergeChart
#print axioms QuantumNLS.BetheRectangleIncidence.sorting_perm_merge
#print axioms QuantumNLS.BetheRectangleIncidence.sorting_perm_eq_or_swap
#print axioms QuantumNLS.BetheRectangleIncidence.singleCollision
#print axioms QuantumNLS.BetheRectangleIncidence.append_single_fiber
#print axioms QuantumNLS.BetheRectangleIncidence.singleCollision_charts
#print axioms QuantumNLS.BetheRectangleIncidence.incidentCharts
#print axioms QuantumNLS.BetheRectangleIncidence.card_singleCollision_charts
#print axioms QuantumNLS.BetheRectangleIncidence.card_noCollision_charts
#print axioms QuantumNLS.BetheRectangleIncidence.rectangleEndpoint
#print axioms QuantumNLS.BetheRectangleIncidence.rectangleEndpoint_values
#print axioms QuantumNLS.BetheRectangleIncidence.physical_endpoint_ne_spectator
#print axioms QuantumNLS.BetheRectangleIncidence.double_fiber_adjacent
#print axioms QuantumNLS.BetheRectangleIncidence.singleCollision_adjacent
