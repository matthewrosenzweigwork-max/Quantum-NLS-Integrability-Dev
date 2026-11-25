import QuantumNLS.BetheCornerTransport

/-! Admitted labels for the literal BGE1 expansion. Endpoint assignments are
retained as labels, including zero degree and coincident endpoint values.
The collision-profile partition below does not choose a cancellation mark. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheGeneratedLabels
open TensorPlacements BetheGeneratedEndpoints BetheFaceEnumeration
open BetheRectangleIncidence BethePhysicalFaceCharts BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport
attribute [local instance] Classical.propDecidable

theorem sum_guarded {α : Type*} [Fintype α] (p : α → Prop) (f : α → ℂ) :
    (∑ a : {a // p a}, f a.1) = ∑ a : α, if p a then f a else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

abbrev BranchLabel (m q : ℕ) :=
  PlacementSubset m q × Bool × (Fin m → Bool)

/-- One input chart, branch and Boolean assignment, before its box guard. -/
def branchAdmitted {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (l : BranchLabel m q) : Prop :=
  clipLower X s l.2.1 l.1 ≤ clipUpper L X s l.2.1 l.1

/-- Literal signed BGE1 summand; there is no endpoint-provenance label. -/
def branchValue {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (l : BranchLabel m q) : ℂ :=
  let Y := cornerTuple (clipLower X s l.2.1 l.1) (clipUpper L X s l.2.1 l.1) l.2.2
  orientation l.2.2 *
    Complex.exp (Complex.I*z*((branchOffset L X l.2.1 - ∑ i, Y i : ℝ) : ℂ)) *
    BethePrimitiveTransport.chartPrimitive l.1 c (BetheSmooth.sourceRoots L n c)
      Y s z (firstPositions (p := m) (q := q))

/-- The exact guard is the nonempty-box guard already present in BGE1. -/
theorem branchAdmitted_iff_nonempty {m q : ℕ} (L : ℝ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (l : BranchLabel m q) :
    branchAdmitted L X s l ↔
      (Icc (clipLower X s l.2.1 l.1) (clipUpper L X s l.2.1 l.1)).Nonempty := by
  exact nonempty_Icc.symm

/-- No original summand is duplicated when guarded labels replace the
conditional chart sum; signs and complete primitive factors are unchanged. -/
theorem sum_branchValue {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (z : ℂ) (X : Fin m → ℝ) (s : Fin q → ℝ) :
    (∑ l : {l : BranchLabel m q // branchAdmitted L X s l},
      branchValue L c n z X s l.1) =
      ∑ T : PlacementSubset m q,
        (sourceCorners L c n z X s false T + sourceCorners L c n z X s true T) := by
  classical
  rw [sum_guarded]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro T _
  rw [Fintype.sum_bool]
  simp only [branchAdmitted, branchValue, sourceCorners]
  split_ifs <;> simp_all [add_comm]

/-- Full finite label type for a fixed ambient N. Degree zero is included.
Output and input charts are distinct data. -/
abbrev RawLabel (N : ℕ) :=
  (d : Fin (N+1)) × (PlacementSubset d.val (N-d.val) × BranchLabel d.val (N-d.val))

/-- Transport from a degree split to the original physical labels. -/
def ambient {N : ℕ} (d : Fin (N+1)) : Fin (d.val+(N-d.val)) ≃ Fin N :=
  finCongr (by omega)

def outputTuple {N : ℕ} (x : Fin N → ℝ) (l : RawLabel N) : Fin l.1.val → ℝ :=
  fun i => x (ambient l.1 (l.2.1.1.orderEmbOfFin l.2.1.2 i))

def spectatorTuple {N : ℕ} (x : Fin N → ℝ) (l : RawLabel N) : Fin (N-l.1.val) → ℝ :=
  fun j => x (ambient l.1 (l.2.1.1ᶜ.orderEmbOfFin (complement_card l.2.1) j))

def admitted {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) : Prop :=
  branchAdmitted L (outputTuple x l) (spectatorTuple x l) l.2.2

abbrev Label {N : ℕ} (L : ℝ) (x : Fin N → ℝ) :=
  {l : RawLabel N // admitted L x l}

/-- Includes exactly c^m per original ordered output subset. -/
def value {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) (l : RawLabel N) : ℂ :=
  (c : ℂ)^l.1.val * branchValue L c (n ∘ ambient l.1) z
    (outputTuple x l) (spectatorTuple x l) l.2.2

/-- Full signed expansion, over every degree and both sets of chart labels.
The RHS is the original BGE1 conditional corner sum with its exact c^m. -/
theorem sum_value {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ) (x : Fin N → ℝ) :
    (∑ l : Label L x, value L c n z x l.1) =
      ∑ d : Fin (N+1), (c : ℂ)^d.val *
        ∑ S : PlacementSubset d.val (N-d.val),
          let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
          let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
          ∑ T : PlacementSubset d.val (N-d.val),
            (sourceCorners L c (n ∘ ambient d) z X s false T +
            sourceCorners L c (n ∘ ambient d) z X s true T) := by
  classical
  rw [sum_guarded, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  dsimp only
  rw [← sum_branchValue, sum_guarded, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  dsimp only [admitted, outputTuple, spectatorTuple, value]
  simp only [mul_ite, mul_zero]
  rfl

/-- All local assignments survive as separate labels even if their values
coincide. Empty boxes instead have no admitted labels. -/
theorem card_branchLabels {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ) :
    Fintype.card {l : BranchLabel m q // branchAdmitted L X s l} =
      ∑ T : PlacementSubset m q, ∑ b : Bool,
        if clipLower X s b T ≤ clipUpper L X s b T then 2^m else 0 := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, branchAdmitted]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

/-- Admission is also an explicit dependent enumeration with an inverse at
all degrees; proof fields do not introduce additional labels. -/
def enumerationEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ) :
    Label L x ≃ ((d : Fin (N+1)) ×
      (S : PlacementSubset d.val (N-d.val)) ×
      {l : BranchLabel d.val (N-d.val) //
        branchAdmitted L
          (fun i => x (ambient d (S.1.orderEmbOfFin S.2 i)))
          (fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))) l}) where
  toFun l := ⟨l.1.1, l.1.2.1, l.1.2.2, l.2⟩
  invFun l := ⟨⟨l.1, l.2.1, l.2.2.1⟩, l.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Literal corner coordinates, with no selection of endpoint provenance. -/
def coordinates {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) : Fin l.1.val → ℝ :=
  cornerTuple (clipLower (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1)
    (clipUpper L (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1) l.2.2.2.2

/-- Every possible mixed collision, in the original physical output labels.
This set records all candidates simultaneously; it is not a list of copies
of the summand, and an empty set retains exterior candidates. -/
def collisionProfile {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) :
    Finset (Fin N × Fin N) :=
  (Finset.univ.filter (fun p : Fin l.1.val × Fin (N-l.1.val) =>
    coordinates L x l p.1 = spectatorTuple x l p.2)).image (fun p =>
      (ambient l.1 (l.2.1.1.orderEmbOfFin l.2.1.2 p.1),
       ambient l.1 (l.2.1.1ᶜ.orderEmbOfFin (complement_card l.2.1) p.2)))

theorem mem_collisionProfile {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (l : RawLabel N) (a t : Fin N) :
    (a,t) ∈ collisionProfile L x l ↔
      ∃ i j, coordinates L x l i = spectatorTuple x l j ∧
        ambient l.1 (l.2.1.1.orderEmbOfFin l.2.1.2 i) = a ∧
        ambient l.1 (l.2.1.1ᶜ.orderEmbOfFin (complement_card l.2.1) j) = t := by
  simp [collisionProfile, Prod.exists]

/-- An exhaustive decomposition by the complete candidate set. Each admitted
label occurs once, including the no-collision stratum and coincident corners.
This inverse does not yet regroup strata into BCT1 cancellation triples. -/
def profileEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ) :
    ((P : Finset (Fin N × Fin N)) ×
      {l : Label L x // collisionProfile L x l.1 = P}) ≃ Label L x :=
  Equiv.sigmaFiberEquiv (fun l : Label L x => collisionProfile L x l.1)

theorem profileEquiv_inverse {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : Label L x) :
    (profileEquiv L x).symm l = ⟨collisionProfile L x l.1, l, rfl⟩ := rfl

/-- Exact signed sum over the strata, retaining every actual BGE1 weight. -/
theorem sum_profiles {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ) (x : Fin N → ℝ) :
    (∑ l : Label L x, value L c n z x l.1) =
      ∑ P : Finset (Fin N × Fin N),
        ∑ l : {l : Label L x // collisionProfile L x l.1 = P},
          value L c n z x l.1.1 := by
  calc
    _ = ∑ p : ((P : Finset (Fin N × Fin N)) ×
        {l : Label L x // collisionProfile L x l.1 = P}),
        value L c n z x p.2.1.1 :=
      ((profileEquiv L x).sum_comp (fun l => value L c n z x l.1)).symm
    _ = _ := by rw [Fintype.sum_sigma]

/-- Counting every eligible mark without a compatible partition introduces
exactly this multiplicity. No division by the number of marks is inserted. -/
theorem sum_all_marks {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ) (x : Fin N → ℝ) :
    (∑ l : Label L x, ∑ _p ∈ collisionProfile L x l.1, value L c n z x l.1) =
      ∑ l : Label L x, ((collisionProfile L x l.1).card : ℂ) * value L c n z x l.1 := by
  apply Finset.sum_congr rfl
  intro l _
  simp

/-- Admission supplies an actual physical cell witness at the generated
corner. No strictness of moving coordinates or generic-corner premise. -/
theorem admitted_corner_cell {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l) :
    let X := fun i => x (S.1.orderEmbOfFin S.2 i)
    let s := fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)
    let Y := cornerTuple (clipLower X s l.2.1 l.1) (clipUpper L X s l.2.1 l.1) l.2.2
    physicalCell L x S.1 (inputOrdering S l.1) l.2.1 (mergeChart S Y s) := by
  dsimp only
  rw [physicalCell_iff_actual L x _ hx.antitone (fun k => ⟨(hb k).1.le,(hb k).2.le⟩)]
  have he (Y : Fin m → ℝ) (s : Fin q → ℝ) :
      (fun i => mergeChart S Y s (S.1.orderEmbOfFin S.2 i)) = Y := by
    funext i
    rw [← mergePermutation_selected S i]
    exact mergeChart_selected S Y s i
  rw [he, closedPhysicalCell_eq_box L _ _ l.2.1 l.1
    ⟨fun _ _ h => hx ((S.1.orderEmbOfFin S.2).strictMono h), fun _ => hb _⟩
    (fun _ _ h => hx.antitone ((S.1ᶜ.orderEmbOfFin (complement_card S)).monotone h))
    (fun _ => ⟨(hb _).1.le,(hb _).2.le⟩)]
  exact cornerTuple_mem_box _ _ hl l.2.2

/-- Every mixed candidate at an admitted corner has the actual BIA1
branch-oriented physical gap and consecutive input ranks. -/
theorem admitted_collision_gap_adjacent {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l)
    (i : Fin m) (j : Fin q)
    (he : cornerTuple
      (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1)
      (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1) l.2.2 i =
      x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) :
    let a := S.1.orderEmbOfFin S.2 i
    let t := S.1ᶜ.orderEmbOfFin (complement_card S) j
    let π := inputOrdering S l.1
    internalGap S.1 a t l.2.1 ∧
      ((π t).val = (π a).val+1 ∨ (π a).val = (π t).val+1) := by
  dsimp only
  have hy := admitted_corner_cell L x hx hb S l hl
  dsimp only at hy
  have ha := S.1.orderEmbOfFin_mem S.2 i
  have ht := Finset.mem_compl.mp (S.1ᶜ.orderEmbOfFin_mem (complement_card S) j)
  let X := fun i => x (S.1.orderEmbOfFin S.2 i)
  let s := fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)
  let Y := cornerTuple (clipLower X s l.2.1 l.1) (clipUpper L X s l.2.1 l.1) l.2.2
  have hc : mergeChart S Y s (S.1.orderEmbOfFin S.2 i) =
      x (S.1ᶜ.orderEmbOfFin (complement_card S) j) := by
    rw [← mergePermutation_selected S i]
    exact (mergeChart_selected S Y s i).trans he
  exact ⟨collision_internalGap L x _ hx S.1 _ _ l.2.1 hy.1 ha ht hc,
    mixed_collision_adjacent L x _ hx S.1 _ _ l.2.1 hy.1 ha ht hc _ hy.2⟩

/-- Zero degree has the unique empty Boolean assignment and a vacuous guard. -/
theorem admitted_zero {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N)
    (hd : l.1.val = 0) : admitted L x l := by
  intro i
  have hi := i.isLt
  omega

theorem collisionProfile_zero {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N)
    (hd : l.1.val = 0) : collisionProfile L x l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨i,j,_,_,_⟩ := (mem_collisionProfile L x l p.1 p.2).mp hp
  have hi := i.isLt
  omega

theorem collisionProfile_full {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N)
    (hd : l.1.val = N) : collisionProfile L x l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨i,j,_,_,_⟩ := (mem_collisionProfile L x l p.1 p.2).mp hp
  have hj := j.isLt
  omega

/-- Toggle one original Boolean label; this is an involution with no fixed
assignment, even if its evaluated endpoint coordinates coincide. -/
def flipEquiv {m : ℕ} (i : Fin m) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun ε := Function.update ε i (!(ε i))
  invFun ε := Function.update ε i (!(ε i))
  left_inv ε := by ext j; by_cases hj : j = i <;> simp [hj]
  right_inv ε := by ext j; by_cases hj : j = i <;> simp [hj]

theorem flipEquiv_ne {m : ℕ} (i : Fin m) (ε : Fin m → Bool) : flipEquiv i ε ≠ ε := by
  intro h
  have hi := congrFun h i
  change Function.update ε i (!(ε i)) i = ε i at hi
  simp only [Function.update_self] at hi
  cases ε i <;> simp_all

theorem orientation_flip {m : ℕ} (i : Fin m) (ε : Fin m → Bool) :
    orientation (flipEquiv i ε) = -orientation ε := by
  change orientation (Function.update ε i (!(ε i))) = -orientation ε
  simpa only [physicalOrientation, orientation] using
    physicalOrientation_flip Finset.univ i (Finset.mem_univ i) ε

theorem cornerTuple_flip {m : ℕ} (lo hi : Fin m → ℝ) (i : Fin m)
    (h : lo i = hi i) (ε : Fin m → Bool) :
    cornerTuple lo hi (flipEquiv i ε) = cornerTuple lo hi ε := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [cornerTuple, flipEquiv, h]
  · simp [cornerTuple, flipEquiv, hj]

/-- Signed collapsed-corner pairing preserves the entire primitive, phase
and pending denominator set, and only reverses the endpoint orientation. -/
theorem branchValue_flip {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (T : PlacementSubset m q) (b : Bool)
    (i : Fin m) (h : clipLower X s b T i = clipUpper L X s b T i)
    (ε : Fin m → Bool) :
    branchValue L c n z X s (T,b,flipEquiv i ε) =
      -branchValue L c n z X s (T,b,ε) := by
  dsimp only [branchValue]
  rw [orientation_flip, cornerTuple_flip _ _ i h]
  ring

/-- Empty boxes contribute no labels; a collapsed nonempty chart keeps all
labels and its signed Boolean sum is proved zero by an explicit involution. -/
theorem sum_collapsed_branch {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (T : PlacementSubset m q) (b : Bool)
    (i : Fin m) (h : clipLower X s b T i = clipUpper L X s b T i) :
    (∑ ε : Fin m → Bool, branchValue L c n z X s (T,b,ε)) = 0 := by
  have he := (flipEquiv i).sum_comp (fun ε => branchValue L c n z X s (T,b,ε))
  simp_rw [branchValue_flip L c n z X s T b i h] at he
  rw [Finset.sum_neg_distrib] at he
  linear_combination (-1/2 : ℂ) * he


open TensorCarrier PhysicalTensor BetheHigherPlacement BetheGeneralSliceEndpoints
open BetheTransferKernelAdjoint BetheWeakGradient BetheFiniteNAction

/-- The admitted branch labels evaluate each actual positive-c physical
term, using BGE1's proved action with its inherited exact (N)_m coefficient. -/
theorem source_transferTerm_labels_ae (L : ℝ) [Fact (0 < L)]
    (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c) {n : Fin (m+q) → ℤ}
    (hn : Antitone n) (z : ℂ)
    (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), StrictAnti (representatives L x) →
      physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
        (sourceVector L hc hn)).1) x = (c : ℂ)^m *
        ∑ S : PlacementSubset m q,
          let X := fun j => representatives L x (S.1.orderEmbOfFin S.2 j)
          let s := fun j => representatives L x (S.1ᶜ.orderEmbOfFin (complement_card S) j)
          ∑ l : {l : BranchLabel m q // branchAdmitted L X s l},
            branchValue L c n z X s l.1 := by
  filter_upwards [source_transferTerm_corners_ae L m q hm hc hn z hz] with x he hx
  rw [he hx]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  dsimp only
  rw [sum_branchValue]
  simp only [mergePermutation_selected, mergePermutation_spectator]

end QuantumNLS.BetheGeneratedLabels


#print axioms QuantumNLS.BetheGeneratedLabels.sum_guarded
#print axioms QuantumNLS.BetheGeneratedLabels.BranchLabel
#print axioms QuantumNLS.BetheGeneratedLabels.branchAdmitted
#print axioms QuantumNLS.BetheGeneratedLabels.branchValue
#print axioms QuantumNLS.BetheGeneratedLabels.branchAdmitted_iff_nonempty
#print axioms QuantumNLS.BetheGeneratedLabels.sum_branchValue
#print axioms QuantumNLS.BetheGeneratedLabels.RawLabel
#print axioms QuantumNLS.BetheGeneratedLabels.ambient
#print axioms QuantumNLS.BetheGeneratedLabels.outputTuple
#print axioms QuantumNLS.BetheGeneratedLabels.spectatorTuple
#print axioms QuantumNLS.BetheGeneratedLabels.admitted
#print axioms QuantumNLS.BetheGeneratedLabels.Label
#print axioms QuantumNLS.BetheGeneratedLabels.value
#print axioms QuantumNLS.BetheGeneratedLabels.sum_value
#print axioms QuantumNLS.BetheGeneratedLabels.card_branchLabels
#print axioms QuantumNLS.BetheGeneratedLabels.enumerationEquiv
#print axioms QuantumNLS.BetheGeneratedLabels.coordinates
#print axioms QuantumNLS.BetheGeneratedLabels.collisionProfile
#print axioms QuantumNLS.BetheGeneratedLabels.mem_collisionProfile
#print axioms QuantumNLS.BetheGeneratedLabels.profileEquiv
#print axioms QuantumNLS.BetheGeneratedLabels.profileEquiv_inverse
#print axioms QuantumNLS.BetheGeneratedLabels.sum_profiles
#print axioms QuantumNLS.BetheGeneratedLabels.sum_all_marks
#print axioms QuantumNLS.BetheGeneratedLabels.admitted_corner_cell
#print axioms QuantumNLS.BetheGeneratedLabels.admitted_collision_gap_adjacent
#print axioms QuantumNLS.BetheGeneratedLabels.admitted_zero
#print axioms QuantumNLS.BetheGeneratedLabels.collisionProfile_zero
#print axioms QuantumNLS.BetheGeneratedLabels.collisionProfile_full
#print axioms QuantumNLS.BetheGeneratedLabels.flipEquiv
#print axioms QuantumNLS.BetheGeneratedLabels.flipEquiv_ne
#print axioms QuantumNLS.BetheGeneratedLabels.orientation_flip
#print axioms QuantumNLS.BetheGeneratedLabels.cornerTuple_flip
#print axioms QuantumNLS.BetheGeneratedLabels.branchValue_flip
#print axioms QuantumNLS.BetheGeneratedLabels.sum_collapsed_branch
#print axioms QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheGeneratedLabels.sum_guarded,
    ``QuantumNLS.BetheGeneratedLabels.BranchLabel,
    ``QuantumNLS.BetheGeneratedLabels.branchAdmitted,
    ``QuantumNLS.BetheGeneratedLabels.branchValue,
    ``QuantumNLS.BetheGeneratedLabels.branchAdmitted_iff_nonempty,
    ``QuantumNLS.BetheGeneratedLabels.sum_branchValue,
    ``QuantumNLS.BetheGeneratedLabels.RawLabel,
    ``QuantumNLS.BetheGeneratedLabels.ambient,
    ``QuantumNLS.BetheGeneratedLabels.outputTuple,
    ``QuantumNLS.BetheGeneratedLabels.spectatorTuple,
    ``QuantumNLS.BetheGeneratedLabels.admitted,
    ``QuantumNLS.BetheGeneratedLabels.Label,
    ``QuantumNLS.BetheGeneratedLabels.value,
    ``QuantumNLS.BetheGeneratedLabels.sum_value,
    ``QuantumNLS.BetheGeneratedLabels.card_branchLabels,
    ``QuantumNLS.BetheGeneratedLabels.enumerationEquiv,
    ``QuantumNLS.BetheGeneratedLabels.coordinates,
    ``QuantumNLS.BetheGeneratedLabels.collisionProfile,
    ``QuantumNLS.BetheGeneratedLabels.mem_collisionProfile,
    ``QuantumNLS.BetheGeneratedLabels.profileEquiv,
    ``QuantumNLS.BetheGeneratedLabels.profileEquiv_inverse,
    ``QuantumNLS.BetheGeneratedLabels.sum_profiles,
    ``QuantumNLS.BetheGeneratedLabels.sum_all_marks,
    ``QuantumNLS.BetheGeneratedLabels.admitted_corner_cell,
    ``QuantumNLS.BetheGeneratedLabels.admitted_collision_gap_adjacent,
    ``QuantumNLS.BetheGeneratedLabels.admitted_zero,
    ``QuantumNLS.BetheGeneratedLabels.collisionProfile_zero,
    ``QuantumNLS.BetheGeneratedLabels.collisionProfile_full,
    ``QuantumNLS.BetheGeneratedLabels.flipEquiv,
    ``QuantumNLS.BetheGeneratedLabels.flipEquiv_ne,
    ``QuantumNLS.BetheGeneratedLabels.orientation_flip,
    ``QuantumNLS.BetheGeneratedLabels.cornerTuple_flip,
    ``QuantumNLS.BetheGeneratedLabels.branchValue_flip,
    ``QuantumNLS.BetheGeneratedLabels.sum_collapsed_branch,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance]
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
    ``QuantumNLS.BetheGeneratedEndpoints.source_transferTerm_corners_ae,
    ``QuantumNLS.BetheGeneratedEndpoints.sourceCorners,
    ``QuantumNLS.BetheGeneratedEndpoints.clipLower,
    ``QuantumNLS.BetheGeneratedEndpoints.clipUpper,
    ``QuantumNLS.BetheGeneratedEndpoints.closedPhysicalCell_eq_box,
    ``QuantumNLS.BetheInputAdjacency.collision_internalGap,
    ``QuantumNLS.BetheInputAdjacency.mixed_collision_adjacent,
    ``QuantumNLS.BetheCornerTransport.physicalCell_iff_actual,
    ``QuantumNLS.BetheCornerTransport.physicalOrientation_flip,
    ``QuantumNLS.BetheInputAdjacency.source_promoted_face_balance_of_chart,
    ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Generated label aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Generated label aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Generated label aggregate audit PASS: {seen.size} transitive constants across separate roots. Full admitted all-degree labels, exact BGE1 signed expression, complete enumeration/profile inverses, cardinal mark overcount, actual mixed-collision geometry, collapsed sign involution and actual positive-c per-degree action. The inherited fixed-mark triple is a separate root. Compatible cancellation-triple decomposition, global sums and spectral assembly remain OPEN."
