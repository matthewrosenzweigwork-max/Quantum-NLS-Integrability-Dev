import QuantumNLS.BetheStrictLabelStrata
import Mathlib.Data.Fintype.Sum

/-! Disjoint original-label arms at a chosen full-profile seam. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheTripleStrata
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
attribute [local instance] Classical.propDecidable

/-- Sort the branch-oriented moving/spectator pair into the full-profile mark. -/
def seamMark {N : ℕ} (b : Bool) (a t : Fin N) : Fin N × Fin N :=
  if b then (t,a) else (a,t)

abbrev FirstLower {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (a t : Fin N) (b : Bool) :=
  {l : MixedStratum L x (seamMark b a t) a t //
    l.1.2.2.2.1 = b ∧ booleans l.1 a = b}

abbrev SecondLower {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (a t : Fin N) (b : Bool) :=
  {l : MixedStratum L x (seamMark b a t) a t //
    l.1.2.2.2.1 = b ∧ booleans l.1 a = !b}

abbrev Higher {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (a t : Fin N) (b : Bool) :=
  {l : RawLabel N // admitted L x l ∧ labelMark L x l = some (seamMark b a t) ∧
    l.2.2.2.1 = b ∧ a ∈ outputSet l ∧ t ∈ outputSet l ∧
    fullInput L x l a = fullInput L x l t}

abbrev SeamStratum {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (a t : Fin N) (b : Bool) :=
  {l : RawLabel N // admitted L x l ∧ labelMark L x l = some (seamMark b a t) ∧
    l.2.2.2.1 = b}

/-- The BSL1 lower exchange restricted to an actual fixed branch. -/
def lowerEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool) :
    FirstLower L x a t b ≃ SecondLower L x a t b where
  toFun l := ⟨mixedExchange L x hx hb (seamMark b a t) a t l.1, by
    have h := mixedExchange_orientation L x hx hb (seamMark b a t) a t l.1
    exact ⟨h.2.trans l.2.1,by rw [h.1,l.2.2]⟩⟩
  invFun l := ⟨mixedExchange L x hx hb (seamMark b a t) a t l.1, by
    have h := mixedExchange_orientation L x hx hb (seamMark b a t) a t l.1
    exact ⟨h.2.trans l.2.1,by rw [h.1,l.2.2]; simp⟩⟩
  left_inv l := Subtype.ext (mixedExchange_involutive L x hx hb (seamMark b a t) a t l.1)
  right_inv l := Subtype.ext (mixedExchange_involutive L x hx hb (seamMark b a t) a t l.1)

/-- Original first-lower promotion, retaining every simultaneous seam. -/
def raise {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (l : FirstLower L x a t b) : Higher L x a t b := by
  have hp := (mixed_incident_iff L x hx hb l.1.1 l.1.2.1 a t
    l.1.2.2.2.1 l.1.2.2.2.2.1 l.1.2.2.2.2.2).mpr (l.2.2.trans l.2.1.symm)
  have hs := promoteLabel_supported L x hx hb l.1.1 l.1.2.1 a t
    l.1.2.2.2.1 l.1.2.2.2.2.1 l.1.2.2.2.2.2 (l.2.2.trans l.2.1.symm) hp
  refine ⟨promoteLabel l.1.1 t hp,hs.1,hs.2.2.trans l.1.2.2.1,l.2.1,?_,?_,?_⟩
  · rw [(promoteLabel_data _ _ _).1]; exact Finset.mem_insert_of_mem l.1.2.2.2.1
  · rw [(promoteLabel_data _ _ _).1]; exact Finset.mem_insert_self _ _
  · rw [hs.2.1,l.1.2.2.2.2.2]
    rw [label_corner L x hx hb l.1.1 l.1.2.1]
    simp [physicalCorner,l.1.2.2.2.2.1]

/-- Support forces the two higher endpoint labels and their pinned value. -/
theorem higher_pinned {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : Higher L x a t b) :
    fullInput L x l.1 a = x t ∧ fullInput L x l.1 t = x t ∧
    booleans l.1 a = b ∧ booleans l.1 t = !b := by
  have hy := label_cell L x hx hb l.1 l.2.1
  have hna := label_physical_strict L x hx hb l.1 l.2.1 a l.2.2.2.2.1
  have hnt := label_physical_strict L x hx hb l.1 l.2.1 t l.2.2.2.2.2.1
  by_cases heq : b = false
  · simp only [heq,Bool.false_eq_true,ite_false] at ho ⊢
    have hg := selected_collision_gap L x _ hx _ l.1.2.2.2.1 hy.1 a t
      l.2.2.2.2.1 l.2.2.2.2.2.1 ho l.2.2.2.2.2.2
    have heps := label_selected_orientations L x hx hb l.1 l.2.1 a t
      l.2.2.2.2.1 l.2.2.2.2.2.1 ho l.2.2.2.2.2.2 hna hnt
    simp only [l.2.2.2.1,heq,Bool.false_eq_true,ite_false] at hg
    simpa using And.intro hg.2.1 (And.intro hg.2.2 heps)
  · have heq : b = true := by cases b <;> simp_all
    simp only [heq,ite_true] at ho ⊢
    have hg := selected_collision_gap L x _ hx _ l.1.2.2.2.1 hy.1 t a
      l.2.2.2.2.2.1 l.2.2.2.2.1 ho l.2.2.2.2.2.2.symm
    have heps := label_selected_orientations L x hx hb l.1 l.2.1 t a
      l.2.2.2.2.2.1 l.2.2.2.2.1 ho l.2.2.2.2.2.2.symm hnt hna
    simp only [l.2.2.2.1,heq,ite_true] at hg
    simpa using And.intro hg.2.1 (And.intro hg.2.2 (And.intro heps.2 heps.1))

/-- Demotion is defined for every actual higher label in this stratum. -/
theorem higher_demotable {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : Higher L x a t b) :
    ∃ hp : orderedBlocks ((outputSet l.1).erase t) (ordering l.1),
      admitted L x (demoteLabel l.1 t hp) ∧
      fullInput L x (demoteLabel l.1 t hp) = fullInput L x l.1 ∧
      labelMark L x (demoteLabel l.1 t hp) = labelMark L x l.1 := by
  have h := selected_seam_demote_strict L x hx hb l.1 l.2.1
  by_cases heq : b = false
  · have h' := h a t l.2.2.2.2.1 l.2.2.2.2.2.1 (by simpa [heq] using ho)
      l.2.2.2.2.2.2
    simp only [l.2.2.2.1,heq,Bool.false_eq_true,ite_false] at h'
    obtain ⟨hp,ha,hv,hm,_⟩ := h'; exact ⟨hp,ha,hv,hm⟩
  · have heq : b = true := by cases b <;> simp_all
    have h' := h t a l.2.2.2.2.2.1 l.2.2.2.2.1 (by simpa [heq] using ho)
      l.2.2.2.2.2.2.symm
    simp only [l.2.2.2.1,heq,ite_true] at h'
    obtain ⟨hp,ha,hv,hm,_⟩ := h'; exact ⟨hp,ha,hv,hm⟩

/-- Literal original higher-to-first-lower map; no arbitrary chart choice. -/
def lower {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : Higher L x a t b) : FirstLower L x a t b := by
  let h := higher_demotable L x hx hb a t b ho l
  let hp := h.choose
  have hs := h.choose_spec
  have hat : a ≠ t := by
    intro he; rw [he] at ho; simp at ho
  have ha : a ∈ (outputSet l.1).erase t := Finset.mem_erase.mpr ⟨hat,l.2.2.2.2.1⟩
  have hpin := higher_pinned L x hx hb a t b ho l
  refine ⟨⟨demoteLabel l.1 t hp,hs.1,hs.2.2.trans l.2.2.1,?_,?_,?_⟩,?_,?_⟩
  · rw [(demoteLabel_data _ _ _).1]; exact ha
  · rw [(demoteLabel_data _ _ _).1]; exact Finset.notMem_erase _ _
  · rw [hs.2.1]; exact hpin.1
  · exact l.2.2.2.1
  · simpa only [demoteLabel,reconstruct_booleans,ha,ite_true] using hpin.2.2.1

/-- The actual two cross-degree maps are inverse on all supported arms. -/
def higherEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) : FirstLower L x a t b ≃ Higher L x a t b where
  toFun := raise L x hx hb a t b
  invFun := lower L x hx hb a t b ho
  left_inv l := by
    apply Subtype.ext; apply Subtype.ext
    dsimp only [lower,raise]
    apply demote_promote_inverse
    exact l.1.2.2.2.2.1
  right_inv l := by
    apply Subtype.ext
    dsimp only [lower,raise]
    apply promote_demote_inverse
    · exact l.2.2.2.2.2.1
    · exact (higher_pinned L x hx hb a t b ho l).2.2.2.trans (congrArg Bool.not l.2.2.2.1.symm)

/-- Every chosen mark is the actual sorted full-input coincidence. -/
theorem marked_input_eq {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (a t : Fin N) (b : Bool) (l : SeamStratum L x a t b) :
    fullInput L x l.1 a = fullInput L x l.1 t := by
  have hm : seamMark b a t ∈ seams (fullInput L x l.1) :=
    chooseSeam_mem (labelProfile L x l.1) (seamMark b a t) l.2.2.1
  by_cases h : b = false
  · have hs : seamMark b a t = (a,t) := by simp [seamMark,h]
    have hm' := (congrArg (fun q : Fin N × Fin N => q ∈ seams (fullInput L x l.1)) hs).mp hm
    exact ((mem_seams _ a t).mp hm').2
  · have h : b = true := by cases b <;> simp_all
    have hs : seamMark b a t = (t,a) := by simp [seamMark,h]
    have hm' := (congrArg (fun q : Fin N × Fin N => q ∈ seams (fullInput L x l.1)) hs).mp hm
    exact ((mem_seams _ t a).mp hm').2.symm

/-- The branch forces which member of the chosen pair is selected.
The opposite moving/spectator direction is excluded by actual support. -/
theorem marked_has_moving {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : SeamStratum L x a t b) :
    a ∈ outputSet l.1 := by
  have hy := label_cell L x hx hb l.1 l.2.1
  have he := marked_input_eq L x a t b l
  by_contra ha
  have hva : fullInput L x l.1 a = x a := by
    rw [label_corner L x hx hb l.1 l.2.1]; simp [physicalCorner,ha]
  by_cases ht : t ∈ outputSet l.1
  · have hg := collision_internalGap L x _ hx _ t a _ hy.1 ht ha (he.symm.trans hva)
    have hr := hg.2.2
    rw [l.2.2.2] at hr
    by_cases h : b = false
    · simp only [h,Bool.false_eq_true,ite_false] at ho hr
      exact (not_lt_of_gt ho) hr.1
    · have h : b = true := by cases b <;> simp_all
      simp only [h,ite_true] at ho hr
      exact (not_lt_of_gt ho) hr.1
  · have hvt : fullInput L x l.1 t = x t := by
      rw [label_corner L x hx hb l.1 l.2.1]; simp [physicalCorner,ht]
    have hat := hx.injective (hva.symm.trans (he.trans hvt))
    rw [hat] at ho
    simp at ho

/-- Exact disjoint membership/Boolean partition of all original labels
in the chosen full-profile seam and branch, including every higher label. -/
def armEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) :
    FirstLower L x a t b ⊕ (SecondLower L x a t b ⊕ Higher L x a t b) ≃
      SeamStratum L x a t b where
  toFun
    | .inl l => ⟨l.1.1,l.1.2.1,l.1.2.2.1,l.2.1⟩
    | .inr (.inl l) => ⟨l.1.1,l.1.2.1,l.1.2.2.1,l.2.1⟩
    | .inr (.inr l) => ⟨l.1,l.2.1,l.2.2.1,l.2.2.2.1⟩
  invFun l := by
    have ha := marked_has_moving L x hx hb a t b ho l
    have he := marked_input_eq L x a t b l
    by_cases ht : t ∈ outputSet l.1
    · exact .inr (.inr ⟨l.1,l.2.1,l.2.2.1,l.2.2.2,ha,ht,he⟩)
    · have he' : fullInput L x l.1 a = x t := by
        rw [he,label_corner L x hx hb l.1 l.2.1]; simp [physicalCorner,ht]
      let m : MixedStratum L x (seamMark b a t) a t := ⟨l.1,l.2.1,l.2.2.1,ha,ht,he'⟩
      by_cases hε : booleans l.1 a = b
      · exact .inl ⟨m,l.2.2.2,hε⟩
      · have hε' : booleans l.1 a = !b := Bool.eq_not_iff.mpr hε
        exact .inr (.inl ⟨m,l.2.2.2,hε'⟩)
  left_inv l := by
    rcases l with l | (l | l)
    · dsimp only
      simp only [dite_eq_right l.1.2.2.2.2.1,dite_eq_left l.2.2]
    · dsimp only
      have hn : booleans l.1.1 a ≠ b := by rw [l.2.2]; cases b <;> simp
      simp only [dite_eq_right l.1.2.2.2.2.1,dite_eq_right hn]
    · dsimp only
      simp only [dite_eq_left l.2.2.2.2.2.1]
  right_inv l := by
    dsimp only
    split_ifs <;> rfl

/-- A single triple equivalence: three disjoint copies of the first
lower, with the actual BSL1 exchange and BCD1 promotion as its other arms. -/
def tripleEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) :
    FirstLower L x a t b ⊕ (FirstLower L x a t b ⊕ FirstLower L x a t b) ≃
      SeamStratum L x a t b :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr
    (lowerEquiv L x hx hb a t b) (higherEquiv L x hx hb a t b ho))).trans
      (armEquiv L x hx hb a t b ho)

/-- Exact literal degrees of both lower copies and the promoted copy. -/
theorem lowerEquiv_degree {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (l : FirstLower L x a t b) :
    (lowerEquiv L x hx hb a t b l).1.1.1 = l.1.1.1 :=
  mixedExchange_degree L x hx hb (seamMark b a t) a t l.1

theorem higherEquiv_degree {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : FirstLower L x a t b) :
    (higherEquiv L x hx hb a t b ho l).1.1.val = l.1.1.1.val + 1 := by
  dsimp only [higherEquiv,Equiv.coe_fn_mk,raise]
  apply promoteLabel_degree
  exact l.1.2.2.2.2.1

/-- Both constructed arms preserve the complete input, hence every
simultaneous seam, not merely the chosen pair. -/
theorem triple_inputs {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : FirstLower L x a t b) :
    fullInput L x (lowerEquiv L x hx hb a t b l).1.1 = fullInput L x l.1.1 ∧
    fullInput L x (higherEquiv L x hx hb a t b ho l).1 = fullInput L x l.1.1 := by
  refine ⟨mixedExchange_input L x hx hb (seamMark b a t) a t l.1,?_⟩
  dsimp only [higherEquiv,Equiv.coe_fn_mk,raise]
  apply (promoteLabel_supported L x hx hb l.1.1 l.1.2.1 a t
    l.1.2.2.2.1 l.1.2.2.2.2.1 l.1.2.2.2.2.2 (l.2.2.trans l.2.1.symm) _).2.1

/-- Every arm remains in the literal original noncollapsed class.
This also reconciles BSP1 collapsed pairing on the strict representative. -/
theorem triple_noncollapsed {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (l : FirstLower L x a t b) :
    Noncollapsed L x l.1.1 ∧
    Noncollapsed L x (lowerEquiv L x hx hb a t b l).1.1 ∧
    Noncollapsed L x (higherEquiv L x hx hb a t b ho l).1 :=
  ⟨admitted_noncollapsed L x hx hb _ l.1.2.1,
   admitted_noncollapsed L x hx hb _ (lowerEquiv L x hx hb a t b l).1.2.1,
   admitted_noncollapsed L x hx hb _ (higherEquiv L x hx hb a t b ho l).2.1⟩

/-- Exact signed triple regrouping for any function of the original labels.
No cancellation or relation between the three function values is assumed. -/
theorem sum_triples {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (f : RawLabel N → ℂ) :
    (∑ l : SeamStratum L x a t b, f l.1) =
      ∑ l : FirstLower L x a t b,
        (f l.1.1 + f (lowerEquiv L x hx hb a t b l).1.1 +
          f (higherEquiv L x hx hb a t b ho l).1) := by
  classical
  let _ : Fintype (FirstLower L x a t b) := inferInstance
  have h := (tripleEquiv L x hx hb a t b ho).sum_comp (fun l => f l.1)
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type] at h
  simpa [tripleEquiv,armEquiv,Finset.sum_add_distrib,add_assoc] using h.symm

/-- Multiplicity one in each original degree, including the exact +1
shift of the higher arm. The weight may select a single degree. -/
theorem sum_triples_degree {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (a t : Fin N) (b : Bool)
    (ho : if b then t < a else a < t) (w : ℕ → ℂ) (f : RawLabel N → ℂ) :
    (∑ l : SeamStratum L x a t b, w l.1.1.val * f l.1) =
      ∑ l : FirstLower L x a t b,
        (w l.1.1.1.val * (f l.1.1 + f (lowerEquiv L x hx hb a t b l).1.1) +
          w (l.1.1.1.val+1) * f (higherEquiv L x hx hb a t b ho l).1) := by
  rw [sum_triples L x hx hb a t b ho (fun l => w l.1.val * f l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [lowerEquiv_degree L x hx hb a t b l,higherEquiv_degree L x hx hb a t b ho l]
  ring

/-- The branch-dependent pair has exactly the stored unordered mark. -/
theorem seamMark_branch {N : ℕ} (b : Bool) (p : Fin N × Fin N) :
    seamMark b (if b then p.2 else p.1) (if b then p.1 else p.2) = p := by
  cases b <;> simp [seamMark]

/-- Flatten only proof fields when splitting a chosen-mark fiber by branch. -/
def branchFiberEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (p : Fin N × Fin N) (b : Bool) :
    {l : {l : Label L x // labelMark L x l.1 = some p} // l.1.1.2.2.2.1 = b} ≃
      SeamStratum L x (if b then p.2 else p.1) (if b then p.1 else p.2) b where
  toFun l := ⟨l.1.1.1,l.1.1.2,by rw [seamMark_branch]; exact l.1.2,l.2⟩
  invFun l := ⟨⟨⟨l.1,l.2.1⟩,l.2.2.1.trans (congrArg some (seamMark_branch b p))⟩,l.2.2.2⟩
  left_inv _ := Subtype.ext (Subtype.ext (Subtype.ext rfl))
  right_inv _ := Subtype.ext rfl

/-- Exact branch split in the same fiber used by sum_marks_original. -/
theorem sum_branches {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (p : Fin N × Fin N) (f : RawLabel N → ℂ) :
    (∑ l : {l : Label L x // labelMark L x l.1 = some p}, f l.1.1) =
      ∑ b : Bool, ∑ l : SeamStratum L x
        (if b then p.2 else p.1) (if b then p.1 else p.2) b, f l.1 := by
  classical
  let e := (Equiv.sigmaCongrRight fun b => (branchFiberEquiv L x p b).symm).trans
    (Equiv.sigmaFiberEquiv (fun l : {l : Label L x // labelMark L x l.1 = some p} =>
      l.1.1.2.2.2.1))
  have h := e.sum_comp (fun l => f l.1.1)
  rw [Fintype.sum_sigma] at h
  simpa [e,branchFiberEquiv] using h.symm

/-- The actual triple sum for one full-profile chosen mark. -/
def chosenTripleSum {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (hp : p.1 < p.2) (f : RawLabel N → ℂ) : ℂ :=
  ∑ b : Bool, ∑ l : FirstLower L x
      (if b then p.2 else p.1) (if b then p.1 else p.2) b,
    (f l.1.1 + f (lowerEquiv L x hx hb _ _ b l).1.1 +
      f (higherEquiv L x hx hb _ _ b (by cases b <;> simpa using hp) l).1)

theorem sum_chosen_triples {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (hp : p.1 < p.2) (f : RawLabel N → ℂ) :
    (∑ l : {l : Label L x // labelMark L x l.1 = some p}, f l.1.1) =
      chosenTripleSum L x hx hb p hp f := by
  rw [sum_branches]
  apply Finset.sum_congr rfl
  intro b _
  exact sum_triples L x hx hb _ _ b (by cases b <;> simpa using hp) f

/-- Retain the entire no-input-coincidence fiber. It is not yet identified
with the actual exterior charts. Invalid unordered marks have no labels. -/
def regroupedMark {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (f : RawLabel N → ℂ) (p : Option (Fin N × Fin N)) : ℂ :=
  match p with
  | none => ∑ l : {l : Label L x // labelMark L x l.1 = none}, f l.1.1
  | some p => if hp : p.1 < p.2 then chosenTripleSum L x hx hb p hp f else 0

/-- Multiplicity one against the original mark fiber, for arbitrary weights. -/
theorem regroupedMark_eq {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (f : RawLabel N → ℂ) (p : Option (Fin N × Fin N)) :
    regroupedMark L x hx hb f p =
      ∑ l : {l : Label L x // labelMark L x l.1 = p}, f l.1.1 := by
  classical
  cases p with
  | none => rfl
  | some p =>
    by_cases hp : p.1 < p.2
    · simpa only [regroupedMark,dite_eq_left hp] using
        (sum_chosen_triples L x hx hb p hp f).symm
    · let _ : IsEmpty {l : Label L x // labelMark L x l.1 = some p} := ⟨by
        intro l
        have h := chooseSeam_mem (labelProfile L x l.1.1) p l.2
        exact hp ((mem_seams _ p.1 p.2).mp h).1⟩
      simp [regroupedMark,hp]

/-- Literal signed BGE1 expansion regrouped into disjoint triples and the
unchanged no-input-coincidence fiber; no global vanishing is asserted. -/
theorem sum_marks_triples_original {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ p : Option (Fin N × Fin N), regroupedMark L x hx hb (value L c n z x) p) =
      ∑ d : Fin (N+1), (c : ℂ)^d.val *
        ∑ S : PlacementSubset d.val (N-d.val),
          let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
          let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
          ∑ T : PlacementSubset d.val (N-d.val),
            (sourceCorners L c (n ∘ ambient d) z X s false T +
             sourceCorners L c (n ∘ ambient d) z X s true T) := by
  simp_rw [regroupedMark_eq]
  exact sum_marks_original L c n z x

/-- The finite mark partition preserves every weight on literal degrees. -/
theorem sum_regrouped_weighted {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) (f : RawLabel N → ℂ) :
    (∑ p : Option (Fin N × Fin N),
      regroupedMark L x hx hb (fun l => w l.1.val * f l) p) =
      ∑ l : Label L x, w l.1.1.val * f l.1 := by
  simp_rw [regroupedMark_eq]
  have h := (markEquiv L x).sum_comp (fun l => w l.1.1.val * f l.1)
  rw [Fintype.sum_sigma] at h
  exact h

/-- Literal BGE1 degree expansion with an arbitrary degree weight. -/
theorem sum_value_weighted {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (w : ℕ → ℂ) :
    (∑ l : Label L x, w l.1.1.val * value L c n z x l.1) =
      ∑ d : Fin (N+1), w d.val * (c : ℂ)^d.val *
        ∑ S : PlacementSubset d.val (N-d.val),
          let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
          let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
          ∑ T : PlacementSubset d.val (N-d.val),
            (sourceCorners L c (n ∘ ambient d) z X s false T +
             sourceCorners L c (n ∘ ambient d) z X s true T) := by
  classical
  rw [sum_guarded (admitted L x) (fun l : RawLabel N => w l.1.val * value L c n z x l),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  dsimp only
  rw [← sum_branchValue,sum_guarded,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  dsimp only [admitted,outputTuple,spectatorTuple,value]
  simp only [mul_ite,mul_zero,mul_assoc]
  rfl

/-- Degree-by-degree multiplicity against the literal original expansion.
Taking w to be a degree indicator selects exactly that original degree. -/
theorem sum_marks_triples_original_weighted {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) :
    (∑ p : Option (Fin N × Fin N),
      regroupedMark L x hx hb (fun l => w l.1.val * value L c n z x l) p) =
      ∑ d : Fin (N+1), w d.val * (c : ℂ)^d.val *
        ∑ S : PlacementSubset d.val (N-d.val),
          let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
          let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
          ∑ T : PlacementSubset d.val (N-d.val),
            (sourceCorners L c (n ∘ ambient d) z X s false T +
             sourceCorners L c (n ∘ ambient d) z X s true T) := by
  rw [sum_regrouped_weighted]
  exact sum_value_weighted L c n z x w

end QuantumNLS.BetheTripleStrata

#print axioms QuantumNLS.BetheTripleStrata.seamMark
#print axioms QuantumNLS.BetheTripleStrata.FirstLower
#print axioms QuantumNLS.BetheTripleStrata.SecondLower
#print axioms QuantumNLS.BetheTripleStrata.Higher
#print axioms QuantumNLS.BetheTripleStrata.SeamStratum
#print axioms QuantumNLS.BetheTripleStrata.lowerEquiv
#print axioms QuantumNLS.BetheTripleStrata.raise
#print axioms QuantumNLS.BetheTripleStrata.higher_pinned
#print axioms QuantumNLS.BetheTripleStrata.higher_demotable
#print axioms QuantumNLS.BetheTripleStrata.lower
#print axioms QuantumNLS.BetheTripleStrata.higherEquiv
#print axioms QuantumNLS.BetheTripleStrata.marked_input_eq
#print axioms QuantumNLS.BetheTripleStrata.marked_has_moving
#print axioms QuantumNLS.BetheTripleStrata.armEquiv
#print axioms QuantumNLS.BetheTripleStrata.tripleEquiv
#print axioms QuantumNLS.BetheTripleStrata.lowerEquiv_degree
#print axioms QuantumNLS.BetheTripleStrata.higherEquiv_degree
#print axioms QuantumNLS.BetheTripleStrata.triple_inputs
#print axioms QuantumNLS.BetheTripleStrata.triple_noncollapsed
#print axioms QuantumNLS.BetheTripleStrata.sum_triples
#print axioms QuantumNLS.BetheTripleStrata.sum_triples_degree
#print axioms QuantumNLS.BetheTripleStrata.seamMark_branch
#print axioms QuantumNLS.BetheTripleStrata.branchFiberEquiv
#print axioms QuantumNLS.BetheTripleStrata.sum_branches
#print axioms QuantumNLS.BetheTripleStrata.chosenTripleSum
#print axioms QuantumNLS.BetheTripleStrata.sum_chosen_triples
#print axioms QuantumNLS.BetheTripleStrata.regroupedMark
#print axioms QuantumNLS.BetheTripleStrata.regroupedMark_eq
#print axioms QuantumNLS.BetheTripleStrata.sum_marks_triples_original
#print axioms QuantumNLS.BetheTripleStrata.sum_regrouped_weighted
#print axioms QuantumNLS.BetheTripleStrata.sum_value_weighted
#print axioms QuantumNLS.BetheTripleStrata.sum_marks_triples_original_weighted
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheTripleStrata.seamMark,
    ``QuantumNLS.BetheTripleStrata.FirstLower,
    ``QuantumNLS.BetheTripleStrata.SecondLower,
    ``QuantumNLS.BetheTripleStrata.Higher,
    ``QuantumNLS.BetheTripleStrata.SeamStratum,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv,
    ``QuantumNLS.BetheTripleStrata.raise,
    ``QuantumNLS.BetheTripleStrata.higher_pinned,
    ``QuantumNLS.BetheTripleStrata.higher_demotable,
    ``QuantumNLS.BetheTripleStrata.lower,
    ``QuantumNLS.BetheTripleStrata.higherEquiv,
    ``QuantumNLS.BetheTripleStrata.marked_input_eq,
    ``QuantumNLS.BetheTripleStrata.marked_has_moving,
    ``QuantumNLS.BetheTripleStrata.armEquiv,
    ``QuantumNLS.BetheTripleStrata.tripleEquiv,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.higherEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.triple_inputs,
    ``QuantumNLS.BetheTripleStrata.triple_noncollapsed,
    ``QuantumNLS.BetheTripleStrata.sum_triples,
    ``QuantumNLS.BetheTripleStrata.sum_triples_degree,
    ``QuantumNLS.BetheTripleStrata.seamMark_branch,
    ``QuantumNLS.BetheTripleStrata.branchFiberEquiv,
    ``QuantumNLS.BetheTripleStrata.sum_branches,
    ``QuantumNLS.BetheTripleStrata.chosenTripleSum,
    ``QuantumNLS.BetheTripleStrata.sum_chosen_triples,
    ``QuantumNLS.BetheTripleStrata.regroupedMark,
    ``QuantumNLS.BetheTripleStrata.regroupedMark_eq,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original,
    ``QuantumNLS.BetheTripleStrata.sum_regrouped_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_value_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original_weighted,

    ``QuantumNLS.BetheStrictLabelStrata.endpoint_candidates_disjoint,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCell_strict,
    ``QuantumNLS.BetheStrictLabelStrata.Noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.label_physical_strict,
    ``QuantumNLS.BetheStrictLabelStrata.admitted_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.no_admitted_collapsed,
    ``QuantumNLS.BetheStrictLabelStrata.promoteLabel_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.mixed_incident_iff,
    ``QuantumNLS.BetheStrictLabelStrata.selected_seam_demote_strict,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_data,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_booleans,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_degree,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_inverse,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_ne,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCorner_exchange_any,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported_any,
    ``QuantumNLS.BetheStrictLabelStrata.MixedStratum,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_involutive,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_ne,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_degree,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_input,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_orientation,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv_degree,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Triple strata nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_promote,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_exchanged,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheInputAdjacency.chartOrderingEquiv,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse] do
    unless seen.contains n do
      throwError "Triple strata aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Triple strata aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Triple strata aggregate audit PASS: {seen.size} transitive constants across separate roots. Exhaustive disjoint original-label triple equivalence at every chosen seam and branch, literal noncollapse, full inputs and chosen marks retained, and exact weighted degree-by-degree regrouping against the original BGE1 sum. Inherited local balance and physical action audited as separate roots. Actual exterior classification, raw-label balance transport, global cancellation and spectral assembly remain OPEN."
