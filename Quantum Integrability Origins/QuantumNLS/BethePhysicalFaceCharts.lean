import QuantumNLS.BethePhysicalReindex
import QuantumNLS.BetheChamberSweep

/-! The actual raw source integrals split into merged chambers almost
everywhere, with multiplicity one. Boundary traces and cross-degree
primitive transport are separate obligations. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BethePhysicalFaceCharts
open TensorPlacements BetheFaceEnumeration BethePhysicalReindex
open BetheTransferKernelAdjoint BetheWeakGradient BetheExtension

theorem append_injective {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : Function.Injective y) (hs : Function.Injective s)
    (hne : ∀ i j, y i ≠ s j) : Function.Injective (Fin.append y s) := by
  intro a b
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b <;> intro h
  · exact congrArg (Fin.castAdd q) (hy (by simpa using h))
  · exact False.elim (hne i j (by simpa using h))
  · exact False.elim (hne j i (by simpa using h.symm))
  · exact congrArg (Fin.natAdd m) (hs (by simpa using h))

theorem cube_ae_cross_ne {m q : ℕ} (L : ℝ) (s : Fin q → ℝ) :
    ∀ᵐ y ∂cubeMeasure m L, ∀ i j, y i ≠ s j := by
  have h (i : Fin m) (j : Fin q) : ∀ᵐ y ∂cubeMeasure m L, y i ≠ s j := by
    have he := Measure.ae_eval_ne (fun _ : Fin m => (volume : Measure ℝ)) i (s j)
    rw [← volume_pi] at he
    exact ae_restrict_of_ae he
  exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (h i))

def chartSet {m q : ℕ} (S : PlacementSubset m q) (s : Fin q → ℝ) : Set (Fin m → ℝ) :=
  {y | Antitone (mergeChart S y s)}

theorem measurableSet_chartSet {m q : ℕ} (S : PlacementSubset m q) (s : Fin q → ℝ) :
    MeasurableSet (chartSet S s) := by
  unfold chartSet Antitone
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (by unfold mergeChart; fun_prop) (by unfold mergeChart; fun_prop)

/-- The raw integrand, not a formal face label. -/
def rawSource {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (y : Fin m → ℝ) : ℂ :=
  rawKernel L z X y * symmetricExtension L c n (Fin.append y s)

theorem rawSource_zero_of_not_strictAnti {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (z : ℂ) (X : Fin m → ℝ) (s : Fin q → ℝ) (y : Fin m → ℝ)
    (hy : ¬ StrictAnti y) : rawSource L c n z X s y = 0 := by
  classical
  have hp : ¬ PlusOrder L X y := fun h => hy (BetheFiniteNAction.plusOrder_input_strictAnti h)
  have hm : ¬ MinusOrder L X y := fun h => hy (BetheFiniteNAction.minusOrder_input_strictAnti h)
  simp [rawSource, rawKernel, rawPlus, rawMinus, hp, hm]

theorem integrable_rawSource {m q : ℕ} {L : ℝ} (hL : 0 ≤ L) (c : ℝ)
    (n : Fin (m+q) → ℤ) (z : ℂ) (X : Fin m → ℝ) (s : Fin q → ℝ) :
    Integrable (rawSource L c n z X s) (cubeMeasure m L) := by
  have hf : Continuous (fun y : Fin m → ℝ => symmetricExtension L c n (Fin.append y s)) :=
    (continuous_symmetricExtension L c n).comp (by fun_prop)
  have hi : Integrable (fun y : Fin m → ℝ => symmetricExtension L c n (Fin.append y s))
      (cubeMeasure m L) := hf.integrableOn_Icc
  apply hi.bdd_mul
    ((((BetheTransferOperators.measurable_rawPlus m L z).add
      (BetheTransferOperators.measurable_rawMinus m L z)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards with y
  exact (norm_add_le _ _).trans (add_le_add
    (BetheTransferOperators.norm_rawPlus_le L hL z X y)
    (BetheTransferOperators.norm_rawMinus_le L hL z X y))

/-- Each nonzero raw integrand has exactly one merged chamber off the
spectator hyperplanes. Thus its chamber multiplicity is exactly one. -/
theorem rawSource_partition_ae {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (z : ℂ) (X : Fin m → ℝ) (s : Fin q → ℝ) (hs : StrictAnti s) :
    rawSource L c n z X s =ᵐ[cubeMeasure m L]
      fun y => ∑ S : PlacementSubset m q, (chartSet S s).indicator (rawSource L c n z X s) y := by
  classical
  filter_upwards [cube_ae_cross_ne L s] with y hne
  by_cases hy : StrictAnti y
  · obtain ⟨S, hS, hu⟩ := exists_unique_mergeChart y s hy hs
      (append_injective y s hy.injective hs.injective hne)
    rw [Finset.sum_eq_single S]
    · exact (indicator_of_mem hS _).symm
    · intro T _ hT
      apply indicator_of_notMem
      exact fun h => hT (hu T h)
    · simp
  · have hz := rawSource_zero_of_not_strictAnti L c n z X s y hy
    rw [hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro S _
    by_cases h : y ∈ chartSet S s <;> simp [h, hz]

/-- An actual almost-everywhere disjoint chamber decomposition of the
physical raw integral, retaining both branches and all spectator values. -/
theorem integral_rawSource_charts {m q : ℕ} {L : ℝ} (hL : 0 ≤ L) (c : ℝ)
    (n : Fin (m+q) → ℤ) (z : ℂ) (X : Fin m → ℝ) (s : Fin q → ℝ) (hs : StrictAnti s) :
    (∫ y, rawSource L c n z X s y ∂cubeMeasure m L) =
      ∑ S : PlacementSubset m q, ∫ y in chartSet S s, rawSource L c n z X s y ∂cubeMeasure m L := by
  rw [integral_congr_ae (rawSource_partition_ae L c n z X s hs)]
  rw [integral_finsetSum _ (fun S _ =>
    (integrable_rawSource hL c n z X s).indicator (measurableSet_chartSet S s))]
  apply Finset.sum_congr rfl
  intro S _
  exact integral_indicator (measurableSet_chartSet S s)

/-- Literal positive-c source cube integral split into the physical merged
chambers. No integral is discarded at a collision without a null-set proof. -/
theorem sourceRawCube_charts {m q : ℕ} {L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) (x : Fin (m+q) → ℝ)
    (hs : StrictAnti (fun i : Fin q => x (Fin.natAdd m i))) :
    sourceRawCube L hc hn z x =
      ∑ T : PlacementSubset m q, ∫ y in chartSet T (fun i : Fin q => x (Fin.natAdd m i)),
        rawSource L c n z (fun i : Fin m => x (Fin.castAdd q i))
          (fun i : Fin q => x (Fin.natAdd m i)) y ∂cubeMeasure m L :=
  integral_rawSource_charts hL c n z _ _ hs

/-- The two literal alternating rectangles at fixed ordered output X.
false is the plus branch; true is the minus branch. -/
def rectangleLower {m : ℕ} (X : Fin m → ℝ) (b : Bool) (i : Fin m) : ℝ :=
  if b then X i else BetheFiniteNAction.lower X i

def rectangleUpper {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool) (i : Fin m) : ℝ :=
  if b then BetheFiniteNAction.upper L X i else X i

def openRectangle {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool) : Set (Fin m → ℝ) :=
  {y | ∀ i, y i ∈ Ioo (rectangleLower X b i) (rectangleUpper L X b i)}

def closedRectangle {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool) : Set (Fin m → ℝ) :=
  {y | ∀ i, y i ∈ Icc (rectangleLower X b i) (rectangleUpper L X b i)}

/-- Actual branch support, rather than an abstract rectangle stipulated
to represent the physical kernel. -/
theorem plusOrder_openRectangle {m : ℕ} {L : ℝ} {X : Fin m → ℝ}
    (hX : X ∈ BetheWavefunctions.chamber m L) (y : Fin m → ℝ) :
    PlusOrder L X y ↔ y ∈ openRectangle L X false :=
  BetheFiniteNAction.plusOrder_box hX y

theorem minusOrder_openRectangle {m : ℕ} {L : ℝ} {X : Fin m → ℝ}
    (hX : X ∈ BetheWavefunctions.chamber m L) (y : Fin m → ℝ) :
    MinusOrder L X y ↔ y ∈ openRectangle L X true :=
  BetheFiniteNAction.minusOrder_box hX y

/-- A rectangle face is a moving integration coordinate and one of its
two actual endpoints. false is the lower endpoint; true is the upper. -/
abbrev RectangleFace (m : ℕ) := Fin m × Bool

def rectangleFaceEquation {m : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (b : Bool) (f : RectangleFace m) : Prop :=
  y f.1 = if f.2 then rectangleUpper L X b f.1 else rectangleLower X b f.1

theorem card_rectangleFace (m : ℕ) : Fintype.card (RectangleFace m) = 2*m := by
  simp [RectangleFace, Nat.mul_comm]

/-- Complete endpoint exhaustion of each literal alternating rectangle.
Corners may satisfy several equations; no multiplicity at an intersection
or between different transfer degrees is inferred from this statement. -/
theorem rectangle_interior_or_face {m : ℕ} (L : ℝ) (X y : Fin m → ℝ) (b : Bool)
    (hy : y ∈ closedRectangle L X b) :
    y ∈ openRectangle L X b ∨ ∃ f, rectangleFaceEquation L X y b f := by
  classical
  by_cases h : ∃ f, rectangleFaceEquation L X y b f
  · exact Or.inr h
  · left
    intro i
    have hl : y i ≠ rectangleLower X b i := fun he => h ⟨(i,false),he⟩
    have hu : y i ≠ rectangleUpper L X b i := fun he => h ⟨(i,true),he⟩
    exact ⟨lt_of_le_of_ne (hy i).1 hl.symm, lt_of_le_of_ne (hy i).2 hu⟩

/-- The two exterior endpoint labels are precisely plus-last-lower=0
and minus-first-upper=L, as used in the frozen round35 source pairing. -/
theorem exterior_rectangle_faces {r : ℕ} (L : ℝ) (X y : Fin (r+1) → ℝ) :
    (rectangleFaceEquation L X y false (Fin.last r,false) ↔ y (Fin.last r) = 0) ∧
    (rectangleFaceEquation L X y true (0,true) ↔ y 0 = L) := by
  simp [rectangleFaceEquation, rectangleLower, rectangleUpper,
    BetheFiniteNAction.lower, BetheFiniteNAction.upper]

/-- Every plus upper or minus lower endpoint is the same selected-output
coordinate X_j. These are separate from the exterior 0/L pair. -/
theorem selected_rectangle_faces {m : ℕ} (L : ℝ) (X y : Fin m → ℝ) (i : Fin m) :
    (rectangleFaceEquation L X y false (i,true) ↔ y i = X i) ∧
    (rectangleFaceEquation L X y true (i,false) ↔ y i = X i) := by
  simp [rectangleFaceEquation, rectangleLower, rectangleUpper]

/-- The other selected-output endpoints use the adjacent X coordinate. -/
theorem adjacent_rectangle_faces {r : ℕ} (L : ℝ) (X y : Fin (r+1) → ℝ) (j : Fin r) :
    (rectangleFaceEquation L X y false (j.castSucc,false) ↔ y j.castSucc = X j.succ) ∧
    (rectangleFaceEquation L X y true (j.succ,true) ↔ y j.succ = X j.castSucc) := by
  have hj : j.val+1 < r+1 := by omega
  simp [rectangleFaceEquation, rectangleLower, rectangleUpper,
    BetheFiniteNAction.lower, BetheFiniteNAction.upper, hj]
  constructor <;> rfl

open TensorCarrier PhysicalTensor BetheHigherPlacement BetheGeneralSliceEndpoints
variable (L : ℝ) [Fact (0 < L)]

/-- The actual physical positive-degree transfer term, after both inner
compressions, the full outer average, and the a.e. merged-chamber split.
The outer subset has coefficient c^m and every inner chart multiplicity one. -/
theorem source_transferTerm_charts_ae (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), StrictAnti (representatives L x) →
      physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
        (sourceVector L hc hn)).1) x = (c : ℂ)^m *
        ∑ S : PlacementSubset m q, ∑ T : PlacementSubset m q,
          ∫ y in chartSet T (fun i : Fin q => representatives L x ((mergePermutation S) (Fin.natAdd m i))),
            rawSource L c n z
              (fun i : Fin m => representatives L x ((mergePermutation S) (Fin.castAdd q i)))
              (fun i : Fin q => representatives L x ((mergePermutation S) (Fin.natAdd m i))) y
              ∂cubeMeasure m L := by
  filter_upwards [source_transferTerm_cube_ae L m q hm hc hn z] with x he hx
  rw [he hx]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  have hs : StrictAnti (fun i : Fin q => representatives L (coordPerm (mergePermutation S) x)
      (Fin.natAdd m i)) := by
    intro i j hij
    apply hx
    simpa only [Equiv.symm_symm, mergePermutation_spectator] using
      (S.1ᶜ.orderEmbOfFin (complement_card S)).strictMono hij
  exact sourceRawCube_charts (Fact.out : 0 < L).le hc hn z _ hs

end QuantumNLS.BethePhysicalFaceCharts

#print axioms QuantumNLS.BethePhysicalFaceCharts.append_injective
#print axioms QuantumNLS.BethePhysicalFaceCharts.cube_ae_cross_ne
#print axioms QuantumNLS.BethePhysicalFaceCharts.chartSet
#print axioms QuantumNLS.BethePhysicalFaceCharts.measurableSet_chartSet
#print axioms QuantumNLS.BethePhysicalFaceCharts.rawSource
#print axioms QuantumNLS.BethePhysicalFaceCharts.rawSource_zero_of_not_strictAnti
#print axioms QuantumNLS.BethePhysicalFaceCharts.integrable_rawSource
#print axioms QuantumNLS.BethePhysicalFaceCharts.rawSource_partition_ae
#print axioms QuantumNLS.BethePhysicalFaceCharts.integral_rawSource_charts
#print axioms QuantumNLS.BethePhysicalFaceCharts.sourceRawCube_charts
#print axioms QuantumNLS.BethePhysicalFaceCharts.rectangleLower
#print axioms QuantumNLS.BethePhysicalFaceCharts.rectangleUpper
#print axioms QuantumNLS.BethePhysicalFaceCharts.openRectangle
#print axioms QuantumNLS.BethePhysicalFaceCharts.closedRectangle
#print axioms QuantumNLS.BethePhysicalFaceCharts.plusOrder_openRectangle
#print axioms QuantumNLS.BethePhysicalFaceCharts.minusOrder_openRectangle
#print axioms QuantumNLS.BethePhysicalFaceCharts.RectangleFace
#print axioms QuantumNLS.BethePhysicalFaceCharts.rectangleFaceEquation
#print axioms QuantumNLS.BethePhysicalFaceCharts.card_rectangleFace
#print axioms QuantumNLS.BethePhysicalFaceCharts.rectangle_interior_or_face
#print axioms QuantumNLS.BethePhysicalFaceCharts.exterior_rectangle_faces
#print axioms QuantumNLS.BethePhysicalFaceCharts.selected_rectangle_faces
#print axioms QuantumNLS.BethePhysicalFaceCharts.adjacent_rectangle_faces
#print axioms QuantumNLS.BethePhysicalFaceCharts.source_transferTerm_charts_ae

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BethePhysicalFaceCharts.source_transferTerm_charts_ae,
    ``QuantumNLS.BethePhysicalFaceCharts.rectangle_interior_or_face,
    ``QuantumNLS.BethePhysicalFaceCharts.exterior_rectangle_faces,
    ``QuantumNLS.BethePhysicalFaceCharts.selected_rectangle_faces,
    ``QuantumNLS.BethePhysicalFaceCharts.adjacent_rectangle_faces,
    ``QuantumNLS.BethePhysicalFaceCharts.plusOrder_openRectangle,
    ``QuantumNLS.BethePhysicalFaceCharts.minusOrder_openRectangle,
    ``QuantumNLS.BethePhysicalFaceCharts.card_rectangleFace]
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
  for n in #[``QuantumNLS.BethePhysicalReindex.slice_permuted,
      ``QuantumNLS.BethePhysicalReindex.slice_inputAverage,
      ``QuantumNLS.BethePhysicalReindex.sum_compressed,
      ``QuantumNLS.BethePhysicalReindex.source_transferTerm_raw_ae,
      ``QuantumNLS.BethePhysicalReindex.rawSlice_orderedFiber,
      ``QuantumNLS.BethePhysicalReindex.sum_raw_by_subset,
      ``QuantumNLS.BethePhysicalReindex.rawSlice_source_cube,
      ``QuantumNLS.BetheHigherPlacement.source_transferTerm,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``QuantumNLS.BetheFaceEnumeration.orderedFiberEquiv,
      ``QuantumNLS.BetheFaceEnumeration.card_orderedFiber,
      ``QuantumNLS.BetheFaceEnumeration.exists_unique_mergeChart,
      ``QuantumNLS.PhysicalTensor.measurePreserving_coordPerm,
      ``QuantumNLS.BetheExtension.torusExtension_permute,
      ``QuantumNLS.BethePhysicalFaceCharts.cube_ae_cross_ne,
      ``QuantumNLS.BethePhysicalFaceCharts.measurableSet_chartSet,
      ``QuantumNLS.BethePhysicalFaceCharts.integrable_rawSource,
      ``QuantumNLS.BethePhysicalFaceCharts.rawSource_partition_ae,
      ``QuantumNLS.BethePhysicalFaceCharts.integral_rawSource_charts,
      ``QuantumNLS.BetheFiniteNAction.plusOrder_box,
      ``QuantumNLS.BetheFiniteNAction.minusOrder_box,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Physical reindex/charts route missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Physical reindex/charts route forbidden dependency: {n}"
  Lean.logInfo m!"Physical reindex/charts route PASS: {seen.size} transitive constants; actual source transfer term, both inner compressions, full outer average, exact c^m ordered-subset coefficient, mass-L cube conversion, a.e. unique merged chambers and all rectangle endpoint equations. Trace-compatible multivariable incidence, primitive transport, cross-degree cancellation, allN eigenrelation and basis OPEN."
