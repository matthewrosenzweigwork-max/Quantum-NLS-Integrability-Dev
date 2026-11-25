import QuantumNLS.BetheCyclicPrimitives
import QuantumNLS.BetheIteratedIncidence

/-! Complete one-coordinate fibers of actual closed rectangle/chart cells.
Original input labels and arbitrary pending denominators are retained.
No strictness is imposed on the remaining moving tuple. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheChartFiberSteps
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BethePrimitiveTransport BetheInternalFaces
open BetheCrossDegreeFaces BetheFiniteNAction

/-- Closed physical chamber, including all multiple collisions. -/
def boundedChamber {N : ℕ} (L : ℝ) (x : Fin N → ℝ) : Prop :=
  Antitone x ∧ ∀ i, x i ∈ Icc 0 L

/-- The complete fiber of a closed chamber is its neighbor interval.
The two missing neighbors are the physical endpoints 0 and L. -/
theorem boundedChamber_update_iff {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (a : Fin N) (hx : boundedChamber L x) (t : ℝ) :
    boundedChamber L (Function.update x a t) ↔ t ∈ Icc (lower x a) (upper L x a) := by
  classical
  constructor
  · intro ht
    constructor
    · unfold lower
      split_ifs with h
      · have hh := ht.1 (show a ≤ (⟨a.val+1,h⟩ : Fin N) by exact Fin.le_iff_val_le_val.mpr (by change a.val ≤ a.val+1; omega))
        have hn : (⟨a.val+1,h⟩ : Fin N) ≠ a := by intro he; have := congrArg Fin.val he; simp at this
        simpa only [Function.update_self, Function.update_of_ne hn] using hh
      · simpa only [Function.update_self] using (ht.2 a).1
    · unfold upper
      split_ifs with h
      · have hh := ht.1 (show (⟨a.val-1,by omega⟩ : Fin N) ≤ a by exact Fin.le_iff_val_le_val.mpr (by change a.val-1 ≤ a.val; omega))
        have hn : (⟨a.val-1,by omega⟩ : Fin N) ≠ a := by intro he; have := congrArg Fin.val he; simp at this; omega
        simpa only [Function.update_self, Function.update_of_ne hn] using hh
      · simpa only [Function.update_self] using (ht.2 a).2
  · intro ht
    have hl : 0 ≤ lower x a := by unfold lower; split_ifs <;> first | exact (hx.2 _).1 | exact le_rfl
    have hu : upper L x a ≤ L := by unfold upper; split_ifs <;> first | exact (hx.2 _).2 | exact le_rfl
    constructor
    · intro i j hij
      by_cases hi : i = a
      · subst i
        by_cases hj : j = a
        · subst j; exact le_rfl
        have hv : a.val < j.val := by have := Fin.le_iff_val_le_val.mp hij; have hne := Fin.val_ne_of_ne hj; omega
        have hnext : a.val+1 < N := by omega
        have horder : (⟨a.val+1,hnext⟩ : Fin N) ≤ j := Fin.le_iff_val_le_val.mpr (by change a.val+1 ≤ j.val; omega)
        have htl : x ⟨a.val+1,hnext⟩ ≤ t := by simpa only [lower,dite_eq_left hnext] using ht.1
        have hh := (hx.1 horder).trans htl
        simpa only [lower, dite_eq_left hnext, Function.update_self, Function.update_of_ne hj] using hh
      · by_cases hj : j = a
        · subst j
          have hv : i.val < a.val := by have := Fin.le_iff_val_le_val.mp hij; have hne := Fin.val_ne_of_ne hi; omega
          have hp : 0 < a.val := by omega
          have horder : i ≤ (⟨a.val-1,by omega⟩ : Fin N) := Fin.le_iff_val_le_val.mpr (by change i.val ≤ a.val-1; omega)
          have htu : t ≤ x ⟨a.val-1,by omega⟩ := by simpa only [upper,dite_eq_left hp] using ht.2
          have hh := htu.trans (hx.1 horder)
          simpa only [upper, dite_eq_left hp, Function.update_self, Function.update_of_ne hi] using hh
        · simpa only [Function.update_of_ne hi, Function.update_of_ne hj] using hx.1 hij
    · intro i
      by_cases hi : i = a
      · subst i
        simpa only [Function.update_self] using (show t ∈ Icc 0 L from ⟨hl.trans ht.1,ht.2.trans hu⟩)
      · simpa only [Function.update_of_ne hi] using hx.2 i

/-- Changing an original selected label changes precisely its actual merged
rank; no rank is guessed from the current value ordering. -/
theorem mergeChart_update {m q : ℕ} (S : PlacementSubset m q)
    (y : Fin m → ℝ) (s : Fin q → ℝ) (i : Fin m) (t : ℝ) :
    mergeChart S (Function.update y i t) s =
      Function.update (mergeChart S y s) (selectedRank S i) t := by
  classical
  ext k
  obtain ⟨j,rfl⟩ := (mergePermutation S).surjective k
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · by_cases ha : a = i
    · subst a; simp [mergeChart,selectedRank]
    · have hn : mergePermutation S (Fin.castAdd q a) ≠ selectedRank S i := by
        intro h
        exact ha ((Fin.castAdd_injective m q) ((mergePermutation S).injective h))
      simp [mergeChart,Function.update_of_ne ha,Function.update_of_ne hn]
  · have hn : mergePermutation S (Fin.natAdd m a) ≠ selectedRank S i := by
      intro h
      have hv := congrArg Fin.val ((mergePermutation S).injective h)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp [mergeChart,Function.update_of_ne hn]

/-- A physical cell is the original rectangle intersected with its bounded
merged chart. Its fibers include every lower-dimensional collision. -/
def closedPhysicalCell {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) : Set (Fin m → ℝ) :=
  {y | y ∈ closedRectangle L X b ∧ boundedChamber L (mergeChart S y s)}

def fiberLower {m q : ℕ} (X y : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) : ℝ :=
  max (rectangleLower X b i) (lower (mergeChart S y s) (selectedRank S i))

def fiberUpper {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) : ℝ :=
  min (rectangleUpper L X b i) (upper L (mergeChart S y s) (selectedRank S i))

/-- Exact full fiber equality: endpoints are derived by intersecting the
literal rectangle with the two actual chamber neighbors. -/
theorem closedPhysicalCell_fiber {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q) (i : Fin m)
    (hy : y ∈ closedPhysicalCell L X s b S) :
    {t | Function.update y i t ∈ closedPhysicalCell L X s b S} =
      Icc (fiberLower X y s b S i) (fiberUpper L X y s b S i) := by
  classical
  have hr (t : ℝ) : Function.update y i t ∈ closedRectangle L X b ↔
      t ∈ Icc (rectangleLower X b i) (rectangleUpper L X b i) := by
    constructor
    · intro h; simpa only [Function.update_self] using h i
    · intro ht j
      by_cases hj : j = i
      · subst j; simpa only [Function.update_self] using ht
      · simpa only [Function.update_of_ne hj] using hy.1 j
  ext t
  change (_ ∧ _) ↔ _
  rw [hr,mergeChart_update,boundedChamber_update_iff L _ _ hy.2]
  simp only [fiberLower,fiberUpper,mem_Icc,max_le_iff,le_min_iff]
  tauto

/-- Every original selected label has a nonempty complete fiber through
an incident point, including zero-length fibers at corners. -/
theorem fiber_bounds {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q) (i : Fin m)
    (hy : y ∈ closedPhysicalCell L X s b S) :
    fiberLower X y s b S i ≤ y i ∧ y i ≤ fiberUpper L X y s b S i := by
  have hm : y i ∈ {t | Function.update y i t ∈ closedPhysicalCell L X s b S} := by
    change Function.update y i (y i) ∈ closedPhysicalCell L X s b S
    simpa only [Function.update_eq_self] using hy
  rw [closedPhysicalCell_fiber L X y s b S i hy] at hm
  exact hm

/-- One ordinary primitive integration on the entire actual chart fiber,
retaining the original input label set A. Both endpoint terms survive. -/
theorem integral_chartPrimitive_fiber {m q : ℕ} (L c : ℝ) (r : Fin (m+q) → ℝ)
    (X y : Fin m → ℝ) (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (i : Fin m) (hy : y ∈ closedPhysicalCell L X s b S)
    (z : ℂ) (hz : ∀ k, z ≠ (r k : ℂ))
    (A : Finset (Fin (m+q))) (ha : Fin.castAdd q i ∉ A) (u : ℝ) :
    (∫ t in {t | Function.update y i t ∈ closedPhysicalCell L X s b S},
      Complex.exp (Complex.I*z*(u-t)) * chartPrimitive S c r (Function.update y i t) s z A) =
      Complex.exp (Complex.I*z*(u-fiberUpper L X y s b S i)) *
        chartPrimitive S c r (Function.update y i (fiberUpper L X y s b S i)) s z (insert (Fin.castAdd q i) A) -
      Complex.exp (Complex.I*z*(u-fiberLower X y s b S i)) *
        chartPrimitive S c r (Function.update y i (fiberLower X y s b S i)) s z (insert (Fin.castAdd q i) A) := by
  classical
  have hb := fiber_bounds L X y s b S i hy
  rw [closedPhysicalCell_fiber L X y s b S i hy,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hb.1.trans hb.2)]
  simp only [chartPrimitive,mergeChart_update,activeRanks_insert]
  exact integral_primitive_update c r (mergeChart S y s) (selectedRank S i) z hz
    (activeRanks S A) (rank_notMem S A _ ha) u _ _

/-- The added bounded-chamber notation imposes no extra restriction on the
original rectangle/chart intersection when outputs and spectators are physical. -/
theorem closedPhysicalCell_iff {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (hX : X ∈ BetheWavefunctions.chamber m L) (hs : ∀ j, s j ∈ Icc 0 L) :
    y ∈ closedPhysicalCell L X s b S ↔
      y ∈ closedRectangle L X b ∧ y ∈ chartSet S s := by
  constructor
  · intro h; exact ⟨h.1,h.2.1⟩
  · rintro ⟨hy,hchart⟩
    have hb (i : Fin m) : y i ∈ Icc 0 L := by
      have h := hy i
      cases b
      · change lower X i ≤ y i ∧ y i ≤ X i at h
        exact ⟨(lower_bounds hX i).1.trans h.1,h.2.trans (hX.2 i).2.le⟩
      · change X i ≤ y i ∧ y i ≤ upper L X i at h
        exact ⟨(hX.2 i).1.le.trans h.1,h.2.trans (upper_bounds hX i).2⟩
    refine ⟨hy,hchart,?_⟩
    intro k
    obtain ⟨j,rfl⟩ := (mergePermutation S).surjective k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [mergeChart] using hb i
    · simpa [mergeChart] using hs i

/-- Both explicitly computed endpoints remain in the same complete closed
cell; zero-length fibers are retained with both endpoint evaluations. -/
theorem fiber_endpoints_mem {m q : ℕ} (L : ℝ) (X y : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q) (i : Fin m)
    (hy : y ∈ closedPhysicalCell L X s b S) :
    Function.update y i (fiberLower X y s b S i) ∈ closedPhysicalCell L X s b S ∧
      Function.update y i (fiberUpper L X y s b S i) ∈ closedPhysicalCell L X s b S := by
  have hb := fiber_bounds L X y s b S i hy
  have he := closedPhysicalCell_fiber L X y s b S i hy
  constructor
  · exact (Set.ext_iff.mp he _).mpr ⟨le_rfl,hb.1.trans hb.2⟩
  · exact (Set.ext_iff.mp he _).mpr ⟨hb.1.trans hb.2,le_rfl⟩

/-- At no pending integrations the chart primitive is exactly the literal
symmetric source at the original appended inputs, including collisions. -/
theorem chartPrimitive_empty_source {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (y : Fin m → ℝ) (s : Fin q → ℝ) (S : PlacementSubset m q)
    (hy : y ∈ chartSet S s) (z : ℂ) :
    chartPrimitive S c (BetheSmooth.sourceRoots L n c) y s z ∅ =
      BetheExtension.symmetricExtension L c n (Fin.append y s) := by
  classical
  simp only [chartPrimitive,activeRanks,Finset.image_empty,primitive_empty]
  have he := BetheExtension.symmetricExtension_eq L c n hy
  rw [show BetheWavefunctions.wavefunction L c n (mergeChart S y s) =
    BetheWavefunctions.coordinateAnsatz c (BetheSmooth.sourceRoots L n c) (mergeChart S y s) from rfl] at he
  rw [← he]
  exact BetheExtension.symmetricExtension_permute L c n (Fin.append y s) (mergePermutation S).symm

/-- The initial ordinary source integral on the entire chart fiber, with
its actual two endpoints. Subsequent pending sets use the preceding theorem. -/
theorem integral_source_fiber {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (X y : Fin m → ℝ) (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (i : Fin m) (hy : y ∈ closedPhysicalCell L X s b S)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) (u : ℝ) :
    (∫ t in {t | Function.update y i t ∈ closedPhysicalCell L X s b S},
      Complex.exp (Complex.I*z*(u-t)) *
        BetheExtension.symmetricExtension L c n (Fin.append (Function.update y i t) s)) =
      Complex.exp (Complex.I*z*(u-fiberUpper L X y s b S i)) *
        chartPrimitive S c (BetheSmooth.sourceRoots L n c)
          (Function.update y i (fiberUpper L X y s b S i)) s z {Fin.castAdd q i} -
      Complex.exp (Complex.I*z*(u-fiberLower X y s b S i)) *
        chartPrimitive S c (BetheSmooth.sourceRoots L n c)
          (Function.update y i (fiberLower X y s b S i)) s z {Fin.castAdd q i} := by
  have he := integral_chartPrimitive_fiber L c (BetheSmooth.sourceRoots L n c)
    X y s b S i hy z hz ∅ (Finset.notMem_empty _) u
  simp only [Finset.insert_empty] at he
  rw [← he]
  apply setIntegral_congr_fun
    (by rw [closedPhysicalCell_fiber L X y s b S i hy]; exact measurableSet_Icc)
  intro t ht
  exact congrArg (fun w : ℂ => Complex.exp (Complex.I*z*(u-t)) * w)
    (chartPrimitive_empty_source L c n (Function.update y i t) s S ht.2.1 z).symm

end QuantumNLS.BetheChartFiberSteps

#print axioms QuantumNLS.BetheChartFiberSteps.boundedChamber
#print axioms QuantumNLS.BetheChartFiberSteps.boundedChamber_update_iff
#print axioms QuantumNLS.BetheChartFiberSteps.mergeChart_update
#print axioms QuantumNLS.BetheChartFiberSteps.closedPhysicalCell
#print axioms QuantumNLS.BetheChartFiberSteps.fiberLower
#print axioms QuantumNLS.BetheChartFiberSteps.fiberUpper
#print axioms QuantumNLS.BetheChartFiberSteps.closedPhysicalCell_fiber
#print axioms QuantumNLS.BetheChartFiberSteps.fiber_bounds
#print axioms QuantumNLS.BetheChartFiberSteps.integral_chartPrimitive_fiber
#print axioms QuantumNLS.BetheChartFiberSteps.closedPhysicalCell_iff
#print axioms QuantumNLS.BetheChartFiberSteps.fiber_endpoints_mem
#print axioms QuantumNLS.BetheChartFiberSteps.chartPrimitive_empty_source
#print axioms QuantumNLS.BetheChartFiberSteps.integral_source_fiber


set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheChartFiberSteps.integral_source_fiber,
    ``QuantumNLS.BetheChartFiberSteps.integral_chartPrimitive_fiber,
    ``QuantumNLS.BetheChartFiberSteps.closedPhysicalCell_iff,
    ``QuantumNLS.BetheChartFiberSteps.fiber_endpoints_mem,
    ``QuantumNLS.BetheIteratedIncidence.card_incidentCharts_ratio,
    ``QuantumNLS.BetheIteratedIncidence.exists_chart_weak,
    ``QuantumNLS.BetheIteratedIncidence.card_incidentCharts_constant,
    ``QuantumNLS.BetheCyclicPrimitives.integral_source_primitive_outer_pair,
    ``QuantumNLS.BethePrimitiveTransport.source_spectator_face_seam_ae,
    ``QuantumNLS.BethePhysicalFaceCharts.source_transferTerm_charts_ae]
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
  for n in #[``QuantumNLS.BetheChartFiberSteps.closedPhysicalCell_fiber,
      ``QuantumNLS.BetheChartFiberSteps.boundedChamber_update_iff,
      ``QuantumNLS.BetheChartFiberSteps.mergeChart_update,
      ``QuantumNLS.BetheIteratedIncidence.assemble_bijective,
      ``DomMulAct.stabilizer_card',
      ``QuantumNLS.BetheCrossDegreeFaces.integral_primitive_update,
      ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``QuantumNLS.BethePeriodic.sourceRoots_term_periodic,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Weak incidence/chart fiber aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" || n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Weak incidence/chart fiber aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Weak incidence/chart fiber aggregate audit PASS: {seen.size} transitive constants across separate roots. Exact repeated-value chart counts and complete one-coordinate fibers; frozen BIF1/BPR1/BCP1 support preserved. Complete iterated physical recurrence, global cross-degree cancellation and all-N physical eigenrelation are not derived."
