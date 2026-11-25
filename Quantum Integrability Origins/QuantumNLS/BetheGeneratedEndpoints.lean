import QuantumNLS.BetheResidualFibers
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Finset.Max

/-! Fixed clipped boxes for the physical interlacing cells. All mixed
constraints are against fixed spectators; moving/moving inequalities already
follow from the original alternating rectangle, even at collisions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheGeneratedEndpoints
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheChartFiberSteps BetheResidualFibers
open BethePrimitiveTransport BetheInternalFaces BetheWavefunctions

def lowerCandidates {m q : ℕ} (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) : Finset ℝ :=
  insert (rectangleLower X b i)
    ((Finset.univ.filter (fun j => selectedRank S i ≤ spectatorRank S j)).image s)

def upperCandidates {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) : Finset ℝ :=
  insert (rectangleUpper L X b i)
    ((Finset.univ.filter (fun j => spectatorRank S j ≤ selectedRank S i)).image s)

def clipLower {m q : ℕ} (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) : ℝ :=
  (lowerCandidates X s b S i).max' ⟨_, Finset.mem_insert_self _ _⟩

def clipUpper {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) : ℝ :=
  (upperCandidates L X s b S i).min' ⟨_, Finset.mem_insert_self _ _⟩

theorem clipLower_le_iff {m q : ℕ} (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) (t : ℝ) :
    clipLower X s b S i ≤ t ↔ rectangleLower X b i ≤ t ∧
      ∀ j, selectedRank S i ≤ spectatorRank S j → s j ≤ t := by
  simp [clipLower, lowerCandidates, Finset.max'_le_iff]

theorem le_clipUpper_iff {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) (t : ℝ) :
    t ≤ clipUpper L X s b S i ↔ t ≤ rectangleUpper L X b i ∧
      ∀ j, spectatorRank S j ≤ selectedRank S i → t ≤ s j := by
  simp [clipUpper, upperCandidates, Finset.le_min'_iff]

/-- Endpoint values have original-rectangle or spectator provenance.
Ties do not create extra endpoint summands. -/
theorem clipLower_provenance {m q : ℕ} (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) :
    clipLower X s b S i = rectangleLower X b i ∨
      ∃ j, selectedRank S i ≤ spectatorRank S j ∧ clipLower X s b S i = s j := by
  have h := Finset.max'_mem (lowerCandidates X s b S i) ⟨_, Finset.mem_insert_self _ _⟩
  simpa [lowerCandidates, clipLower, eq_comm] using h

theorem clipUpper_provenance {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (S : PlacementSubset m q) (i : Fin m) :
    clipUpper L X s b S i = rectangleUpper L X b i ∨
      ∃ j, spectatorRank S j ≤ selectedRank S i ∧ clipUpper L X s b S i = s j := by
  have h := Finset.min'_mem (upperCandidates L X s b S i) ⟨_, Finset.mem_insert_self _ _⟩
  simpa [upperCandidates, clipUpper, eq_comm] using h

/-- A literal physical chart cell is a fixed box, including empty boxes.
No surviving moving coordinate occurs in its clipped endpoints. -/
theorem closedPhysicalCell_eq_box {m q : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (hX : X ∈ chamber m L) (hs : Antitone s) (hb : ∀ j, s j ∈ Icc 0 L) :
    closedPhysicalCell L X s b S = Icc (clipLower X s b S) (clipUpper L X s b S) := by
  ext y
  rw [closedPhysicalCell_iff L X y s b S hX hb, closedCell_iff L X y s b S hs]
  change (_ ∧ _) ↔ ((∀ i, _) ∧ ∀ i, _)
  simp only [clipLower_le_iff, le_clipUpper_iff, closedRectangle, mem_ofPred_eq,
    mem_Icc, crossConstraints]
  constructor
  · rintro ⟨hr, hc⟩
    exact ⟨fun i => ⟨(hr i).1, fun j => (hc i j).1⟩,
      fun i => ⟨(hr i).2, fun j => (hc i j).2⟩⟩
  · rintro ⟨hl, hu⟩
    exact ⟨fun i => ⟨(hl i).1, (hu i).1⟩,
      fun i j => ⟨(hl i).2 j, (hu i).2 j⟩⟩

/-- Exact full fiber of the fixed box at any original label. -/
theorem box_fiber {m : ℕ} (lo hi y : Fin m → ℝ) (i : Fin m) :
    {t | Function.update y i t ∈ Icc lo hi} =
      if ∀ j, j ≠ i → y j ∈ Icc (lo j) (hi j) then Icc (lo i) (hi i) else ∅ := by
  classical
  ext t
  simp only [mem_ofPred_eq, mem_Icc, Pi.le_def]
  split_ifs with h
  · constructor
    · intro ht
      exact ⟨by simpa using ht.1 i, by simpa using ht.2 i⟩
    · intro ht
      constructor <;> intro j <;> by_cases hj : j = i
      · subst j; simpa using ht.1
      · simpa [hj] using (h j hj).1
      · subst j; simpa using ht.2
      · simpa [hj] using (h j hj).2
  · simp only [mem_empty_iff_false, iff_false]
    intro ht
    apply h
    intro j hj
    exact ⟨by simpa [hj] using ht.1 j, by simpa [hj] using ht.2 j⟩

theorem planeWave_merge {m q : ℕ} (S : PlacementSubset m q)
    (r : Fin (m+q) → ℝ) (y : Fin m → ℝ) (s : Fin q → ℝ) :
    planeWave r (mergeChart S y s) =
      Complex.exp (Complex.I * ((∑ i, r (selectedRank S i)*y i) +
        (∑ j, r (spectatorRank S j)*s j) : ℝ)) := by
  unfold planeWave
  congr 3
  rw [← Equiv.sum_comp (mergePermutation S) (fun k => r k * mergeChart S y s k),
    Fin.sum_univ_add]
  simp [selectedRank, spectatorRank, mergeChart]

def assignmentConstant {m q : ℕ} (z : ℂ) (u : ℝ) (S : PlacementSubset m q)
    (r : Fin (m+q) → ℝ) (s : Fin q → ℝ) : ℂ :=
  Complex.exp (Complex.I*z*u) *
    Complex.exp (Complex.I * ((∑ j, r (spectatorRank S j)*s j : ℝ) : ℂ))

/-- Complete phase factorization, with the original moving-label ranks. -/
theorem weighted_planeWave_merge {m q : ℕ} (z : ℂ) (u : ℝ)
    (S : PlacementSubset m q) (r : Fin (m+q) → ℝ) (y : Fin m → ℝ) (s : Fin q → ℝ) :
    Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) * planeWave r (mergeChart S y s) =
      assignmentConstant z u S r s *
        ∏ i, Complex.exp (frequency z (r (selectedRank S i)) * (y i : ℂ)) := by
  rw [planeWave_merge, ← Complex.exp_sum]
  simp only [assignmentConstant, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [frequency, mul_sub, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

def expEndpoint (k : ℂ) (lo hi : ℝ) : ℂ :=
  (Complex.exp (k*(hi : ℂ)) - Complex.exp (k*(lo : ℂ))) / k

theorem integral_exp_Icc {k : ℂ} (hk : k ≠ 0) (lo hi : ℝ) (h : lo ≤ hi) :
    (∫ t in Icc lo hi, Complex.exp (k*(t : ℂ))) = expEndpoint k lo hi := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
    integral_exp_mul_complex hk]
  rfl

/-- Product integration uses the actual restricted product measure.
No orientation convention is substituted for an empty physical interval. -/
theorem integral_exp_box {m : ℕ} (lo hi : Fin m → ℝ) (k : Fin m → ℂ)
    (hk : ∀ i, k i ≠ 0) (h : lo ≤ hi) :
    (∫ y in Icc lo hi, ∏ i, Complex.exp (k i * (y i : ℂ))) =
      ∏ i, expEndpoint (k i) (lo i) (hi i) := by
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (i : Fin m) (t : ℝ) => Complex.exp (k i * (t : ℂ)))]
  exact Finset.prod_congr rfl (fun i _ => integral_exp_Icc (hk i) _ _ (h i))

theorem integral_weighted_planeWave_box {m q : ℕ} (z : ℂ) (u : ℝ)
    (S : PlacementSubset m q) (r : Fin (m+q) → ℝ) (s : Fin q → ℝ)
    (lo hi : Fin m → ℝ) (h : lo ≤ hi) (hz : ∀ j, z ≠ (r j : ℂ)) :
    (∫ y in Icc lo hi,
      Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) * planeWave r (mergeChart S y s)) =
      assignmentConstant z u S r s *
        ∏ i, expEndpoint (frequency z (r (selectedRank S i))) (lo i) (hi i) := by
  simp_rw [weighted_planeWave_merge]
  rw [integral_const_mul, integral_exp_box lo hi _
    (fun i => frequency_ne_zero (hz (selectedRank S i))) h]

def cornerTuple {m : ℕ} (lo hi : Fin m → ℝ) (ε : Fin m → Bool) : Fin m → ℝ :=
  fun i => if ε i then hi i else lo i

def orientation {m : ℕ} (ε : Fin m → Bool) : ℂ :=
  ∏ i, if ε i then 1 else -1

theorem prod_expEndpoint {m : ℕ} (lo hi : Fin m → ℝ) (k : Fin m → ℂ) :
    (∏ i, expEndpoint (k i) (lo i) (hi i)) =
      ∑ ε : Fin m → Bool, orientation ε *
        (∏ i, Complex.exp (k i * (cornerTuple lo hi ε i : ℂ))) * ∏ i, (k i)⁻¹ := by
  have he (i : Fin m) : expEndpoint (k i) (lo i) (hi i) =
      ∑ b : Bool, (if b then (1 : ℂ) else -1) *
        Complex.exp (k i * ((if b then hi i else lo i : ℝ) : ℂ)) * (k i)⁻¹ := by
    simp [expEndpoint, div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ε _
  simp only [Finset.prod_mul_distrib, orientation, cornerTuple]

/-- Exhaustive signed endpoint expansion for every moving coordinate.
The labels remain distinct when upper and lower values coincide. -/
theorem integral_weighted_planeWave_corners {m q : ℕ} (z : ℂ) (u : ℝ)
    (S : PlacementSubset m q) (r : Fin (m+q) → ℝ) (s : Fin q → ℝ)
    (lo hi : Fin m → ℝ) (h : lo ≤ hi) (hz : ∀ j, z ≠ (r j : ℂ)) :
    (∫ y in Icc lo hi,
      Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) * planeWave r (mergeChart S y s)) =
      ∑ ε : Fin m → Bool, orientation ε *
        (Complex.exp (Complex.I*z*((u-∑ i, cornerTuple lo hi ε i : ℝ) : ℂ)) *
          planeWave r (mergeChart S (cornerTuple lo hi ε) s)) *
          ∏ i, (frequency z (r (selectedRank S i)))⁻¹ := by
  rw [integral_weighted_planeWave_box z u S r s lo hi h hz,
    prod_expEndpoint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  rw [weighted_planeWave_merge]
  ring

theorem denominator_allMoving {m q : ℕ} (z : ℂ) (S : PlacementSubset m q)
    (r : Fin (m+q) → ℝ) :
    denominator z r (activeRanks S (firstPositions (p := m) (q := q))) =
      ∏ i : Fin m, (frequency z (r (selectedRank S i)))⁻¹ := by
  classical
  unfold denominator activeRanks firstPositions
  rw [Finset.prod_image (fun _ _ _ _ h => (mergePermutation S).injective h),
    Finset.prod_map]
  rfl

/-- All integrations of one chart ansatz are evaluated, with its complete
pending denominator set. This is an identity of actual box integrals. -/
theorem integral_ansatz_box_corners {m q : ℕ} (c : ℝ) (r : Fin (m+q) → ℝ)
    (z : ℂ) (hz : ∀ j, z ≠ (r j : ℂ)) (u : ℝ) (S : PlacementSubset m q)
    (s : Fin q → ℝ) (lo hi : Fin m → ℝ) (h : lo ≤ hi) :
    (∫ y in Icc lo hi, Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) *
      coordinateAnsatz c r (mergeChart S y s)) =
      ∑ ε : Fin m → Bool, orientation ε *
        Complex.exp (Complex.I*z*((u-∑ i, cornerTuple lo hi ε i : ℝ) : ℂ)) *
        chartPrimitive S c r (cornerTuple lo hi ε) s z (firstPositions (p := m) (q := q)) := by
  classical
  have hi' (σ : Equiv.Perm (Fin (m+q))) : IntegrableOn
      (fun y : Fin m → ℝ => coefficient c (r ∘ σ) *
        (Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) * planeWave (r ∘ σ) (mergeChart S y s)))
      (Icc lo hi) := by
    apply Continuous.integrableOn_Icc
    unfold planeWave mergeChart
    fun_prop
  have he (y : Fin m → ℝ) :
      Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) * coordinateAnsatz c r (mergeChart S y s) =
      ∑ σ : Equiv.Perm (Fin (m+q)), coefficient c (r ∘ σ) *
        (Complex.exp (Complex.I*z*((u-∑ i, y i : ℝ) : ℂ)) * planeWave (r ∘ σ) (mergeChart S y s)) := by
    simp only [coordinateAnsatz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun σ _ => hi' σ)]
  have hEval := fun σ : Equiv.Perm (Fin (m+q)) =>
    integral_weighted_planeWave_corners z u S (r ∘ σ) s lo hi h (fun j => hz (σ j))
  simp_rw [integral_const_mul, hEval]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ε _
  simp only [chartPrimitive, primitive, Finset.mul_sum, denominator_allMoving]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem card_cornerAssignments (m : ℕ) : Fintype.card (Fin m → Bool) = 2^m := by
  simp

/-- Exact multiplicity of each endpoint tuple, including every collapsed
interval. Equal candidate values have no extra provenance multiplicity. -/
theorem card_cornerFiber {m : ℕ} (lo hi y : Fin m → ℝ) :
    Fintype.card {ε : Fin m → Bool // cornerTuple lo hi ε = y} =
      ∏ i, ((if hi i = y i then 1 else 0) + (if lo i = y i then 1 else 0) : ℕ) := by
  classical
  let e : {ε : Fin m → Bool // cornerTuple lo hi ε = y} ≃
      (∀ i : Fin m, {b : Bool // (if b then hi i else lo i) = y i}) :=
    (Equiv.subtypeEquivRight (fun ε => by simp only [cornerTuple, funext_iff])).trans
      Equiv.subtypePiEquivPi
  rw [Fintype.card_congr e, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hh : hi i = y i <;> by_cases hl : lo i = y i <;>
    simp [Fintype.card_subtype, Finset.filter_insert,
      Finset.filter_singleton, hh, hl]

theorem cornerTuple_mem_box {m : ℕ} (lo hi : Fin m → ℝ) (h : lo ≤ hi)
    (ε : Fin m → Bool) : cornerTuple lo hi ε ∈ Icc lo hi := by
  constructor <;> intro i <;> dsimp only [cornerTuple] <;> split_ifs <;>
    first | exact h i | exact le_rfl

/-- The full scalar branch offset. In particular minus retains L. -/
def branchOffset {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool) : ℝ :=
  (if b then L else 0) + ∑ i, X i

theorem branch_displacement {m : ℕ} (L : ℝ) (X y : Fin m → ℝ) (b : Bool) :
    (if b then L else 0) + BetheTransferKernelAdjoint.displacement X y =
      branchOffset L X b - ∑ i, y i := by
  simp only [branchOffset, BetheTransferKernelAdjoint.displacement, Finset.sum_sub_distrib]
  ring

def sourceCorners {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q) : ℂ :=
  if clipLower X s b S ≤ clipUpper L X s b S then
    ∑ ε : Fin m → Bool, orientation ε *
      Complex.exp (Complex.I*z*((branchOffset L X b -
        ∑ i, cornerTuple (clipLower X s b S) (clipUpper L X s b S) ε i : ℝ) : ℂ)) *
      chartPrimitive S c (BetheSmooth.sourceRoots L n c)
        (cornerTuple (clipLower X s b S) (clipUpper L X s b S) ε) s z
        (firstPositions (p := m) (q := q))
  else 0

/-- Complete endpoint enumeration of the actual closed-cell branch source,
for all degrees. Empty cells contribute zero before endpoint evaluation. -/
theorem integral_branchSource_corners {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ))
    (X : Fin m → ℝ) (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset m q)
    (hX : X ∈ chamber m L) (hs : Antitone s) (hb : ∀ j, s j ∈ Icc 0 L) :
    (∫ y in closedPhysicalCell L X s b S, branchSource L c n z X s b y) =
      sourceCorners L c n z X s b S := by
  classical
  let lo := clipLower X s b S
  let hi := clipUpper L X s b S
  have hbox := closedPhysicalCell_eq_box L X s b S hX hs hb
  by_cases h : lo ≤ hi
  · change _ = if lo ≤ hi then _ else _
    rw [ite_eq_left h, hbox]
    trans ∫ y in Icc lo hi,
      Complex.exp (Complex.I*z*((branchOffset L X b - ∑ i, y i : ℝ) : ℂ)) *
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) (mergeChart S y s)
    · apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      have hc : y ∈ closedPhysicalCell L X s b S := by rw [hbox]; exact hy
      have he := chartPrimitive_empty_source L c n y s S hc.2.1 z
      simp only [chartPrimitive, activeRanks, Finset.image_empty, primitive_empty] at he
      simp only [branchSource, ← Complex.ofReal_add, branch_displacement, he]
    · exact integral_ansatz_box_corners c _ z hz (branchOffset L X b) S s lo hi h
  · have hempty : Icc lo hi = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact h (hy.1.trans hy.2)
    change _ = if lo ≤ hi then _ else _
    rw [ite_eq_right h, hbox, hempty]
    simp

/-- The BPR1 chart integral after *all* ordinary integrations, not only
its original rectangle faces. Spectator clipping generates the extra faces. -/
theorem integral_rawSource_corners {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ))
    (X : Fin m → ℝ) (s : Fin q → ℝ) (S : PlacementSubset m q)
    (hX : X ∈ chamber m L) (hs : Antitone s) (hb : ∀ j, s j ∈ Icc 0 L) :
    (∫ y in chartSet S s, rawSource L c n z X s y ∂BetheWeakGradient.cubeMeasure m L) =
      sourceCorners L c n z X s false S + sourceCorners L c n z X s true S := by
  rw [integral_rawSource_closed_cells L c n z X s S hX hb,
    integral_branchSource_corners L c n z hz X s false S hX hs hb,
    integral_branchSource_corners L c n z hz X s true S hX hs hb]

/-- Exact endpoint-tuple multiplicity across all admissible charts.
Charts remain labelled because their primitive denominator assignments differ. -/
theorem card_generatedFiber {m q : ℕ} (L : ℝ) (X : Fin m → ℝ) (s : Fin q → ℝ)
    (b : Bool) (y : Fin m → ℝ) :
    Fintype.card {p : PlacementSubset m q × (Fin m → Bool) //
      clipLower X s b p.1 ≤ clipUpper L X s b p.1 ∧
      cornerTuple (clipLower X s b p.1) (clipUpper L X s b p.1) p.2 = y} =
      ∑ S : PlacementSubset m q,
        if clipLower X s b S ≤ clipUpper L X s b S then
          ∏ i, ((if clipUpper L X s b S i = y i then 1 else 0) +
            (if clipLower X s b S i = y i then 1 else 0) : ℕ)
        else 0 := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : clipLower X s b S ≤ clipUpper L X s b S
  · simp only [h, true_and, ite_true]
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, ← Fintype.card_subtype,
      card_cornerFiber]
  · simp [h]

/-- The first generated residual integral of BRF1 is fully evaluated by
the fixed-box route. This is not an assumption about later boundary terms. -/
theorem integral_firstEndpoints_corners {d q : ℕ} (L c : ℝ)
    (n : Fin ((d+1)+q) → ℤ) (z : ℂ)
    (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ))
    (X : Fin (d+1) → ℝ) (s : Fin q → ℝ) (b : Bool)
    (S : PlacementSubset (d+1) q) (i : Fin (d+1))
    (hX : X ∈ chamber (d+1) L) (hs : Antitone s) (hb : ∀ j, s j ∈ Icc 0 L) :
    (∫ v : Fin d → ℝ, firstEndpoints L c n z X s b S i v) =
      sourceCorners L c n z X s b S := by
  rw [← integral_branchSource_first_endpoints L c n z hz X s b S i,
    integral_branchSource_corners L c n z hz X s b S hX hs hb]

open TensorCarrier PhysicalTensor BetheHigherPlacement BetheGeneralSliceEndpoints
open BetheTransferKernelAdjoint BetheWeakGradient BetheFiniteNAction

/-- All generated corners of every actual positive-degree physical term,
with exactly c^m per output subset from the original (N)_m normalization. -/
theorem source_transferTerm_corners_ae (L : ℝ) [Fact (0 < L)]
    (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c) {n : Fin (m+q) → ℤ}
    (hn : Antitone n) (z : ℂ)
    (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), StrictAnti (representatives L x) →
      physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
        (sourceVector L hc hn)).1) x = (c : ℂ)^m *
        ∑ S : PlacementSubset m q, ∑ T : PlacementSubset m q,
          let X := fun j : Fin m => representatives L x ((mergePermutation S) (Fin.castAdd q j))
          let s := fun j : Fin q => representatives L x ((mergePermutation S) (Fin.natAdd m j))
          sourceCorners L c n z X s false T + sourceCorners L c n z X s true T := by
  have hall : ∀ᵐ x ∂torusPiMeasure L (m+q),
      ∀ k, representatives L x k ∈ Ioo 0 L :=
    Filter.eventually_all.mpr (fun k => representatives_interior_ae L _ k)
  filter_upwards [source_transferTerm_charts_ae L m q hm hc hn z, hall] with x he hint hx
  rw [he hx]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  apply integral_rawSource_corners L c n z hz _ _ T
  · constructor
    · intro a b hab
      apply hx
      simpa only [Equiv.symm_symm, mergePermutation_selected] using
        (S.1.orderEmbOfFin S.2).strictMono hab
    · intro j; exact hint _
  · intro a b hab
    apply hx.antitone
    simpa only [Equiv.symm_symm, mergePermutation_spectator] using
      (S.1ᶜ.orderEmbOfFin (complement_card S)).monotone hab
  · intro j; exact ⟨(hint _).1.le, (hint _).2.le⟩

/-- A partial generated face fixes exactly A, retaining every original
moving label. Choices outside A are not counted. -/
def partialEndpoint {m : ℕ} (lo hi : Fin m → ℝ) (A : Finset (Fin m))
    (ε : A → Bool) (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if h : i ∈ A then (if ε ⟨i,h⟩ then hi i else lo i) else y i

theorem card_partialAssignments {m : ℕ} (A : Finset (Fin m)) :
    Fintype.card (A → Bool) = 2^A.card := by simp

/-- Abstract codimension-k labels for the clipped box, before coincident
geometric faces are identified. There is no integration-order factorial. -/
theorem card_partialFaces (m k : ℕ) :
    Fintype.card (Σ A : {A : Finset (Fin m) // A.card = k}, (A.1 → Bool)) =
      Nat.choose m k * 2^k := by
  classical
  rw [Fintype.card_sigma]
  have hcard (A : {A : Finset (Fin m) // A.card = k}) :
      Fintype.card (A.1 → Bool) = 2^k := by simp [A.2]
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  simp

/-- Every generated partial face has the same residual box. Coincident
endpoints and lower-dimensional intersections need no strictness premise. -/
theorem partialEndpoint_mem_box {m : ℕ} (lo hi : Fin m → ℝ) (h : lo ≤ hi)
    (A : Finset (Fin m)) (ε : A → Bool) (y : Fin m → ℝ) :
    partialEndpoint lo hi A ε y ∈ Icc lo hi ↔
      ∀ i, i ∉ A → y i ∈ Icc (lo i) (hi i) := by
  constructor
  · intro hy i hi'
    exact ⟨by simpa [partialEndpoint, hi'] using hy.1 i,
      by simpa [partialEndpoint, hi'] using hy.2 i⟩
  · intro hy
    constructor <;> intro i <;> by_cases ha : i ∈ A
    · simp only [partialEndpoint, dite_eq_left ha]
      split_ifs <;> first | exact h i | exact le_rfl
    · simpa [partialEndpoint, ha] using (hy i ha).1
    · simp only [partialEndpoint, dite_eq_left ha]
      split_ifs <;> first | exact h i | exact le_rfl
    · simpa [partialEndpoint, ha] using (hy i ha).2

/-- A later original moving coordinate never moves any earlier clipped
endpoint. Thus no merged moving-frequency resonance is introduced. -/
theorem partialEndpoint_update {m : ℕ} (lo hi : Fin m → ℝ) (A : Finset (Fin m))
    (ε : A → Bool) (y : Fin m → ℝ) (j : Fin m) (hj : j ∉ A) (t : ℝ) :
    partialEndpoint lo hi A ε (Function.update y j t) =
      Function.update (partialEndpoint lo hi A ε y) j t := by
  classical
  ext i
  by_cases he : i = j
  · subst i; simp [partialEndpoint, hj]
  · by_cases ha : i ∈ A <;> simp [partialEndpoint, he, ha]

/-- The ordinary primitive step on an arbitrary generated partial face.
Both endpoint evaluations and the exact newly inserted original label are
retained. This theorem makes no cross-degree cancellation assumption. -/
theorem integral_partialEndpoint_step {m q : ℕ} (c : ℝ) (r : Fin (m+q) → ℝ)
    (S : PlacementSubset m q) (s : Fin q → ℝ) (lo hi : Fin m → ℝ) (h : lo ≤ hi)
    (A : Finset (Fin m)) (ε : A → Bool) (y : Fin m → ℝ) (j : Fin m) (hj : j ∉ A)
    (z : ℂ) (hz : ∀ k, z ≠ (r k : ℂ)) (P : Finset (Fin (m+q)))
    (hp : Fin.castAdd q j ∉ P) (u : ℝ) :
    (∫ t in Icc (lo j) (hi j), Complex.exp (Complex.I*z*(u-t)) *
      chartPrimitive S c r (partialEndpoint lo hi A ε (Function.update y j t)) s z P) =
      Complex.exp (Complex.I*z*(u-hi j)) *
        chartPrimitive S c r (partialEndpoint lo hi A ε (Function.update y j (hi j))) s z
          (insert (Fin.castAdd q j) P) -
      Complex.exp (Complex.I*z*(u-lo j)) *
        chartPrimitive S c r (partialEndpoint lo hi A ε (Function.update y j (lo j))) s z
          (insert (Fin.castAdd q j) P) := by
  simp_rw [partialEndpoint_update lo hi A ε y j hj]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (h j)]
  simp only [chartPrimitive, mergeChart_update, activeRanks_insert]
  exact BetheCrossDegreeFaces.integral_primitive_update c r
    (mergeChart S (partialEndpoint lo hi A ε y) s) (selectedRank S j) z hz
    (activeRanks S P) (rank_notMem S P _ hp) u (lo j) (hi j)

/-- Exact geometric-tuple multiplicity at every partial integration stage.
An incompatible residual coordinate gives zero; each collapsed eliminated
interval retains both of its separately signed endpoint labels. -/
theorem card_partialEndpointFiber {m : ℕ} (lo hi : Fin m → ℝ)
    (A : Finset (Fin m)) (y w : Fin m → ℝ) :
    Fintype.card {ε : A → Bool // partialEndpoint lo hi A ε y = w} =
      if ∀ i, i ∉ A → y i = w i then
        ∏ i : A, ((if hi i = w i then 1 else 0) + (if lo i = w i then 1 else 0) : ℕ)
      else 0 := by
  classical
  by_cases h : ∀ i, i ∉ A → y i = w i
  · rw [ite_eq_left h]
    have he (ε : A → Bool) : partialEndpoint lo hi A ε y = w ↔
        ∀ i : A, (if ε i then hi i else lo i) = w i := by
      constructor
      · intro hh i
        simpa [partialEndpoint, i.2] using congrFun hh i
      · intro hh
        funext i
        by_cases ha : i ∈ A
        · simpa [partialEndpoint, ha] using hh ⟨i,ha⟩
        · simpa [partialEndpoint, ha] using h i ha
    let e : {ε : A → Bool // partialEndpoint lo hi A ε y = w} ≃
        (∀ i : A, {b : Bool // (if b then hi i else lo i) = w i}) :=
      (Equiv.subtypeEquivRight he).trans
        (Equiv.subtypePiEquivPi (β := fun _ : A => Bool)
          (p := fun (i : A) (b : Bool) => (if b then hi i else lo i) = w i))
    rw [Fintype.card_congr e, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hh : hi i = w i <;> by_cases hl : lo i = w i <;>
      simp [Fintype.card_subtype, Finset.filter_insert, Finset.filter_singleton, hh, hl]
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun ε => h ?_⟩
    intro i hi'
    simpa [partialEndpoint, hi'] using congrFun ε.2 i

end QuantumNLS.BetheGeneratedEndpoints

#print axioms QuantumNLS.BetheGeneratedEndpoints.lowerCandidates
#print axioms QuantumNLS.BetheGeneratedEndpoints.upperCandidates
#print axioms QuantumNLS.BetheGeneratedEndpoints.clipLower
#print axioms QuantumNLS.BetheGeneratedEndpoints.clipUpper
#print axioms QuantumNLS.BetheGeneratedEndpoints.clipLower_le_iff
#print axioms QuantumNLS.BetheGeneratedEndpoints.le_clipUpper_iff
#print axioms QuantumNLS.BetheGeneratedEndpoints.clipLower_provenance
#print axioms QuantumNLS.BetheGeneratedEndpoints.clipUpper_provenance
#print axioms QuantumNLS.BetheGeneratedEndpoints.closedPhysicalCell_eq_box
#print axioms QuantumNLS.BetheGeneratedEndpoints.box_fiber
#print axioms QuantumNLS.BetheGeneratedEndpoints.planeWave_merge
#print axioms QuantumNLS.BetheGeneratedEndpoints.assignmentConstant
#print axioms QuantumNLS.BetheGeneratedEndpoints.weighted_planeWave_merge
#print axioms QuantumNLS.BetheGeneratedEndpoints.expEndpoint
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_exp_Icc
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_exp_box
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_weighted_planeWave_box
#print axioms QuantumNLS.BetheGeneratedEndpoints.cornerTuple
#print axioms QuantumNLS.BetheGeneratedEndpoints.orientation
#print axioms QuantumNLS.BetheGeneratedEndpoints.prod_expEndpoint
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_weighted_planeWave_corners
#print axioms QuantumNLS.BetheGeneratedEndpoints.denominator_allMoving
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_ansatz_box_corners
#print axioms QuantumNLS.BetheGeneratedEndpoints.card_cornerAssignments
#print axioms QuantumNLS.BetheGeneratedEndpoints.card_cornerFiber
#print axioms QuantumNLS.BetheGeneratedEndpoints.cornerTuple_mem_box
#print axioms QuantumNLS.BetheGeneratedEndpoints.branchOffset
#print axioms QuantumNLS.BetheGeneratedEndpoints.branch_displacement
#print axioms QuantumNLS.BetheGeneratedEndpoints.sourceCorners
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_branchSource_corners
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_rawSource_corners
#print axioms QuantumNLS.BetheGeneratedEndpoints.card_generatedFiber
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_firstEndpoints_corners
#print axioms QuantumNLS.BetheGeneratedEndpoints.source_transferTerm_corners_ae
#print axioms QuantumNLS.BetheGeneratedEndpoints.partialEndpoint
#print axioms QuantumNLS.BetheGeneratedEndpoints.card_partialAssignments
#print axioms QuantumNLS.BetheGeneratedEndpoints.card_partialFaces
#print axioms QuantumNLS.BetheGeneratedEndpoints.partialEndpoint_mem_box
#print axioms QuantumNLS.BetheGeneratedEndpoints.partialEndpoint_update
#print axioms QuantumNLS.BetheGeneratedEndpoints.integral_partialEndpoint_step
#print axioms QuantumNLS.BetheGeneratedEndpoints.card_partialEndpointFiber

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheGeneratedEndpoints.source_transferTerm_corners_ae,
    ``QuantumNLS.BetheGeneratedEndpoints.integral_firstEndpoints_corners,
    ``QuantumNLS.BetheGeneratedEndpoints.card_generatedFiber,
    ``QuantumNLS.BetheGeneratedEndpoints.card_partialFaces,
    ``QuantumNLS.BetheGeneratedEndpoints.card_partialEndpointFiber,
    ``QuantumNLS.BetheGeneratedEndpoints.partialEndpoint_mem_box,
    ``QuantumNLS.BetheGeneratedEndpoints.integral_partialEndpoint_step,
    ``QuantumNLS.BetheCyclicPrimitives.integral_source_primitive_outer_pair,
    ``QuantumNLS.BethePrimitiveTransport.source_spectator_face_seam_ae]
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
      ``QuantumNLS.BetheGeneratedEndpoints.closedPhysicalCell_eq_box,
      ``QuantumNLS.BetheGeneratedEndpoints.clipLower_le_iff,
      ``QuantumNLS.BetheGeneratedEndpoints.le_clipUpper_iff,
      ``QuantumNLS.BetheGeneratedEndpoints.integral_ansatz_box_corners,
      ``QuantumNLS.BetheGeneratedEndpoints.prod_expEndpoint,
      ``QuantumNLS.BetheGeneratedEndpoints.denominator_allMoving,
      ``QuantumNLS.BetheGeneratedEndpoints.card_cornerFiber,
      ``MeasureTheory.integral_fintype_prod_eq_prod,
      ``QuantumNLS.BetheResidualFibers.integral_rawSource_closed_cells,
      ``QuantumNLS.BetheResidualFibers.integral_branchSource_first_endpoints,
      ``QuantumNLS.BethePhysicalFaceCharts.source_transferTerm_charts_ae,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
      ``QuantumNLS.BetheCrossDegreeFaces.integral_primitive_update,
      ``QuantumNLS.BethePeriodic.sourceRoots_term_periodic,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Generated endpoint aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Generated endpoint aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Generated physical endpoint aggregate audit PASS: {seen.size} transitive constants across separate roots. Fixed clipped boxes, complete terminal corner expansion, exact tuple multiplicities and arbitrary partial-face primitive steps for actual positive-c transfer terms with exact normalization. Local seam and cyclic identities are separate roots; global cross-degree cancellation and all-N eigenrelation remain open."
