import LiebLiniger.FixedPeriod.Quantum.WickSectorMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
First literal transfer-kernel provider tranche, source KA/KD and free r=0.
The carrier is L² of Lebesgue measure on the centered fixed interval. No
coefficient operator or factorial estimate is provided as an assumption.
The integral-operator and sharp simplex-volume bridges are subsequent work.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LiebLiniger.FixedPeriod.Quantum

/-- The physical interval realization of L²(T_L), with unnormalized Lebesgue measure. -/
def transferIntervalMeasure (L : ℝ) : Measure ℝ :=
  volume.restrict (Icc (-L / 2) (L / 2))

instance transferIntervalMeasure_isFinite (L : ℝ) :
    IsFiniteMeasure (transferIntervalMeasure L) := by
  unfold transferIntervalMeasure
  infer_instance

abbrev TransferCoordinate (r : ℕ) := Fin r → ℝ

abbrev transferCoordinateMeasure (L : ℝ) (r : ℕ) : Measure (TransferCoordinate r) :=
  Measure.pi fun _ => transferIntervalMeasure L

abbrev transferKernelMeasure (L : ℝ) (r : ℕ) :
    Measure (TransferCoordinate r × TransferCoordinate r) :=
  (transferCoordinateMeasure L r).prod (transferCoordinateMeasure L r)

/-- Exactly α<y₀<x₀<⋯<y_(r-1)<x_(r-1)<β, expressed without partial indices. -/
def transferOrderingA (L : ℝ) (r : ℕ) :
    Set (TransferCoordinate r × TransferCoordinate r) :=
  {z | (∀ i, -L / 2 < z.2 i ∧ z.2 i < z.1 i ∧ z.1 i < L / 2) ∧
    ∀ i j, i < j → z.1 i < z.2 j}

/-- Exactly α<x₀<y₀<⋯<x_(r-1)<y_(r-1)<β. -/
def transferOrderingD (L : ℝ) (r : ℕ) :
    Set (TransferCoordinate r × TransferCoordinate r) :=
  {z | (z.2, z.1) ∈ transferOrderingA L r}

/-- The source phase uses the same x-y sign in both kernels. -/
def transferDisplacement {r : ℕ} (z : TransferCoordinate r × TransferCoordinate r) : ℝ :=
  ∑ i, (z.1 i - z.2 i)

private theorem sum_disjoint_lengths_le (r : ℕ) (a b : ℝ)
    (x y : Fin r → ℝ) (hab : a ≤ b)
    (ha : ∀ i, a ≤ y i) (hxy : ∀ i, y i ≤ x i) (hb : ∀ i, x i ≤ b)
    (hord : ∀ i j, i < j → x i ≤ y j) :
    (∑ i, (x i - y i)) ≤ b - a := by
  induction r generalizing a b with
  | zero => simpa only [Fin.sum_univ_zero] using sub_nonneg.mpr hab
  | succ r ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (x 0) b (fun i => x i.succ) (fun i => y i.succ) (hb 0)
      (fun i => hord 0 i.succ (Fin.succ_pos i))
      (fun i => hxy i.succ) (fun i => hb i.succ)
      (fun i j hij => hord i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij))
    linarith [ha 0]

theorem transferDisplacement_mem_Icc_A {L : ℝ} (hL : 0 ≤ L) {r : ℕ}
    {z : TransferCoordinate r × TransferCoordinate r} (hz : z ∈ transferOrderingA L r) :
    transferDisplacement z ∈ Icc 0 L := by
  constructor
  · exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hz.1 i).2.1.le
  · have h := sum_disjoint_lengths_le r (-L / 2) (L / 2) z.1 z.2 (by linarith)
      (fun i => (hz.1 i).1.le) (fun i => (hz.1 i).2.1.le)
      (fun i => (hz.1 i).2.2.le) (fun i j hij => (hz.2 i j hij).le)
    dsimp only [transferDisplacement]
    linarith

theorem transferDisplacement_swap {r : ℕ} (z : TransferCoordinate r × TransferCoordinate r) :
    transferDisplacement (z.2, z.1) = -transferDisplacement z := by
  simp only [transferDisplacement, neg_sub, ← Finset.sum_neg_distrib]

theorem transferDisplacement_mem_Icc_D {L : ℝ} (hL : 0 ≤ L) {r : ℕ}
    {z : TransferCoordinate r × TransferCoordinate r} (hz : z ∈ transferOrderingD L r) :
    transferDisplacement z ∈ Icc (-L) 0 := by
  have h := transferDisplacement_mem_Icc_A hL hz
  rw [transferDisplacement_swap] at h
  constructor <;> linarith [h.1, h.2]

/-- The exact A exponential, before the ordering indicator. -/
def transferPhaseA (L : ℝ) (ζ : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ζ * (L : ℂ) / 2) * Complex.exp (Complex.I * ζ * (s : ℂ))

/-- The exact D exponential, before the ordering indicator. -/
def transferPhaseD (L : ℝ) (ζ : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ζ * (L : ℂ) / 2) * Complex.exp (Complex.I * ζ * (s : ℂ))

private theorem norm_centered_phase_le (L t : ℝ) (ζ : ℂ) (ht : |t| ≤ L / 2) :
    ‖Complex.exp (Complex.I * ζ * (t : ℂ))‖ ≤ Real.exp (L * |ζ.im| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hr : (Complex.I * ζ * (t : ℂ)).re = -ζ.im * t := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hr]
  calc
    -ζ.im * t ≤ |-ζ.im * t| := le_abs_self _
    _ = |ζ.im| * |t| := by rw [abs_mul, abs_neg]
    _ ≤ |ζ.im| * (L / 2) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    _ = L * |ζ.im| / 2 := by ring

theorem transferPhaseA_norm_le {L s : ℝ} (ζ : ℂ) (hs : s ∈ Icc 0 L) :
    ‖transferPhaseA L ζ s‖ ≤ Real.exp (L * |ζ.im| / 2) := by
  have he : transferPhaseA L ζ s = Complex.exp (Complex.I * ζ * ((s - L / 2 : ℝ) : ℂ)) := by
    unfold transferPhaseA
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact norm_centered_phase_le L (s - L / 2) ζ
    (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)

theorem transferPhaseD_norm_le {L s : ℝ} (ζ : ℂ) (hs : s ∈ Icc (-L) 0) :
    ‖transferPhaseD L ζ s‖ ≤ Real.exp (L * |ζ.im| / 2) := by
  have he : transferPhaseD L ζ s = Complex.exp (Complex.I * ζ * ((s + L / 2 : ℝ) : ℂ)) := by
    unfold transferPhaseD
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact norm_centered_phase_le L (s + L / 2) ζ
    (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)

/-- Literal unsymmetrized A transfer kernel. -/
def transferKernelA (L : ℝ) (ζ : ℂ) (r : ℕ) :
    TransferCoordinate r × TransferCoordinate r → ℂ :=
  (transferOrderingA L r).indicator (fun z => transferPhaseA L ζ (transferDisplacement z))

/-- Literal unsymmetrized D transfer kernel. -/
def transferKernelD (L : ℝ) (ζ : ℂ) (r : ℕ) :
    TransferCoordinate r × TransferCoordinate r → ℂ :=
  (transferOrderingD L r).indicator (fun z => transferPhaseD L ζ (transferDisplacement z))

theorem measurableSet_transferOrderingA (L : ℝ) (r : ℕ) :
    MeasurableSet (transferOrderingA L r) := by
  unfold transferOrderingA
  apply measurableSet_setOfPred.mpr
  fun_prop

theorem measurableSet_transferOrderingD (L : ℝ) (r : ℕ) :
    MeasurableSet (transferOrderingD L r) :=
  (measurableSet_transferOrderingA L r).preimage measurable_swap

theorem measurable_transferKernelA (L : ℝ) (ζ : ℂ) (r : ℕ) :
    Measurable (transferKernelA L ζ r) := by
  apply Measurable.indicator _ (measurableSet_transferOrderingA L r)
  unfold transferPhaseA transferDisplacement
  fun_prop

theorem measurable_transferKernelD (L : ℝ) (ζ : ℂ) (r : ℕ) :
    Measurable (transferKernelD L ζ r) := by
  apply Measurable.indicator _ (measurableSet_transferOrderingD L r)
  unfold transferPhaseD transferDisplacement
  fun_prop

theorem transferKernelA_norm_le {L : ℝ} (hL : 0 ≤ L) (ζ : ℂ) (r : ℕ)
    (z : TransferCoordinate r × TransferCoordinate r) :
    ‖transferKernelA L ζ r z‖ ≤ Real.exp (L * |ζ.im| / 2) := by
  by_cases hz : z ∈ transferOrderingA L r
  · rw [transferKernelA, Set.indicator_of_mem hz]
    exact transferPhaseA_norm_le ζ (transferDisplacement_mem_Icc_A hL hz)
  · rw [transferKernelA, Set.indicator_of_notMem hz, norm_zero]
    exact (Real.exp_pos _).le

theorem transferKernelD_norm_le {L : ℝ} (hL : 0 ≤ L) (ζ : ℂ) (r : ℕ)
    (z : TransferCoordinate r × TransferCoordinate r) :
    ‖transferKernelD L ζ r z‖ ≤ Real.exp (L * |ζ.im| / 2) := by
  by_cases hz : z ∈ transferOrderingD L r
  · rw [transferKernelD, Set.indicator_of_mem hz]
    exact transferPhaseD_norm_le ζ (transferDisplacement_mem_Icc_D hL hz)
  · rw [transferKernelD, Set.indicator_of_notMem hz, norm_zero]
    exact (Real.exp_pos _).le

theorem memLp_transferKernelA {L : ℝ} (hL : 0 ≤ L) (ζ : ℂ) (r : ℕ) :
    MemLp (transferKernelA L ζ r) 2 (transferKernelMeasure L r) :=
  MemLp.of_bound (measurable_transferKernelA L ζ r).aestronglyMeasurable
    (Real.exp (L * |ζ.im| / 2)) (Filter.Eventually.of_forall (transferKernelA_norm_le hL ζ r))

theorem memLp_transferKernelD {L : ℝ} (hL : 0 ≤ L) (ζ : ℂ) (r : ℕ) :
    MemLp (transferKernelD L ζ r) 2 (transferKernelMeasure L r) :=
  MemLp.of_bound (measurable_transferKernelD L ζ r).aestronglyMeasurable
    (Real.exp (L * |ζ.im| / 2)) (Filter.Eventually.of_forall (transferKernelD_norm_le hL ζ r))

/-- The free scalar is defined separately, including the vacuum. -/
def transferVacuumScalar (L : ℝ) (ζ : ℂ) : ℂ :=
  2 * Complex.cos (ζ * (L : ℂ) / 2)

/-- The raw literal coefficient kernel; degree zero is the source free scalar. -/
def transferCoefficientRawKernel (L : ℝ) (ζ : ℂ) (r : ℕ) :
    TransferCoordinate r × TransferCoordinate r → ℂ :=
  if r = 0 then fun _ => transferVacuumScalar L ζ
  else transferKernelA L ζ r + transferKernelD L ζ r

@[simp] theorem transferCoefficientRawKernel_zero (L : ℝ) (ζ : ℂ) :
    transferCoefficientRawKernel L ζ 0 = fun _ => transferVacuumScalar L ζ := by
  simp only [transferCoefficientRawKernel, ite_true]

theorem memLp_transferCoefficientRawKernel {L : ℝ} (hL : 0 ≤ L) (ζ : ℂ) (r : ℕ) :
    MemLp (transferCoefficientRawKernel L ζ r) 2 (transferKernelMeasure L r) := by
  by_cases hr : r = 0
  · simp only [transferCoefficientRawKernel, if_pos hr]
    exact memLp_const _
  · simp only [transferCoefficientRawKernel, if_neg hr]
    exact (memLp_transferKernelA hL ζ r).add (memLp_transferKernelD hL ζ r)

/-- An actual L² kernel, before separate input/output permutation averaging. -/
def transferCoefficientRawKernelL2 {L : ℝ} (hL : 0 ≤ L) (ζ : ℂ) (r : ℕ) :
    Lp ℂ 2 (transferKernelMeasure L r) :=
  (memLp_transferCoefficientRawKernel hL ζ r).toLp (transferCoefficientRawKernel L ζ r)

end LiebLiniger.FixedPeriod.Quantum
