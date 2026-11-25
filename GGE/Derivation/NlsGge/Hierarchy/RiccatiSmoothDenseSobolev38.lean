import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Sobolev.SmoothFourier
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Sobolev38
open MeasureTheory Filter Topology
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

section Truncation

variable (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]

/-- Coefficient truncation to the modes `-N ≤ n ≤ N`. -/
def truncCoeff38 (N : ℕ) (x : ℤ → ℂ) : ℤ → ℂ :=
  fun n => if n ∈ Finset.Icc (-(N : ℤ)) N then x n else 0

theorem truncCoeff38_mem (N : ℕ) (x : WeightedHilbert w) :
    Memℓp (weightedCoordinates w (truncCoeff38 N (x : ℤ → ℂ))) 2 := by
  rw [weightedCoordinates_mem_l2_iff w (fun n => (hw.out n).le)]
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
  intro n hn
  simp [truncCoeff38, hn]

/-- The finite Fourier truncation of an element of the weighted Hilbert space. -/
def truncW38 (N : ℕ) (x : WeightedHilbert w) : WeightedHilbert w :=
  ⟨truncCoeff38 N (x : ℤ → ℂ), truncCoeff38_mem w N x⟩

theorem truncW38_apply (N : ℕ) (x : WeightedHilbert w) (n : ℤ) :
    (truncW38 w N x : ℤ → ℂ) n = if n ∈ Finset.Icc (-(N : ℤ)) N then (x : ℤ → ℂ) n else 0 :=
  rfl

theorem truncW38_norm_sq (N : ℕ) (x : WeightedHilbert w) :
    ‖x - truncW38 w N x‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ n ∈ Finset.Icc (-(N : ℤ)) N, w n * ‖(x : ℤ → ℂ) n‖ ^ 2 := by
  have hx := weightedHilbert_hasSum w x
  have hd : HasSum (fun n : ℤ => w n * ‖((x - truncW38 w N x : WeightedHilbert w) : ℤ → ℂ) n‖ ^ 2)
      (‖x - truncW38 w N x‖ ^ 2) := weightedHilbert_hasSum w _
  have hcoef : ∀ n : ℤ, ((x - truncW38 w N x : WeightedHilbert w) : ℤ → ℂ) n =
      if n ∈ Finset.Icc (-(N : ℤ)) N then 0 else (x : ℤ → ℂ) n := by
    intro n
    have : ((x - truncW38 w N x : WeightedHilbert w) : ℤ → ℂ) n =
        (x : ℤ → ℂ) n - (truncW38 w N x : ℤ → ℂ) n := rfl
    rw [this, truncW38_apply]
    split_ifs <;> simp
  have hfin : HasSum (fun n : ℤ => if n ∈ Finset.Icc (-(N : ℤ)) N then
      w n * ‖(x : ℤ → ℂ) n‖ ^ 2 else 0)
      (∑ n ∈ Finset.Icc (-(N : ℤ)) N, w n * ‖(x : ℤ → ℂ) n‖ ^ 2) := by
    have := hasSum_sum_of_ne_finset_zero (f := fun n : ℤ => if n ∈ Finset.Icc (-(N : ℤ)) N then
      w n * ‖(x : ℤ → ℂ) n‖ ^ 2 else 0) (s := Finset.Icc (-(N : ℤ)) N)
      (L := SummationFilter.unconditional ℤ) (fun n hn => by simp [hn])
    rwa [Finset.sum_congr rfl (g := fun n : ℤ => w n * ‖(x : ℤ → ℂ) n‖ ^ 2)
      (fun n hn => by simp only [hn, ite_true])] at this
  have h2 := hx.sub hfin
  have h3 : (fun n : ℤ => w n * ‖((x - truncW38 w N x : WeightedHilbert w) : ℤ → ℂ) n‖ ^ 2) =
      fun n : ℤ => w n * ‖(x : ℤ → ℂ) n‖ ^ 2 - (if n ∈ Finset.Icc (-(N : ℤ)) N then
        w n * ‖(x : ℤ → ℂ) n‖ ^ 2 else 0) := by
    funext n
    rw [hcoef n]
    split_ifs <;> simp
  rw [h3] at hd
  exact hd.unique h2

theorem tendsto_truncW38 (x : WeightedHilbert w) :
    Tendsto (fun N : ℕ => truncW38 w N x) atTop (𝓝 x) := by
  have hx := weightedHilbert_hasSum w x
  have hmono : Monotone (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro a b hab
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  have hcover : ∀ n : ℤ, ∃ N : ℕ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n
    refine ⟨n.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    omega
  have hat : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    tendsto_atTop_finset_of_monotone hmono hcover
  have hpart : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, w n * ‖(x : ℤ → ℂ) n‖ ^ 2)
      atTop (𝓝 (‖x‖ ^ 2)) := by
    have h0 : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, w n * ‖(x : ℤ → ℂ) n‖ ^ 2) atTop
        (𝓝 (‖x‖ ^ 2)) := hx
    exact h0.comp hat
  have hsq : Tendsto (fun N : ℕ => ‖x - truncW38 w N x‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [truncW38_norm_sq]
    have := (tendsto_const_nhds (x := ‖x‖ ^ 2)).sub hpart
    rwa [sub_self] at this
  have hn : Tendsto (fun N : ℕ => ‖x - truncW38 w N x‖) atTop (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [norm_sub_rev] using hn

end Truncation

section SmoothTruncation

/-- The real-line trigonometric polynomial with the Fourier coefficients of `x` on `|n| ≤ N`. -/
def truncField38 (r : ℝ) (N : ℕ) (x : SobolevHilbert r) : ℝ → ℂ :=
  fun t => planeField N (fun i => (show WeightedHilbert (sobolevModeWeight r) from x)
    (modeIndex N i)) (t : PhysicalCircle)

theorem truncField38_eq_sum (r : ℝ) (N : ℕ) (x : SobolevHilbert r) :
    truncField38 r N x = fun t => ∑ i : Fin (2 * N + 1),
      fourierRealTerm (modeIndex N i)
        ((show WeightedHilbert (sobolevModeWeight r) from x) (modeIndex N i)) t := rfl

theorem contDiff_truncField38 (r : ℝ) (N : ℕ) (x : SobolevHilbert r) :
    ContDiff ℝ ∞ (truncField38 r N x) := by
  rw [truncField38_eq_sum]
  exact ContDiff.sum (fun i _ => contDiff_fourierRealTerm _ _)

theorem periodic_truncField38 (r : ℝ) (N : ℕ) (x : SobolevHilbert r) :
    Function.Periodic (truncField38 r N x) 1 := by
  intro t
  unfold truncField38
  congr 1
  exact AddCircle.coe_add_period 1 t

/-- A periodic function's circle lift agrees with it everywhere. -/
theorem liftIoc_coe_eq38 (f : ℝ → ℂ) (hper : Function.Periodic f 1) (t : ℝ) :
    AddCircle.liftIoc 1 0 f (t : PhysicalCircle) = f t := by
  set m : ℤ := ⌈t⌉ - 1 with hm
  have h1 : (t - m : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    have a := Int.ceil_lt_add_one t
    have b := Int.le_ceil t
    rw [hm]
    push_cast
    constructor <;> linarith
  have hcirc : ((t - m : ℝ) : PhysicalCircle) = (t : PhysicalCircle) := by
    have : ((m : ℝ) : PhysicalCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨m, by simp⟩
    rw [AddCircle.coe_sub, this, sub_zero]
  rw [← hcirc, AddCircle.liftIoc_coe_apply h1]
  have := (hper.int_mul m) (t - m)
  simpa using this.symm

/-- The finite Fourier truncation as an element of the Sobolev carrier. -/
def truncSobolev38 (r : ℝ) (N : ℕ) (x : SobolevHilbert r) : SobolevHilbert r :=
  truncW38 (sobolevModeWeight r) N x

theorem truncSobolev38_apply (r : ℝ) (N : ℕ) (x : SobolevHilbert r) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from truncSobolev38 r N x) n =
      if n ∈ Finset.Icc (-(N : ℤ)) N then
        (show WeightedHilbert (sobolevModeWeight r) from x) n else 0 := rfl

theorem tendsto_truncSobolev38 (r : ℝ) (x : SobolevHilbert r) :
    Tendsto (fun N : ℕ => truncSobolev38 r N x) atTop (𝓝 x) :=
  tendsto_truncW38 (sobolevModeWeight r) x

/-- The circle lift of the truncated trigonometric polynomial is the finite plane field. -/
theorem lift_truncField38 (r : ℝ) (N : ℕ) (x : SobolevHilbert r) :
    riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 r N x)
        (contDiff_truncField38 r N x).continuous (periodic_truncField38 r N x) =
      planeContinuous N (fun i => (show WeightedHilbert (sobolevModeWeight r) from x)
        (modeIndex N i)) := by
  ext p
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective p
  change AddCircle.liftIoc 1 0 (truncField38 r N x) (t : PhysicalCircle) = _
  rw [liftIoc_coe_eq38 _ (periodic_truncField38 r N x) t]
  rfl

/-- The linking hypothesis of `localRemainderSobolev38_smooth` holds for the truncation,
with `u` the explicit trigonometric polynomial `truncField38`. -/
theorem truncSobolev38_link (r : ℝ) (N : ℕ) (x : SobolevHilbert r) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from truncSobolev38 r N x) n =
      physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 r N x)
          (contDiff_truncField38 r N x).continuous (periodic_truncField38 r N x))) n := by
  rw [lift_truncField38, truncSobolev38_apply]
  have hL : ContinuousMap.toLp 2 spatialMeasure ℂ (planeContinuous N (fun i =>
      (show WeightedHilbert (sobolevModeWeight r) from x) (modeIndex N i))) =
      planeL2 N (fun i => (show WeightedHilbert (sobolevModeWeight r) from x)
        (modeIndex N i)) := rfl
  rw [hL, physicalFourier_planeL2]
  split_ifs with h
  · rw [Finset.mem_Icc] at h
    obtain ⟨i, hi⟩ := modeIndex_covers N n h.1 h.2
    subst hi
    exact (physicalFourier_planeField N (fun i =>
      (show WeightedHilbert (sobolevModeWeight r) from x) (modeIndex N i)) i).symm
  · rw [Finset.mem_Icc] at h
    exact (physicalFourier_planeField_outside N _ n (by omega)).symm

/-- Sobolev elements arising from smooth period-one fields via the linking hypothesis
used in `localRemainderSobolev38_smooth`. -/
def SmoothPeriodicSobolevSet38 (r : ℝ) : Set (SobolevHilbert r) :=
  {y | ∃ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1),
    ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight r) from y) n =
      physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n}

theorem truncSobolev38_mem_smooth (r : ℝ) (N : ℕ) (x : SobolevHilbert r) :
    truncSobolev38 r N x ∈ SmoothPeriodicSobolevSet38 r :=
  ⟨truncField38 r N x, contDiff_truncField38 r N x, periodic_truncField38 r N x,
    truncSobolev38_link r N x⟩

/-- Density of Sobolev elements of smooth period-one fields in `H^r` (every real `r`). -/
theorem smoothPeriodicSobolev38_dense (r : ℝ) : Dense (SmoothPeriodicSobolevSet38 r) := by
  intro x
  rw [mem_closure_iff_seq_limit]
  exact ⟨fun N => truncSobolev38 r N x, fun N => truncSobolev38_mem_smooth r N x,
    tendsto_truncSobolev38 r x⟩

/-- Corollary: the realized local remainder is the unique continuous function on `H^{M-1}`
agreeing with the classical formula on Sobolev elements of smooth period-one fields. -/
theorem localRemainderSobolev38_unique (M : ℕ) (hM : 2 ≤ M) (β : ℕ → ℝ)
    (F : SobolevHilbert ((M - 1 : ℕ) : ℝ) → ℝ) (hF : Continuous F)
    (hagree : ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
      (x : SobolevHilbert ((M - 1 : ℕ) : ℝ)),
      (∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) →
      F x = ∑ j ∈ Finset.range (M + 1), β j *
        ((∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (formalChargeIntegrand j)).re -
          ∫ t in (0 : ℝ)..1, ‖iteratedDeriv j u t‖ ^ 2)) :
    ∀ x : SobolevHilbert ((M - 1 : ℕ) : ℝ), F x = localRemainderSobolev38 M β (toCarrier38 _ x) := by
  have hG : Continuous (fun x : SobolevHilbert ((M - 1 : ℕ) : ℝ) =>
      localRemainderSobolev38 M β (toCarrier38 _ x)) :=
    (continuous_localRemainderSobolev38 M β).comp (continuous_toCarrier38 _)
  have heq : Set.EqOn F (fun x => localRemainderSobolev38 M β (toCarrier38 _ x))
      (SmoothPeriodicSobolevSet38 ((M - 1 : ℕ) : ℝ)) := by
    rintro y ⟨u, hu, hper, hsource⟩
    show F y = localRemainderSobolev38 M β (toCarrier38 _ y)
    rw [hagree u hu hper y hsource, localRemainderSobolev38_smooth M hM β u hu hper y hsource]
  intro x
  exact congrFun (hF.ext_on (smoothPeriodicSobolev38_dense _) hG heq) x

end SmoothTruncation

end NlsGge.HierarchyRiccati.Core
