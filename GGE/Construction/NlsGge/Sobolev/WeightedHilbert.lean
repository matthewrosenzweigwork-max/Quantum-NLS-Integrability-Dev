import NlsGge.Sobolev.PeriodicBridge

/-! Genuine weighted square-summable sequence spaces, transported from mathlib l2. -/

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators

namespace NlsGge.Pilot

theorem weightedCoordinates_add (w : ℤ → ℝ) (x y : ℤ → ℂ) :
    weightedCoordinates w (x + y) = weightedCoordinates w x + weightedCoordinates w y := by
  funext n
  simp only [weightedCoordinates, Pi.add_apply, mul_add]

theorem weightedCoordinates_smul (w : ℤ → ℝ) (c : ℂ) (x : ℤ → ℂ) :
    weightedCoordinates w (c • x) = c • weightedCoordinates w x := by
  funext n
  simp only [weightedCoordinates, Pi.smul_apply, smul_eq_mul]
  ring

/-- Actual square-summability of the weighted coordinates; closure is proved. -/
def weightedSubmodule (w : ℤ → ℝ) : Submodule ℂ (ℤ → ℂ) where
  carrier := {x | Memℓp (weightedCoordinates w x) 2}
  zero_mem' := by
    change Memℓp (weightedCoordinates w (0 : ℤ → ℂ)) 2
    have h : weightedCoordinates w (0 : ℤ → ℂ) = 0 := by
      funext n
      simp only [weightedCoordinates, Pi.zero_apply, mul_zero]
    rw [h]
    exact zero_memℓp
  add_mem' := by
    intro x y hx hy
    change Memℓp (weightedCoordinates w (x + y)) 2
    rw [weightedCoordinates_add]
    exact hx.add hy
  smul_mem' := by
    intro c x hx
    change Memℓp (weightedCoordinates w (c • x)) 2
    rw [weightedCoordinates_smul]
    exact hx.const_smul c

/-- The carrier is a true subspace of integer complex sequences, not all sequences. -/
def WeightedHilbert (w : ℤ → ℝ) : Type := weightedSubmodule w

instance weightedHilbertCoeFun (w : ℤ → ℝ) : CoeFun (WeightedHilbert w) (fun _ => ℤ → ℂ) :=
  ⟨Subtype.val⟩

instance weightedHilbertAddCommGroup (w : ℤ → ℝ) : AddCommGroup (WeightedHilbert w) :=
  inferInstanceAs (AddCommGroup (weightedSubmodule w))

instance weightedHilbertModule (w : ℤ → ℝ) : Module ℂ (WeightedHilbert w) :=
  inferInstanceAs (Module ℂ (weightedSubmodule w))

/-- Actual square-root weighting into genuine l2. -/
def weightedLinearMap (w : ℤ → ℝ) :
    WeightedHilbert w →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun x := ⟨weightedCoordinates w (x : ℤ → ℂ), x.property⟩
  map_add' x y := by
    apply lp.ext
    exact weightedCoordinates_add w (x : ℤ → ℂ) (y : ℤ → ℂ)
  map_smul' c x := by
    apply lp.ext
    exact weightedCoordinates_smul w c (x : ℤ → ℂ)

theorem weightedLinearMap_apply (w : ℤ → ℝ) (x : WeightedHilbert w) (n : ℤ) :
    weightedLinearMap w x n = weightedCoordinates w (x : ℤ → ℂ) n := rfl

section PositiveWeights

variable (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]

theorem weightSqrt_ne_zero (n : ℤ) : (Real.sqrt (w n) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (hw.out n)).ne'

/-- Explicit inverse weighting, whose membership is proved by cancellation. -/
def weightedInverse (y : lp (fun _ : ℤ => ℂ) 2) : WeightedHilbert w := by
  refine ⟨fun n => y n / (Real.sqrt (w n) : ℂ), ?_⟩
  change Memℓp (weightedCoordinates w (fun n => y n / (Real.sqrt (w n) : ℂ))) 2
  have h : weightedCoordinates w (fun n => y n / (Real.sqrt (w n) : ℂ)) = y := by
    funext n
    dsimp [weightedCoordinates]
    field_simp [weightSqrt_ne_zero w n]
  rw [h]
  exact lp.memℓp y

/-- The derived bijection onto l2 uses division by the positive square-root weight. -/
def weightedLinearEquiv : WeightedHilbert w ≃ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  __ := weightedLinearMap w
  invFun := weightedInverse w
  left_inv x := by
    apply Subtype.ext
    funext n
    dsimp [weightedInverse, weightedLinearMap, weightedCoordinates]
    field_simp [weightSqrt_ne_zero w n]
  right_inv y := by
    apply lp.ext
    funext n
    dsimp [weightedInverse, weightedLinearMap, weightedCoordinates]
    field_simp [weightSqrt_ne_zero w n]

instance weightedHilbertNormedAddCommGroup : NormedAddCommGroup (WeightedHilbert w) :=
  NormedAddCommGroup.induced _ _ (weightedLinearMap w) (weightedLinearEquiv w).injective

instance weightedHilbertNormedSpace : NormedSpace ℂ (WeightedHilbert w) where
  norm_smul_le c x := by
    change ‖weightedLinearMap w (c • x)‖ ≤ ‖c‖ * ‖weightedLinearMap w x‖
    rw [map_smul]
    exact norm_smul_le c (weightedLinearMap w x)

instance weightedHilbertInnerProductSpace : InnerProductSpace ℂ (WeightedHilbert w) :=
  InnerProductSpace.induced (weightedLinearMap w)

/-- The Hilbert norm is the actual l2 norm of the weighted coordinates. -/
def weightedIsometry : WeightedHilbert w ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  __ := weightedLinearEquiv w
  norm_map' _ := rfl

instance weightedHilbertCompleteSpace : CompleteSpace (WeightedHilbert w) :=
  (weightedIsometry w).toIsometryEquiv.completeSpace

theorem weightedHilbert_hasSum (x : WeightedHilbert w) :
    HasSum (fun n : ℤ => w n * ‖(x : ℤ → ℂ) n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (weightedLinearMap w x)
  change HasSum (fun n : ℤ => ‖weightedCoordinates w (x : ℤ → ℂ) n‖ ^
    (2 : ℝ≥0∞).toReal) (‖x‖ ^ (2 : ℝ≥0∞).toReal) at h
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    weightedCoordinates_norm_sq w (fun n => (hw.out n).le) (x : ℤ → ℂ)] using h

theorem weightedHilbert_norm_sq (x : WeightedHilbert w) :
    ‖x‖ ^ 2 = ∑' n : ℤ, w n * ‖(x : ℤ → ℂ) n‖ ^ 2 :=
  (weightedHilbert_hasSum w x).tsum_eq.symm

end PositiveWeights

/-- Source E_s uses the same Hilbert carrier and norm with real scalars. -/
abbrev WeightedRealHilbert (w : ℤ → ℝ) : Type := RestrictScalars ℝ ℂ (WeightedHilbert w)

instance weightedRealHilbertInnerProductSpace (w : ℤ → ℝ)
    [Fact (∀ n : ℤ, 0 < w n)] : InnerProductSpace ℝ (WeightedRealHilbert w) := by
  letI : NormedSpace ℂ (WeightedRealHilbert w) :=
    Module.RestrictScalars.normedSpaceOrig
  letI : InnerProductSpace ℂ (WeightedRealHilbert w) :=
    inferInstanceAs (InnerProductSpace ℂ (WeightedHilbert w))
  exact InnerProductSpace.complexToReal


section Comparison

variable (w v : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]
  [hv : Fact (∀ n : ℤ, 0 < v n)]

def weightedComparison (C : ℝ) (hC : 0 ≤ C) (hcmp : ∀ n : ℤ, v n ≤ C * w n) :
    WeightedHilbert w →ₗ[ℂ] WeightedHilbert v where
  toFun x := ⟨(x : ℤ → ℂ), by
    change Memℓp (weightedCoordinates v (x : ℤ → ℂ)) 2
    apply (weightedCoordinates_mem_l2_iff v (fun n => (hv.out n).le) _).2
    have hs := (weightedHilbert_hasSum w x).summable.mul_left C
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hv.out n).le (sq_nonneg _))
      (fun n => ?_) hs
    calc
      v n * ‖(x : ℤ → ℂ) n‖ ^ 2 ≤ (C * w n) * ‖(x : ℤ → ℂ) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hcmp n) (sq_nonneg _)
      _ = C * (w n * ‖(x : ℤ → ℂ) n‖ ^ 2) := by ring⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

theorem weightedComparison_apply (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) (x : WeightedHilbert w) (n : ℤ) :
    (weightedComparison w v C hC hcmp x : ℤ → ℂ) n = (x : ℤ → ℂ) n := rfl

theorem weightedComparison_norm_sq_le (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) (x : WeightedHilbert w) :
    ‖weightedComparison w v C hC hcmp x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  rw [weightedHilbert_norm_sq v, weightedHilbert_norm_sq w]
  have hs := (weightedHilbert_hasSum w x).summable
  rw [← hs.tsum_mul_left C]
  apply Summable.tsum_le_tsum
    (fun n => ?_) (weightedHilbert_hasSum v (weightedComparison w v C hC hcmp x)).summable
    (hs.mul_left C)
  change v n * ‖(x : ℤ → ℂ) n‖ ^ 2 ≤ C * (w n * ‖(x : ℤ → ℂ) n‖ ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right (hcmp n) (sq_nonneg ‖(x : ℤ → ℂ) n‖)]

theorem weightedComparison_norm_le (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) (x : WeightedHilbert w) :
    ‖weightedComparison w v C hC hcmp x‖ ≤ Real.sqrt C * ‖x‖ := by
  have hsq := weightedComparison_norm_sq_le w v C hC hcmp x
  have hs : (Real.sqrt C * ‖x‖) ^ 2 = C * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  have hpos : 0 ≤ Real.sqrt C * ‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (weightedComparison w v C hC hcmp x)]

def weightedComparisonContinuous (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) : WeightedHilbert w →L[ℂ] WeightedHilbert v :=
  (weightedComparison w v C hC hcmp).mkContinuous (Real.sqrt C)
    (weightedComparison_norm_le w v C hC hcmp)

end Comparison

section Projection

open Filter
open scoped Topology

variable (w : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < w n)]

theorem weightedIsometry_apply (x : WeightedHilbert w) (n : ℤ) :
    weightedIsometry w x n = weightedCoordinates w (x : ℤ → ℂ) n := rfl

theorem weightedIsometry_symm_apply (y : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    ((weightedIsometry w).symm y : ℤ → ℂ) n = y n / (Real.sqrt (w n) : ℂ) := rfl

def weightedProjection (s : Finset ℤ) (x : WeightedHilbert w) : WeightedHilbert w :=
  (weightedIsometry w).symm (∑ n ∈ s, lp.single 2 n (weightedIsometry w x n))

theorem weightedProjection_apply (s : Finset ℤ) (x : WeightedHilbert w) (n : ℤ) :
    (weightedProjection w s x : ℤ → ℂ) n = if n ∈ s then (x : ℤ → ℂ) n else 0 := by
  classical
  simp only [weightedProjection, weightedIsometry_symm_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single,
    weightedIsometry_apply, weightedCoordinates]
  split_ifs
  · field_simp [weightSqrt_ne_zero w n]
  · simp

def symmetricModes (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem symmetricModes_tendsto : Tendsto symmetricModes atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro N M hNM n hn
    simp only [symmetricModes, Finset.mem_Icc] at hn ⊢
    omega
  · intro n
    refine ⟨n.natAbs, ?_⟩
    simp only [symmetricModes, Finset.mem_Icc]
    omega

theorem weightedProjection_tendsto (x : WeightedHilbert w) :
    Tendsto (fun N : ℕ => weightedProjection w (symmetricModes N) x) atTop (𝓝 x) := by
  have hs := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (weightedIsometry w x)
  have ht := hs.comp symmetricModes_tendsto
  have h := ((weightedIsometry w).symm.continuous.tendsto (weightedIsometry w x)).comp ht
  simpa only [weightedProjection, Function.comp_def,
    LinearIsometryEquiv.symm_apply_apply] using h

end Projection

end NlsGge.Pilot
