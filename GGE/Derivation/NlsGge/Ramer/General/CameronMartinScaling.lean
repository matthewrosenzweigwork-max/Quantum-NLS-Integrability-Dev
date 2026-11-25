import NlsGge.Measure.ComplexGaussian
import NlsGge.Measure.CountableGaussian
import NlsGge.Ramer.ConstantShiftInverseOrientation
import NlsGge.Measure.ActualSourceCMFiniteScoreL2CauchyContractV1

/-!
# Cameron–Martin theorem for arbitrary positive rates, by diagonal scaling

Sequence space `ℤ → ℂ` only. For rates `q q' : ℤ → ℝ` with `0 < q, q'` put
`λ n = √(q n / q' n)`. The diagonal map `scaleSeq λ` carries
`countableComplexGaussian q` to `countableComplexGaussian q'`, and is an isometry
between the Cameron–Martin spaces with norms `2 Σ q |h|²` and `2 Σ q' |h|²`.
Transport from the reference rate `sourceRate c₀` gives the inverse-orientation
Cameron–Martin density for every positive rate. Conventions unchanged: real-component
variance `1/(2a)`, CM norm `2 Σ q |h|²`, negative score for `z ↦ z - h`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal BigOperators

namespace NlsGge.Ramer.General

open NlsGge.Measure NlsGge.Pilot

/-! ### Goal 1: one-dimensional scaling -/

theorem componentVariance_div_sq (a l : ℝ) (ha : 0 < a) (hl : l ≠ 0) :
    componentVariance (a / l ^ 2) = NNReal.mk (l ^ 2) (sq_nonneg _) * componentVariance a := by
  have hl2 : 0 < l ^ 2 := by positivity
  apply NNReal.eq
  rw [componentVariance_coe _ (div_pos ha hl2), NNReal.coe_mul, componentVariance_coe a ha]
  simp only [NNReal.coe_mk]
  field_simp

theorem map_real_smul_complexGaussian (a : ℝ) (ha : 0 < a) (l : ℝ) (hl : l ≠ 0) :
    (complexGaussian a).map (fun z : ℂ => (l : ℂ) * z) = complexGaussian (a / l ^ 2) := by
  have hm : Measurable (fun x : ℝ => l * x) := by fun_prop
  have hmc : Measurable (fun z : ℂ => (l : ℂ) * z) := by fun_prop
  unfold complexGaussian
  rw [Measure.map_map hmc Complex.measurableEquivRealProd.symm.measurable]
  have hcomp : ((fun z : ℂ => (l : ℂ) * z) ∘ Complex.measurableEquivRealProd.symm) =
      Complex.measurableEquivRealProd.symm ∘ Prod.map (fun x : ℝ => l * x) (fun x : ℝ => l * x) := by
    funext p
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
  rw [hcomp, ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable (hm.prodMap hm),
    ← Measure.map_prod_map _ _ hm hm, gaussianReal_map_const_mul, mul_zero,
    ← componentVariance_div_sq a l ha hl]

/-! ### The scaling equivalence on sequence space -/

/-- Diagonal real scaling of sequences. -/
def scaleSeq (l : ℤ → ℝ) (z : ℤ → ℂ) : ℤ → ℂ := fun n => (l n : ℂ) * z n

theorem measurable_scaleSeq (l : ℤ → ℝ) : Measurable (scaleSeq l) := by
  unfold scaleSeq; fun_prop

/-- The scaling as a measurable equivalence (for nonvanishing `l`). -/
def scaleEquiv (l : ℤ → ℝ) (hl : ∀ n, l n ≠ 0) : (ℤ → ℂ) ≃ᵐ (ℤ → ℂ) where
  toFun := scaleSeq l
  invFun := fun z n => ((l n)⁻¹ : ℝ) * z n
  left_inv z := by
    funext n
    have : (l n : ℂ) ≠ 0 := by exact_mod_cast hl n
    simp [scaleSeq]
    field_simp
  right_inv z := by
    funext n
    have : (l n : ℂ) ≠ 0 := by exact_mod_cast hl n
    simp [scaleSeq]
    field_simp
  measurable_toFun := measurable_scaleSeq l
  measurable_invFun := by
    refine Measurable.of_eval (fun n => ?_)
    exact (measurable_const.mul (measurable_pi_apply n))

theorem scaleEquiv_apply (l : ℤ → ℝ) (hl : ∀ n, l n ≠ 0) (z : ℤ → ℂ) :
    scaleEquiv l hl z = scaleSeq l z := rfl

/-! ### Goal 2: product scaling -/

theorem map_scaleSeq_countableComplexGaussian (q q' l : ℤ → ℝ) (hq : ∀ n, 0 < q n)
    (hl : ∀ n, l n ≠ 0) (hqq : ∀ n, q' n = q n / l n ^ 2) :
    (countableComplexGaussian q).map (scaleSeq l) = countableComplexGaussian q' := by
  unfold countableComplexGaussian
  have h := Measure.infinitePi_map_pi (μ := fun n : ℤ => complexGaussian (q n))
    (f := fun n (z : ℂ) => (l n : ℂ) * z) (fun n => by fun_prop)
  change (Measure.infinitePi fun n : ℤ => complexGaussian (q n)).map
    (fun z n => (l n : ℂ) * z n) = _ at h
  unfold scaleSeq
  rw [h]
  congr 1
  funext n
  rw [map_real_smul_complexGaussian _ (hq n) _ (hl n), hqq n]


/-! ### Goal 3: the H-isometry of the scaling -/

/-- Fourier coordinates of a vector of `WeightedRealHilbert w`. -/
def wCoord {w : ℤ → ℝ} (x : WeightedRealHilbert w) (n : ℤ) : ℂ :=
  (show WeightedHilbert w from x) n

theorem wCoord_add {w : ℤ → ℝ} (x y : WeightedRealHilbert w) (n : ℤ) :
    wCoord (x + y) n = wCoord x n + wCoord y n := rfl

theorem wCoord_smul {w : ℤ → ℝ} (r : ℝ) (x : WeightedRealHilbert w) (n : ℤ) :
    wCoord (r • x) n = (r : ℂ) * wCoord x n := rfl

theorem wCoord_ext {w : ℤ → ℝ} {x y : WeightedRealHilbert w}
    (h : ∀ n, wCoord x n = wCoord y n) : x = y := by
  change (show WeightedHilbert w from x) = (show WeightedHilbert w from y)
  exact Subtype.ext (funext h)

theorem wCoord_norm_sq {w : ℤ → ℝ} [Fact (∀ n, 0 < w n)] (x : WeightedRealHilbert w) :
    ‖x‖ ^ 2 = ∑' n : ℤ, w n * ‖wCoord x n‖ ^ 2 :=
  weightedHilbert_norm_sq w x

theorem wCoord_summable {w : ℤ → ℝ} [Fact (∀ n, 0 < w n)] (x : WeightedRealHilbert w) :
    Summable (fun n : ℤ => w n * ‖wCoord x n‖ ^ 2) :=
  (weightedHilbert_hasSum w x).summable

section Scale

variable {w w' : ℤ → ℝ} [Fact (∀ n, 0 < w n)] [Fact (∀ n, 0 < w' n)] (l : ℤ → ℝ)

/-- Coordinatewise scaling of an element, as a vector of the target space. -/
def scaleHElem (hww : ∀ n, w n = w' n * l n ^ 2) (x : WeightedRealHilbert w) :
    WeightedRealHilbert w' :=
  show WeightedHilbert w' from
    (⟨fun n => (l n : ℂ) * wCoord x n, by
      change Memℓp (weightedCoordinates w' _) 2
      rw [weightedCoordinates_mem_l2_iff w' (fun n => (Fact.out : ∀ n, 0 < w' n) n |>.le)]
      refine (wCoord_summable x).congr (fun n => ?_)
      rw [hww n, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring⟩ : weightedSubmodule w')

theorem wCoord_scaleHElem (hww : ∀ n, w n = w' n * l n ^ 2) (x : WeightedRealHilbert w)
    (n : ℤ) : wCoord (scaleHElem l hww x) n = (l n : ℂ) * wCoord x n := rfl


theorem scaleHElem_add (hww : ∀ n, w n = w' n * l n ^ 2) (x y : WeightedRealHilbert w) :
    scaleHElem l hww (x + y) = scaleHElem l hww x + scaleHElem l hww y := by
  apply wCoord_ext; intro n
  rw [wCoord_scaleHElem, wCoord_add, wCoord_add, wCoord_scaleHElem, wCoord_scaleHElem, mul_add]

theorem scaleHElem_smul (hww : ∀ n, w n = w' n * l n ^ 2) (r : ℝ) (x : WeightedRealHilbert w) :
    scaleHElem l hww (r • x) = r • scaleHElem l hww x := by
  apply wCoord_ext; intro n
  rw [wCoord_scaleHElem, wCoord_smul, wCoord_smul, wCoord_scaleHElem]; ring

theorem scaleHElem_norm (hww : ∀ n, w n = w' n * l n ^ 2) (x : WeightedRealHilbert w) :
    ‖scaleHElem l hww x‖ = ‖x‖ := by
  have h : ‖scaleHElem l hww x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [wCoord_norm_sq, wCoord_norm_sq]
    refine tsum_congr (fun n => ?_)
    rw [wCoord_scaleHElem, hww n, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem scaleHElem_inv_left (hl : ∀ n, l n ≠ 0) (hww : ∀ n, w n = w' n * l n ^ 2)
    (hww' : ∀ n, w' n = w n * (l n)⁻¹ ^ 2) (x : WeightedRealHilbert w) :
    scaleHElem (fun n => (l n)⁻¹) hww' (scaleHElem l hww x) = x := by
  apply wCoord_ext; intro n
  have : (l n : ℂ) ≠ 0 := by exact_mod_cast hl n
  rw [wCoord_scaleHElem, wCoord_scaleHElem]
  push_cast
  field_simp

theorem scaleHElem_inv_right (hl : ∀ n, l n ≠ 0) (hww : ∀ n, w n = w' n * l n ^ 2)
    (hww' : ∀ n, w' n = w n * (l n)⁻¹ ^ 2) (y : WeightedRealHilbert w') :
    scaleHElem l hww (scaleHElem (fun n => (l n)⁻¹) hww' y) = y := by
  apply wCoord_ext; intro n
  have : (l n : ℂ) ≠ 0 := by exact_mod_cast hl n
  rw [wCoord_scaleHElem, wCoord_scaleHElem]
  push_cast
  field_simp

/-- The coordinate scaling as a real linear isometry equivalence. -/
def scaleHEquiv (hl : ∀ n, l n ≠ 0) (hww : ∀ n, w n = w' n * l n ^ 2) :
    WeightedRealHilbert w ≃ₗᵢ[ℝ] WeightedRealHilbert w' :=
  have hww' : ∀ n, w' n = w n * (l n)⁻¹ ^ 2 := fun n => by
    rw [hww n]; have := hl n; field_simp
  { toFun := scaleHElem l hww
    invFun := scaleHElem (fun n => (l n)⁻¹) hww'
    map_add' := scaleHElem_add l hww
    map_smul' := fun r x => scaleHElem_smul l hww r x
    left_inv := scaleHElem_inv_left l hl hww hww'
    right_inv := scaleHElem_inv_right l hl hww hww'
    norm_map' := scaleHElem_norm l hww }

theorem scaleHEquiv_coord (hl : ∀ n, l n ≠ 0) (hww : ∀ n, w n = w' n * l n ^ 2)
    (x : WeightedRealHilbert w) (n : ℤ) :
    wCoord (scaleHEquiv l hl hww x) n = (l n : ℂ) * wCoord x n := rfl

end Scale

/-- The scaling `WeightedRealHilbert (2q) ≃ₗᵢ[ℝ] WeightedRealHilbert (2q')` for `q = q' λ²`. -/
def scaleH (q q' l : ℤ → ℝ) [Fact (∀ n, 0 < 2 * q n)] [Fact (∀ n, 0 < 2 * q' n)]
    (hl : ∀ n, l n ≠ 0) (hqq : ∀ n, q n = q' n * l n ^ 2) :
    WeightedRealHilbert (fun n => 2 * q n) ≃ₗᵢ[ℝ] WeightedRealHilbert (fun n => 2 * q' n) :=
  scaleHEquiv l hl (fun n => by rw [hqq n]; ring)

theorem scaleH_coord (q q' l : ℤ → ℝ) [Fact (∀ n, 0 < 2 * q n)] [Fact (∀ n, 0 < 2 * q' n)]
    (hl : ∀ n, l n ≠ 0) (hqq : ∀ n, q n = q' n * l n ^ 2)
    (h : WeightedRealHilbert (fun n => 2 * q n)) (n : ℤ) :
    wCoord (scaleH q q' l hl hqq h) n = (l n : ℂ) * wCoord h n := rfl

/-! ### Goal 4: score invariance -/

/-- Generic finite Cameron–Martin score
`2 Σ_{n ∈ symmetricModes N} q n · Re(conj (h n) · z n)`. -/
def cmScore (q : ℤ → ℝ) (h : ℤ → ℂ) (N : ℕ) (z : ℤ → ℂ) : ℝ :=
  2 * ∑ n ∈ symmetricModes N, q n * (starRingEnd ℂ (h n) * z n).re

theorem cmScore_scale (q q' l : ℤ → ℝ) (hqq : ∀ n, q n = q' n * l n ^ 2)
    (h : ℤ → ℂ) (N : ℕ) (z : ℤ → ℂ) :
    cmScore q' (fun n => (l n : ℂ) * h n) N (scaleSeq l z) = cmScore q h N z := by
  unfold cmScore scaleSeq
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [hqq n]
  have : (starRingEnd ℂ (↑(l n) * h n) * (↑(l n) * z n)) =
      ((l n ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (h n) * z n) := by
    simp [map_mul, Complex.conj_ofReal]; ring
  rw [this, Complex.re_ofReal_mul]; ring


/-! ### The existing score is the generic score -/

theorem weightedLinearMap_partial_apply {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (N : ℕ) (z : ℤ → ℂ) (i : ℤ) :
    weightedLinearMap (fullModeWeight c 0)
        (show WeightedHilbert (fullModeWeight c 0) from fullWeightedSequencePartial c 0 N z) i =
      if i ∈ symmetricModes N then weightedCoordinates (fullModeWeight c 0) z i else 0 := by
  classical
  have h := (weightedIsometry (fullModeWeight c 0)).apply_symm_apply
    (∑ n ∈ symmetricModes N,
      lp.single 2 n (weightedCoordinates (fullModeWeight c 0) z n))
  have h2 := congrArg (fun y : lp (fun _ : ℤ => ℂ) 2 => y i) h
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single] at h2
  exact h2

theorem actualSourceCMFiniteScorePartial_eq_sum {lower upper : ℝ}
    (c : BoundedCoefficients lower upper)
    (x : WeightedRealHilbert (cmModeWeight c)) (N : ℕ) (z : ℤ → ℂ) :
    actualSourceCMFiniteScorePartial c x N z =
      2 * ∑ n ∈ symmetricModes N, sourceRate c n *
        (starRingEnd ℂ (actualSourceCMSequence c x n) * z n).re := by
  classical
  unfold actualSourceCMFiniteScorePartial actualSourceCMFiniteScoreFunctional
  change (2 : ℝ) * (inner ℝ (cmToFullWeightedHilbert c 0 (by norm_num) x)
      (fullWeightedSequencePartial c 0 N z)) = _
  change (2 : ℝ) * (inner ℂ
      (show WeightedHilbert (fullModeWeight c 0) from cmToFullWeightedHilbert c 0 (by norm_num) x)
      (show WeightedHilbert (fullModeWeight c 0) from fullWeightedSequencePartial c 0 N z)).re = _
  rw [show inner ℂ
      (show WeightedHilbert (fullModeWeight c 0) from cmToFullWeightedHilbert c 0 (by norm_num) x)
      (show WeightedHilbert (fullModeWeight c 0) from fullWeightedSequencePartial c 0 N z) =
      inner ℂ (weightedLinearMap (fullModeWeight c 0)
        (show WeightedHilbert (fullModeWeight c 0) from cmToFullWeightedHilbert c 0 (by norm_num) x))
        (weightedLinearMap (fullModeWeight c 0)
        (show WeightedHilbert (fullModeWeight c 0) from fullWeightedSequencePartial c 0 N z))
    from rfl, lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := symmetricModes N)]
  · rw [Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [weightedLinearMap_partial_apply, if_pos hn]
    have hs : (Real.sqrt (fullModeWeight c 0 n)) ^ 2 = sourceRate c n := by
      rw [Real.sq_sqrt (fullModeWeight_pos c 0 n).le]
      simp [fullModeWeight]
    change (inner ℂ ((Real.sqrt (fullModeWeight c 0 n) : ℂ) * actualSourceCMSequence c x n)
      (weightedCoordinates (fullModeWeight c 0) z n)).re = _
    simp only [weightedCoordinates, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    have : (starRingEnd ℂ) (actualSourceCMSequence c x n) * z n *
        ((Real.sqrt (fullModeWeight c 0 n) : ℂ) * (Real.sqrt (fullModeWeight c 0 n) : ℂ)) =
        ((sourceRate c n : ℝ) : ℂ) * ((starRingEnd ℂ) (actualSourceCMSequence c x n) * z n) := by
      rw [← Complex.ofReal_mul, ← sq, hs]; ring
    rw [show (↑(Real.sqrt (fullModeWeight c 0 n)) * z n *
        (↑(Real.sqrt (fullModeWeight c 0 n)) * (starRingEnd ℂ) (actualSourceCMSequence c x n))) =
        (starRingEnd ℂ) (actualSourceCMSequence c x n) * z n *
        ((Real.sqrt (fullModeWeight c 0 n) : ℂ) * (Real.sqrt (fullModeWeight c 0 n) : ℂ)) by ring,
      this, Complex.re_ofReal_mul]
  · intro n hn
    rw [weightedLinearMap_partial_apply, if_neg hn]
    simp


/-! ### Generic score as an `L²` class -/

theorem memLp_two_coord (q : ℤ → ℝ) (n : ℤ) :
    MemLp (fun z : ℤ → ℂ => z n) 2 (countableComplexGaussian q) :=
  (memLp_two_iff_integrable_sq_norm (measurable_pi_apply n).aestronglyMeasurable).2
    (integrable_countableComplexGaussian_sqNorm q n)

theorem memLp_cmScore (q : ℤ → ℝ) (h : ℤ → ℂ) (N : ℕ) :
    MemLp (cmScore q h N) 2 (countableComplexGaussian q) := by
  unfold cmScore
  refine MemLp.const_mul ?_ 2
  have : (fun z : ℤ → ℂ => ∑ n ∈ symmetricModes N, q n * (starRingEnd ℂ (h n) * z n).re) =
      ∑ n ∈ symmetricModes N, (fun z : ℤ → ℂ => q n * (starRingEnd ℂ (h n) * z n).re) := by
    funext z; simp
  rw [this]
  exact memLp_finset_sum' _ (fun n _ =>
    (((memLp_two_coord q n).const_mul (starRingEnd ℂ (h n))).re).const_mul (q n))

/-- The finite score `cmScore q h N` as an element of `L²(countableComplexGaussian q)`. -/
def cmScoreLp (q : ℤ → ℝ) (h : ℤ → ℂ) (N : ℕ) : Lp ℝ 2 (countableComplexGaussian q) :=
  (memLp_cmScore q h N).toLp (cmScore q h N)

theorem cmScoreLp_ae (q : ℤ → ℝ) (h : ℤ → ℂ) (N : ℕ) :
    (cmScoreLp q h N : (ℤ → ℂ) → ℝ) =ᵐ[countableComplexGaussian q] cmScore q h N :=
  MemLp.coeFn_toLp _

theorem cmScore_neg (q : ℤ → ℝ) (h : ℤ → ℂ) (N : ℕ) (z : ℤ → ℂ) :
    cmScore q (fun n => -h n) N z = -cmScore q h N z := by
  unfold cmScore
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp [neg_mul]
  ring

theorem cmScoreLp_neg (q : ℤ → ℝ) (h : ℤ → ℂ) (N : ℕ) :
    cmScoreLp q (fun n => -h n) N = -cmScoreLp q h N := by
  apply Lp.ext
  filter_upwards [cmScoreLp_ae q (fun n => -h n) N, cmScoreLp_ae q h N,
    Lp.coeFn_neg (cmScoreLp q h N)] with z h1 h2 h3
  rw [h1, h3, Pi.neg_apply, h2]
  exact cmScore_neg q h N z


/-! ### Goal 5: the Cameron–Martin theorem for arbitrary rates -/

/-- Pushing a density measure forward by a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (T : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map T = (μ.map T).withDensity (fun b => f (T.symm b)) := by
  ext s hs
  rw [Measure.map_apply T.measurable hs, withDensity_apply _ (T.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map T.measurable hs,
    lintegral_map_equiv]
  simp

/-- Transport of a shift formula through a measurable equivalence. -/
theorem shift_density_transport {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (T : α ≃ᵐ α) (hT : μ.map T = ν) (σ τ : α → α) (hσ : Measurable σ)
    (hστ : ∀ z, T (σ z) = τ (T z)) (hτ : Measurable τ) (F₀ F : α → ℝ≥0∞)
    (hmap : ν.map τ = ν.withDensity F₀) (hF : F =ᵐ[μ] fun z => F₀ (T z)) :
    μ.map σ = μ.withDensity F := by
  have h1 : (μ.map σ).map T = (μ.withDensity F).map T := by
    rw [Measure.map_map T.measurable hσ, withDensity_congr_ae hF, map_withDensity_equiv]
    have : (T ∘ σ) = τ ∘ T := funext hστ
    rw [this, ← Measure.map_map hτ T.measurable, hT, hmap]
    simp
  have h2 := congrArg (fun m => m.map T.symm) h1
  rw [Measure.map_map T.symm.measurable T.measurable,
    Measure.map_map T.symm.measurable T.measurable] at h2
  have e : (T.symm ∘ T) = id := funext T.symm_apply_apply
  rw [e, Measure.map_id, Measure.map_id] at h2
  exact h2


/-- The reference coefficients `c₀ ≡ 1`. -/
def refCoeff : BoundedCoefficients 1 1 := boundedCoefficients_const 1 1 one_pos le_rfl

theorem fullWeightSequenceGaussian_eq_sourceRate {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) :
    fullWeightSequenceGaussian c.val = countableComplexGaussian (sourceRate c) := rfl

/-- Scaling factors `λ n = √(q n / q' n)`. -/
def scaleFactor (q q' : ℤ → ℝ) (n : ℤ) : ℝ := Real.sqrt (q n / q' n)

theorem scaleFactor_pos (q q' : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hq' : ∀ n, 0 < q' n) (n : ℤ) :
    0 < scaleFactor q q' n :=
  Real.sqrt_pos.2 (div_pos (hq n) (hq' n))

theorem scaleFactor_rel (q q' : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hq' : ∀ n, 0 < q' n) (n : ℤ) :
    q n = q' n * scaleFactor q q' n ^ 2 := by
  unfold scaleFactor
  rw [Real.sq_sqrt (div_pos (hq n) (hq' n)).le]
  have := (hq' n).ne'
  field_simp

theorem scaleFactor_rel' (q q' : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hq' : ∀ n, 0 < q' n) (n : ℤ) :
    q' n = q n / scaleFactor q q' n ^ 2 := by
  have h := scaleFactor_rel q q' hq hq' n
  have := (scaleFactor_pos q q' hq hq' n).ne'
  field_simp
  linarith

theorem measurePreserving_scaleSeq (q q' : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hq' : ∀ n, 0 < q' n) :
    MeasurePreserving (scaleSeq (scaleFactor q q'))
      (countableComplexGaussian q) (countableComplexGaussian q') :=
  ⟨measurable_scaleSeq _, map_scaleSeq_countableComplexGaussian q q' _ hq
    (fun n => (scaleFactor_pos q q' hq hq' n).ne') (scaleFactor_rel' q q' hq hq')⟩

/-- **Cameron–Martin theorem for an arbitrary positive rate, inverse orientation.** -/
theorem exists_cm_inverseShift_negativeScoreDensity (q : ℤ → ℝ) (hq : ∀ n, 0 < q n)
    (h : WeightedRealHilbert (fun n => 2 * q n)) :
    ∃ S : Lp ℝ 2 (countableComplexGaussian q),
      Tendsto (fun N : ℕ => cmScoreLp q (wCoord h) N) atTop (𝓝 S) ∧
      AEMeasurable (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-S z -
        (∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2) / 2))) (countableComplexGaussian q) ∧
      (∫⁻ z : ℤ → ℂ, ENNReal.ofReal (Real.exp (-S z -
        (∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2) / 2)) ∂countableComplexGaussian q) = 1 ∧
      (countableComplexGaussian q).map (fun z : ℤ → ℂ => fun n => z n - wCoord h n) =
        (countableComplexGaussian q).withDensity (fun z => ENNReal.ofReal (Real.exp (-S z -
          (∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2) / 2))) := by
  have hq₀ : ∀ n, 0 < sourceRate refCoeff n := sourceRate_pos refCoeff
  have hl : ∀ n, scaleFactor q (sourceRate refCoeff) n ≠ 0 :=
    fun n => (scaleFactor_pos q _ hq hq₀ n).ne'
  have hqq := scaleFactor_rel q (sourceRate refCoeff) hq hq₀
  have : Fact (∀ n, 0 < 2 * q n) := ⟨fun n => by have := hq n; positivity⟩
  set l := scaleFactor q (sourceRate refCoeff) with hldef
  set g : WeightedRealHilbert (cmModeWeight refCoeff) :=
    scaleH q (sourceRate refCoeff) l hl hqq h with hg
  obtain ⟨S₀, hS₀, hm₀, hmass₀, hmap₀⟩ :=
    exists_actualSourceCM_inverseShift_negativeScoreDensity refCoeff g
  set γ := countableComplexGaussian q with hγ
  let T : (ℤ → ℂ) ≃ᵐ (ℤ → ℂ) := scaleEquiv l hl
  have hT : MeasurePreserving T γ (fullWeightSequenceGaussian refCoeff.val) := measurePreserving_scaleSeq q _ hq hq₀
  have hgc : ∀ n, actualSourceCMSequence refCoeff g n = (l n : ℂ) * wCoord h n := fun n => rfl
  have hQ : (∑' n : ℤ, cmModeWeight refCoeff n * ‖actualSourceCMSequence refCoeff g n‖ ^ 2) =
      ∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2 := by
    refine tsum_congr (fun n => ?_)
    rw [hgc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hqq n]
    simp only [cmModeWeight]
    ring
  rw [hQ] at hm₀ hmass₀ hmap₀
  set Q := ∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2 with hQdef
  have hscore : ∀ (N : ℕ) (z : ℤ → ℂ),
      actualSourceCMFiniteScorePartial refCoeff g N (T z) = cmScore q (wCoord h) N z := by
    intro N z
    rw [actualSourceCMFiniteScorePartial_eq_sum]
    have := cmScore_scale q (sourceRate refCoeff) l hqq (wCoord h) N z
    rw [← this]
    rfl
  let Sq : Lp ℝ 2 γ := Lp.compMeasurePreserving T hT S₀
  have hSq : (Sq : (ℤ → ℂ) → ℝ) =ᵐ[γ] fun z => S₀ (T z) :=
    Lp.coeFn_compMeasurePreserving S₀ hT
  have hLp : ∀ N : ℕ, cmScoreLp q (wCoord h) N =
      Lp.compMeasurePreserving T hT (actualSourceCMFiniteScorePartialLp refCoeff g N) := by
    intro N
    apply Lp.ext
    have e0 : (actualSourceCMFiniteScorePartialLp refCoeff g N : (ℤ → ℂ) → ℝ) =ᵐ[(fullWeightSequenceGaussian refCoeff.val)]
        actualSourceCMFiniteScorePartial refCoeff g N := by
      unfold actualSourceCMFiniteScorePartialLp
      exact MemLp.coeFn_toLp _
    filter_upwards [cmScoreLp_ae q (wCoord h) N,
      Lp.coeFn_compMeasurePreserving (actualSourceCMFiniteScorePartialLp refCoeff g N) hT,
      hT.quasiMeasurePreserving.ae_eq_comp e0] with z h1 h2 h3
    rw [h1, h2]
    exact (hscore N z).symm.trans (h3.symm)
  have hF : (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-Sq z - Q / 2))) =ᵐ[γ]
      fun z => (fun w : ℤ → ℂ => ENNReal.ofReal (Real.exp (-S₀ w - Q / 2))) (T z) := by
    have h1 : (Sq : (ℤ → ℂ) → ℝ) =ᵐ[γ] fun z => S₀ (T z) := hSq
    filter_upwards [h1] with z hz
    simp only [hz]
  refine ⟨Sq, ?_, ?_, ?_, ?_⟩
  · simp only [hLp]
    exact ((Lp.isometry_compMeasurePreserving (p := 2) hT).continuous.tendsto _).comp hS₀
  · exact (hm₀.comp_quasiMeasurePreserving hT.quasiMeasurePreserving).congr hF.symm
  · rw [lintegral_congr_ae hF]
    exact (hT.lintegral_comp_emb T.measurableEmbedding _).trans hmass₀
  · refine shift_density_transport γ (fullWeightSequenceGaussian refCoeff.val) T hT.map_eq _ _ ?_ ?_ ?_ _ _ hmap₀ hF
    · exact Measurable.of_eval (fun n => (measurable_pi_apply n).sub measurable_const)
    · intro z
      funext n
      show (l n : ℂ) * (z n - wCoord h n) = (l n : ℂ) * z n - actualSourceCMSequence refCoeff g n
      rw [hgc, mul_sub]
    · exact Measurable.of_eval (fun n => (measurable_pi_apply n).sub measurable_const)


/-- **Cameron–Martin theorem for an arbitrary positive rate, `+h` orientation** (positive score):
`(z ↦ z + h)_# γ_q = exp(S - ‖h‖²/2) γ_q`. -/
theorem exists_cm_shift_positiveScoreDensity (q : ℤ → ℝ) (hq : ∀ n, 0 < q n)
    (h : WeightedRealHilbert (fun n => 2 * q n)) :
    ∃ S : Lp ℝ 2 (countableComplexGaussian q),
      Tendsto (fun N : ℕ => cmScoreLp q (wCoord h) N) atTop (𝓝 S) ∧
      AEMeasurable (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (S z -
        (∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2) / 2))) (countableComplexGaussian q) ∧
      (∫⁻ z : ℤ → ℂ, ENNReal.ofReal (Real.exp (S z -
        (∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2) / 2)) ∂countableComplexGaussian q) = 1 ∧
      (countableComplexGaussian q).map (fun z : ℤ → ℂ => fun n => z n + wCoord h n) =
        (countableComplexGaussian q).withDensity (fun z => ENNReal.ofReal (Real.exp (S z -
          (∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2) / 2))) := by
  have haveFact : Fact (∀ n, 0 < 2 * q n) := ⟨fun n => by have := hq n; positivity⟩
  obtain ⟨S', hS', hm', hmass', hmap'⟩ :=
    exists_cm_inverseShift_negativeScoreDensity q hq (-h)
  have hw : ∀ n, wCoord (-h) n = -wCoord h n := fun n => rfl
  have hwf : wCoord (-h) = fun n => -wCoord h n := funext hw
  have hQ : (∑' n : ℤ, 2 * q n * ‖wCoord (-h) n‖ ^ 2) =
      ∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2 := by
    refine tsum_congr (fun n => ?_)
    rw [hw, norm_neg]
  rw [hQ] at hm' hmass' hmap'
  rw [hwf] at hS'
  set Q := ∑' n : ℤ, 2 * q n * ‖wCoord h n‖ ^ 2 with hQdef
  have hae : (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-S' z - Q / 2))) =ᵐ[
      countableComplexGaussian q]
      (fun z => ENNReal.ofReal (Real.exp ((-S' : Lp ℝ 2 _) z - Q / 2))) := by
    filter_upwards [Lp.coeFn_neg S'] with z hz
    rw [hz, Pi.neg_apply]
  refine ⟨-S', ?_, ?_, ?_, ?_⟩
  · have h1 := hS'.neg
    simp only [cmScoreLp_neg, neg_neg] at h1
    exact h1
  · exact hm'.congr hae
  · rw [← lintegral_congr_ae hae]; exact hmass'
  · have hfun : (fun z : ℤ → ℂ => fun n => z n + wCoord h n) =
        (fun z : ℤ → ℂ => fun n => z n - wCoord (-h) n) := by
      funext z n; rw [hw]; ring
    rw [hfun, hmap']
    exact withDensity_congr_ae hae

/-! ### Goal 6: quasi-invariance on sequence space -/

theorem quasiMeasurePreserving_add_wCoord (q : ℤ → ℝ) (hq : ∀ n, 0 < q n)
    (h : WeightedRealHilbert (fun n => 2 * q n)) :
    Measure.QuasiMeasurePreserving (fun z : ℤ → ℂ => fun n => z n + wCoord h n)
      (countableComplexGaussian q) (countableComplexGaussian q) := by
  obtain ⟨S, -, -, -, hmap⟩ := exists_cm_shift_positiveScoreDensity q hq h
  refine ⟨Measurable.of_eval (fun n => (measurable_pi_apply n).add measurable_const), ?_⟩
  rw [hmap]
  exact withDensity_absolutelyContinuous _ _

theorem quasiMeasurePreserving_sub_wCoord (q : ℤ → ℝ) (hq : ∀ n, 0 < q n)
    (h : WeightedRealHilbert (fun n => 2 * q n)) :
    Measure.QuasiMeasurePreserving (fun z : ℤ → ℂ => fun n => z n - wCoord h n)
      (countableComplexGaussian q) (countableComplexGaussian q) := by
  obtain ⟨S, -, -, -, hmap⟩ := exists_cm_inverseShift_negativeScoreDensity q hq h
  refine ⟨Measurable.of_eval (fun n => (measurable_pi_apply n).sub measurable_const), ?_⟩
  rw [hmap]
  exact withDensity_absolutelyContinuous _ _

/-! ### Regression probe for `q = sourceRate c` -/

/-- For `q = sourceRate c` the generic score is the existing finite CM score, pointwise. -/
theorem cmScore_sourceRate_eq {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (x : WeightedRealHilbert (cmModeWeight c)) (N : ℕ) :
    cmScore (sourceRate c) (wCoord x) N = actualSourceCMFiniteScorePartial c x N := by
  funext z
  rw [actualSourceCMFiniteScorePartial_eq_sum]
  rfl

/-- The `L²` classes agree, over `fullWeightSequenceGaussian c.val = countableComplexGaussian
(sourceRate c)`. -/
theorem cmScoreLp_sourceRate_eq {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (x : WeightedRealHilbert (cmModeWeight c)) (N : ℕ) :
    cmScoreLp (sourceRate c) (wCoord x) N = actualSourceCMFiniteScorePartialLp c x N := by
  apply Lp.ext
  have e0 : (actualSourceCMFiniteScorePartialLp c x N : (ℤ → ℂ) → ℝ) =ᵐ[
      fullWeightSequenceGaussian c.val] actualSourceCMFiniteScorePartial c x N := by
    unfold actualSourceCMFiniteScorePartialLp
    exact MemLp.coeFn_toLp _
  filter_upwards [cmScoreLp_ae (sourceRate c) (wCoord x) N, e0] with z h1 h2
  exact h1.trans ((congrFun (cmScore_sourceRate_eq c x N) z).trans h2.symm)

end NlsGge.Ramer.General
