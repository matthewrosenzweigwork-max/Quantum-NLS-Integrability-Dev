import NlsGge.Ramer.TruncatedDerivConvergence
import NlsGge.Ramer.CylindricalClosability

/-!
# The divergences of the truncated fields converge in `L²(γ)`

See `TruncatedDivergenceLimit.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-- v2's truncated field `G_N(x) = P_N G(P_N x)` on the finite head `V_N = P_N H`. -/
def truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (N : ℕ) :
    actualCMHead c N → actualCMHead c N :=
  fun v => cmTrunc c N (G (headToE c s N v))

theorem headToE_eq_cmToFull (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (N : ℕ) (v : actualCMHead c N) :
    headToE c s N v = cmToFullWeightedHilbert c s hs0 (v : ActualCM c) :=
  fullWeighted_ext c s (fun _ => rfl)

theorem norm_headToE_apply_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (N : ℕ) (v : actualCMHead c N) : ‖headToE c s N v‖ ≤ ‖v‖ := by
  rw [headToE_eq_cmToFull c s hs0]
  refine (cmToFullWeightedHilbert_norm_le c s hs0 _).trans ?_
  have h1 : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; norm_num
  calc Real.sqrt (1 / 2 : ℝ) * ‖(v : ActualCM c)‖ ≤ 1 * ‖(v : ActualCM c)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖v‖ := by rw [one_mul]; rfl

theorem contDiff_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (N : ℕ) :
    ContDiff ℝ 2 (truncField c s G N) :=
  (cmTrunc c N).contDiff.comp (hG.comp (headToE c s N).contDiff)

theorem norm_truncField_le (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (N : ℕ)
    (v : actualCMHead c N) : ‖truncField c s G N v‖ ≤ B :=
  (norm_cmTrunc_le c N _).trans (hB _)

theorem fderiv_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (N : ℕ)
    (v : actualCMHead c N) :
    fderiv ℝ (truncField c s G N) v =
      (cmTrunc c N).comp ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N)) :=
  ((cmTrunc c N).hasFDerivAt.comp v
    (((hG.differentiable (by norm_num)) (headToE c s N v)).hasFDerivAt.comp v
      (headToE c s N).hasFDerivAt)).fderiv

theorem norm_fderiv_truncField_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (N : ℕ) (v : actualCMHead c N) :
    ‖fderiv ℝ (truncField c s G N) v‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  rw [fderiv_truncField c s G hG]
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 (fun w => ?_)
  calc ‖((cmTrunc c N).comp ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) w‖
      = ‖cmTrunc c N (fderiv ℝ G (headToE c s N v) (headToE c s N w))‖ := rfl
    _ ≤ ‖fderiv ℝ G (headToE c s N v) (headToE c s N w)‖ := norm_cmTrunc_le c N _
    _ ≤ ‖fderiv ℝ G (headToE c s N v)‖ * ‖headToE c s N w‖ := (fderiv ℝ G _).le_opNorm _
    _ ≤ B * ‖w‖ := mul_le_mul (hDB _) (norm_headToE_apply_le c s hs0 N w) (norm_nonneg _) hB0


/-! ### The Hilbert-Schmidt term of the lifted difference -/

theorem levelProj_eq_cmTrunc (c : BoundedCoefficients lower upper) (N M : ℕ)
    (u : actualCMHead c M) : levelProj c N M u = cmTrunc c N (u : ActualCM c) := by
  apply Subtype.ext
  apply cmCoord_ext
  intro n
  rw [cmCoord_levelProj, cmCoord_cmTrunc]

/-- The `p`-th basis column of the truncated derivative at `w`. -/
def truncDerivBasis (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (N : ℕ) (w : actualCMHead c N)
    (p : ℤ × Fin 2) : ActualCM c :=
  ((cmTrunc c N (fderiv ℝ G (headToE c s N w)
    (cmToFullWeightedHilbert c s hs0
      ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) :
        actualCMHead c N) : ActualCM c))) : actualCMHead c N) : ActualCM c)

theorem fderiv_lift_apply (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (g : actualCMHead c N → actualCMHead c N) (hg : Differentiable ℝ g) (x u : actualCMHead c M) :
    fderiv ℝ (liftField c h g) x u =
      levelIncl c h (fderiv ℝ g (levelProj c N M x) (levelProj c N M u)) := by
  have hGD : fderiv ℝ (liftField c h g) x =
      (levelIncl c h).comp ((fderiv ℝ g (levelProj c N M x)).comp (levelProj c N M)) := by
    have h1 := (hg (levelProj c N M x)).hasFDerivAt.comp x (levelProj c N M).hasFDerivAt
    exact ((levelIncl c h).hasFDerivAt.comp x h1).fderiv
  rw [hGD]; rfl

theorem norm_fderiv_diff_basis (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) {N M : ℕ} (h : N ≤ M)
    (x : actualCMHead c M) (q : headIndex M) :
    ‖fderiv ℝ (fun y => liftField c h (truncField c s G N) y - truncField c s G M y) x
        (headBasis c M q)‖ =
      ‖truncDerivBasis c s hs0 G N (levelProj c N M x) q.1 -
        truncDerivBasis c s hs0 G M x q.1‖ := by
  have hq := mem_headIndex.1 q.2
  have hgN : Differentiable ℝ (truncField c s G N) :=
    (contDiff_truncField c s G hG N).differentiable (by norm_num)
  have hgM : Differentiable ℝ (truncField c s G M) :=
    (contDiff_truncField c s G hG M).differentiable (by norm_num)
  have hL : Differentiable ℝ (liftField c h (truncField c s G N)) :=
    (levelIncl c h).differentiable.comp (hgN.comp (levelProj c N M).differentiable)
  have hb : (headBasis c M q : actualCMHead c M) =
      ⟨weightedRealHilbertBasis (cmModeWeight c) q.1, basis_mem_actualCMHead c M q.1 hq⟩ :=
    congrFun (OrthonormalBasis.coe_mk _ _) q
  rw [fderiv_fun_sub (hL x) (hgM x), sub_apply, fderiv_lift_apply c h _ hgN]
  rw [hb]
  have hN1 : ((levelIncl c h (fderiv ℝ (truncField c s G N) (levelProj c N M x)
      (levelProj c N M ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
        basis_mem_actualCMHead c M q.1 hq⟩)) : actualCMHead c M) : ActualCM c) =
      truncDerivBasis c s hs0 G N (levelProj c N M x) q.1 := by
    rw [coe_levelIncl, fderiv_truncField c s G hG]
    unfold truncDerivBasis
    change ((cmTrunc c N (fderiv ℝ G (headToE c s N (levelProj c N M x))
      (headToE c s N (levelProj c N M ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
        basis_mem_actualCMHead c M q.1 hq⟩))) : actualCMHead c N) : ActualCM c) = _
    have e : headToE c s N (levelProj c N M ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
        basis_mem_actualCMHead c M q.1 hq⟩) = cmToFullWeightedHilbert c s hs0
        ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) q.1) :
          actualCMHead c N) : ActualCM c) := by
      rw [headToE_eq_cmToFull c s hs0, levelProj_eq_cmTrunc]
    rw [e]
  have hN2 : ((fderiv ℝ (truncField c s G M) x
      ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
        basis_mem_actualCMHead c M q.1 hq⟩ : actualCMHead c M) : ActualCM c) =
      truncDerivBasis c s hs0 G M x q.1 := by
    rw [fderiv_truncField c s G hG]
    unfold truncDerivBasis
    change ((cmTrunc c M (fderiv ℝ G (headToE c s M x)
      (headToE c s M ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
        basis_mem_actualCMHead c M q.1 hq⟩))) : ActualCM c) = _
    rw [headToE_basis c s hs0 M q.1 hq, cmTrunc_basis_of_mem c M q.1 hq]
  rw [← hN1, ← hN2]
  rfl


theorem ofReal_norm_sub_sq_le {E : Type*} [NormedAddCommGroup E] (a b t : E) :
    ENNReal.ofReal (‖a - b‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖a - t‖ ^ 2) + 2 * ENNReal.ofReal (‖b - t‖ ^ 2) := by
  have h : ‖a - b‖ ^ 2 ≤ 2 * ‖a - t‖ ^ 2 + 2 * ‖b - t‖ ^ 2 := by
    have h1 : ‖a - b‖ ≤ ‖a - t‖ + ‖b - t‖ := by
      calc ‖a - b‖ = ‖(a - t) - (b - t)‖ := by congr 1; abel
        _ ≤ ‖a - t‖ + ‖b - t‖ := norm_sub_le _ _
    nlinarith [sq_nonneg (‖a - t‖ - ‖b - t‖), norm_nonneg (a - b), norm_nonneg (a - t),
      norm_nonneg (b - t)]
  calc ENNReal.ofReal (‖a - b‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a - t‖ ^ 2 + 2 * ‖b - t‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (‖a - t‖ ^ 2) + 2 * ENNReal.ofReal (‖b - t‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp

theorem ofReal_hsNormSq_diff_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) {N M : ℕ} (h : N ≤ M)
    (x : actualCMHead c M) (t : ℤ × Fin 2 → ActualCM c) :
    ENNReal.ofReal (hsNormSq (fderiv ℝ
        (fun y => liftField c h (truncField c s G N) y - truncField c s G M y) x)) ≤
      2 * ∑' p : ℤ × Fin 2, ENNReal.ofReal
          (‖truncDerivBasis c s hs0 G N (levelProj c N M x) p - t p‖ ^ 2) +
      2 * ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖truncDerivBasis c s hs0 G M x p - t p‖ ^ 2) := by
  rw [hsNormSq_eq_sum_norm_sq (headBasis c M)]
  simp_rw [norm_fderiv_diff_basis c s hs0 G hG h x]
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => sq_nonneg _)]
  calc ∑ q : headIndex M, ENNReal.ofReal (‖truncDerivBasis c s hs0 G N (levelProj c N M x) q.1 -
        truncDerivBasis c s hs0 G M x q.1‖ ^ 2)
      ≤ ∑ q : headIndex M, (2 * ENNReal.ofReal
          (‖truncDerivBasis c s hs0 G N (levelProj c N M x) q.1 - t q.1‖ ^ 2) +
          2 * ENNReal.ofReal (‖truncDerivBasis c s hs0 G M x q.1 - t q.1‖ ^ 2)) :=
        Finset.sum_le_sum fun q _ => ofReal_norm_sub_sq_le _ _ _
    _ = ∑ p ∈ headIndex M, (2 * ENNReal.ofReal
          (‖truncDerivBasis c s hs0 G N (levelProj c N M x) p - t p‖ ^ 2) +
          2 * ENNReal.ofReal (‖truncDerivBasis c s hs0 G M x p - t p‖ ^ 2)) :=
        Finset.sum_coe_sort (headIndex M) (fun p => 2 * ENNReal.ofReal
          (‖truncDerivBasis c s hs0 G N (levelProj c N M x) p - t p‖ ^ 2) +
          2 * ENNReal.ofReal (‖truncDerivBasis c s hs0 G M x p - t p‖ ^ 2))
    _ ≤ ∑' p : ℤ × Fin 2, (2 * ENNReal.ofReal
          (‖truncDerivBasis c s hs0 G N (levelProj c N M x) p - t p‖ ^ 2) +
          2 * ENNReal.ofReal (‖truncDerivBasis c s hs0 G M x p - t p‖ ^ 2)) :=
        ENNReal.sum_le_tsum _
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]


/-! ### The mixed-level `L²` estimate -/

theorem integral_sq_cylDiv_truncField_diff_le (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs0 : 0 ≤ s) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) {N M : ℕ} (h : N ≤ M) :
    Integrable (fun z => (cylDiv c N (truncField c s G N) z -
        cylDiv c M (truncField c s G M) z) ^ 2)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    Integrable (fun z => ‖cylField c N (truncField c s G N) z -
        cylField c M (truncField c s G M) z‖ ^ 2)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    Integrable (fun z => hsNormSq (fderiv ℝ
        (fun y => liftField c h (truncField c s G N) y - truncField c s G M y)
        (headPt c M z))) (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    ∫ z, (cylDiv c N (truncField c s G N) z - cylDiv c M (truncField c s G M) z) ^ 2
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
      ∫ z, ‖cylField c N (truncField c s G N) z - cylField c M (truncField c s G M) z‖ ^ 2
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
      ∫ z, hsNormSq (fderiv ℝ
          (fun y => liftField c h (truncField c s G N) y - truncField c s G M y)
          (headPt c M z)) ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  set gN := truncField c s G N with hgN
  set gM := truncField c s G M with hgM
  have hgN2 : ContDiff ℝ 2 gN := contDiff_truncField c s G hG N
  have hgM2 : ContDiff ℝ 2 gM := contDiff_truncField c s G hG M
  have hgN1 : ContDiff ℝ 1 gN := hgN2.of_le (by norm_num)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨hL1, hLg, hLD⟩ := liftField_growth c h gN hgN1 B 0
    (fun v => by rw [pow_zero, mul_one]; exact norm_truncField_le c s G B hB N v)
    (fun v => by rw [pow_zero, mul_one]; exact norm_fderiv_truncField_le c s hs0 G hG B hDB N v)
  have hL2 : ContDiff ℝ 2 (liftField c h gN) :=
    (levelIncl c h).contDiff.comp (hgN2.comp (levelProj c N M).contDiff)
  have hΔ : ContDiff ℝ 2 (fun y => liftField c h gN y - gM y) := hL2.sub hgM2
  have hLd : Differentiable ℝ (liftField c h gN) := hL2.differentiable (by norm_num)
  have hMd : Differentiable ℝ gM := hgM2.differentiable (by norm_num)
  have hΔg : ∀ v, ‖liftField c h gN v - gM v‖ ≤ (2 * B) * (1 + ‖v‖) ^ 0 := by
    intro v
    rw [pow_zero, mul_one]
    have h1 := hLg v
    rw [pow_zero, mul_one] at h1
    have h2 := norm_truncField_le c s G B hB M v
    calc ‖liftField c h gN v - gM v‖ ≤ ‖liftField c h gN v‖ + ‖gM v‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith
  have hΔD : ∀ v, ‖fderiv ℝ (fun y => liftField c h gN y - gM y) v‖ ≤ (2 * B) * (1 + ‖v‖) ^ 0 := by
    intro v
    rw [pow_zero, mul_one, fderiv_fun_sub (hLd v) (hMd v)]
    have h1 := hLD v
    rw [pow_zero, mul_one] at h1
    have h2 := norm_fderiv_truncField_le c s hs0 G hG B hDB M v
    calc ‖fderiv ℝ (liftField c h gN) v - fderiv ℝ gM v‖
        ≤ ‖fderiv ℝ (liftField c h gN) v‖ + ‖fderiv ℝ gM v‖ := by
          rw [sub_eq_add_neg]
          exact (ContinuousLinearMap.opNorm_add_le _ _).trans
            (by rw [ContinuousLinearMap.opNorm_neg])
      _ ≤ 2 * B := by linarith
  have key := integral_sq_cylDiv_le_of_growth c M (fun y => liftField c h gN y - gM y) hΔ
    (2 * B) 0 hΔg hΔD
  have hdiv : ∀ z, cylDiv c M (fun y => liftField c h gN y - gM y) z =
      cylDiv c N gN z - cylDiv c M gM z := fun z => by
    unfold cylDiv
    rw [finiteGaussianDivergence_sub _ _ _ (hLd _) (hMd _)]
    have := cylDiv_lift c h gN (hgN2.differentiable (by norm_num)) z
    unfold cylDiv at this
    rw [this]
  have hfield : ∀ z, cylField c M (fun y => liftField c h gN y - gM y) z =
      cylField c N gN z - cylField c M gM z := fun z => by
    rw [← cylField_lift c h gN z]; rfl
  simp only [hdiv, hfield] at key
  exact key


/-! ### The two error terms -/

/-- Squared `H`-distance of the truncated field to `G ∘ ξ`, in `ℝ≥0∞`. -/
def fieldErr (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (N : ℕ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖cylField c N (truncField c s G N) z -
    G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖ ^ 2)

/-- Squared Hilbert-Schmidt distance (as an `ℝ≥0∞` basis sum) of the truncated derivative to
`DG(ξ(z)) ∘ i`. -/
def derivErr (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (N : ℕ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖truncDerivBasis c s hs0 G N (headPt c N z) p -
    fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
      (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))‖ ^ 2)

theorem measurable_fieldDist (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) (N : ℕ) :
    Measurable (fun z => ‖cylField c N (truncField c s G N) z -
      G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) := by
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hc : Continuous (fun v : actualCMHead c N =>
      ((cmTrunc c N (G (headToE c s N v)) : actualCMHead c N) : ActualCM c)) :=
    continuous_subtype_val.comp ((cmTrunc c N).continuous.comp
      (hG.comp (headToE c s N).continuous))
  have h1 : Measurable (fun z => cylField c N (truncField c s G N) z) :=
    hc.measurable.comp (measurable_headPt c N)
  have h2 : Measurable (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :=
    hG.measurable.comp hRm
  exact (h1.sub h2).norm

theorem measurable_fieldErr (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) (N : ℕ) :
    Measurable (fieldErr c s G N) :=
  ENNReal.measurable_ofReal.comp ((measurable_fieldDist c s G hG N).pow_const 2)

theorem measurable_derivErr (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (N : ℕ) :
    Measurable (derivErr c s hs0 G N) := by
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  refine Measurable.tsum (fun p => ?_)
  have hc : Continuous (fun v : actualCMHead c N => truncDerivBasis c s hs0 G N v p) :=
    continuous_subtype_val.comp ((cmTrunc c N).continuous.comp
      ((hD.comp (headToE c s N).continuous).clm_apply continuous_const))
  have h1 := hc.measurable.comp (measurable_headPt c N)
  have hc2 : Continuous (fun x : FullWeightedHilbert c s => fderiv ℝ G x
      (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))) :=
    hD.clm_apply continuous_const
  have h2 := hc2.measurable.comp hRm
  exact ENNReal.measurable_ofReal.comp ((h1.sub h2).norm.pow_const 2)


theorem eLpNorm_two_pow_two {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) (by norm_num) hf
  simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  have h' : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    have e : ((2 : NNReal) : ℝ≥0∞) = 2 := rfl
    rw [e] at h; exact h
  rw [h']
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem tendsto_lintegral_fieldErr (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G)
    (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N => ∫⁻ z, fieldErr c s G N z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val))
      atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_truncatedField c s hs G hG B hB
  have h2 := (ENNReal.continuous_pow 2).tendsto 0 |>.comp h
  simp only [Function.comp_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h2
  refine h2.congr (fun N => ?_)
  rw [eLpNorm_two_pow_two]
  · rfl
  · exact (measurable_fieldDist c s G hG N).aestronglyMeasurable


theorem tendsto_lintegral_derivErr (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G)
    (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N => ∫⁻ z, derivErr c s (le_of_lt (by linarith : 0 < s)) G N z
      ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) :=
  tendsto_lintegral_hs_truncatedDeriv c s hs G hG B hDB

theorem lintegral_two_mul_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ z, (2 * f z + 2 * g z) ∂μ = 2 * ∫⁻ z, f z ∂μ + 2 * ∫⁻ z, g z ∂μ := by
  rw [lintegral_add_left (hf.const_mul 2), lintegral_const_mul 2 hf, lintegral_const_mul 2 hg]

/-- **Mixed-level `L²` estimate** (v2 Cauchy argument): for `N ≤ M`,
`‖δ_cyl G_N − δ_cyl G_M‖²_{L²(γ)} ≤ 2 (E_N + E_M)` with `E_N` the sum of the field and
derivative errors of the truncation at level `N`. -/
theorem lintegral_sq_cylDiv_truncField_diff_le (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs0 : 0 ≤ s) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) {N M : ℕ} (h : N ≤ M) :
    ∫⁻ z, ENNReal.ofReal ((cylDiv c N (truncField c s G N) z -
        cylDiv c M (truncField c s G M) z) ^ 2)
      ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
    2 * (∫⁻ z, fieldErr c s G N z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
        ∫⁻ z, derivErr c s hs0 G N z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) +
    2 * (∫⁻ z, fieldErr c s G M z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
        ∫⁻ z, derivErr c s hs0 G M z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  obtain ⟨i1, i2, i3, hle⟩ := integral_sq_cylDiv_truncField_diff_le c s hs0 G hG B hB hDB h
  have hG0 : Continuous G := hG.continuous
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hfe : ∀ K, Measurable (fieldErr c s G K) := fun K => measurable_fieldErr c s G hG0 K
  have hde : ∀ K, Measurable (derivErr c s hs0 G K) := fun K => measurable_derivErr c s hs0 G hG1 K
  have hpt1 : ∀ z, ENNReal.ofReal (‖cylField c N (truncField c s G N) z -
      cylField c M (truncField c s G M) z‖ ^ 2) ≤ 2 * fieldErr c s G N z + 2 * fieldErr c s G M z :=
    fun z => ofReal_norm_sub_sq_le _ _ _
  have hpt2 : ∀ z, ENNReal.ofReal (hsNormSq (fderiv ℝ
      (fun y => liftField c h (truncField c s G N) y - truncField c s G M y) (headPt c M z))) ≤
      2 * derivErr c s hs0 G N z + 2 * derivErr c s hs0 G M z := by
    intro z
    have := ofReal_hsNormSq_diff_le c s hs0 G hG h (headPt c M z)
      (fun p => fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
        (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p)))
    rw [levelProj_headPt c h] at this
    exact this
  calc ∫⁻ z, ENNReal.ofReal ((cylDiv c N (truncField c s G N) z -
        cylDiv c M (truncField c s G M) z) ^ 2) ∂γ
      = ENNReal.ofReal (∫ z, (cylDiv c N (truncField c s G N) z -
        cylDiv c M (truncField c s G M) z) ^ 2 ∂γ) :=
        (ofReal_integral_eq_lintegral_ofReal i1 (Eventually.of_forall fun z => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (∫ z, ‖cylField c N (truncField c s G N) z -
          cylField c M (truncField c s G M) z‖ ^ 2 ∂γ +
        ∫ z, hsNormSq (fderiv ℝ
          (fun y => liftField c h (truncField c s G N) y - truncField c s G M y)
          (headPt c M z)) ∂γ) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (∫ z, ‖cylField c N (truncField c s G N) z -
          cylField c M (truncField c s G M) z‖ ^ 2 ∂γ) +
        ENNReal.ofReal (∫ z, hsNormSq (fderiv ℝ
          (fun y => liftField c h (truncField c s G N) y - truncField c s G M y)
          (headPt c M z)) ∂γ) :=
        ENNReal.ofReal_add (integral_nonneg fun z => sq_nonneg _)
          (integral_nonneg fun z => hsNormSq_nonneg _)
    _ = ∫⁻ z, ENNReal.ofReal (‖cylField c N (truncField c s G N) z -
          cylField c M (truncField c s G M) z‖ ^ 2) ∂γ +
        ∫⁻ z, ENNReal.ofReal (hsNormSq (fderiv ℝ
          (fun y => liftField c h (truncField c s G N) y - truncField c s G M y)
          (headPt c M z))) ∂γ := by
        rw [ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun z => sq_nonneg _),
          ofReal_integral_eq_lintegral_ofReal i3
            (Eventually.of_forall fun z => hsNormSq_nonneg _)]
    _ ≤ ∫⁻ z, (2 * fieldErr c s G N z + 2 * fieldErr c s G M z) ∂γ +
        ∫⁻ z, (2 * derivErr c s hs0 G N z + 2 * derivErr c s hs0 G M z) ∂γ :=
        add_le_add (lintegral_mono hpt1) (lintegral_mono hpt2)
    _ = _ := by
        rw [lintegral_two_mul_add (hfe N) (hfe M), lintegral_two_mul_add (hde N) (hde M)]
        ring


/-! ### The divergences of the truncated fields converge in `L²(γ)` -/

theorem memLp_cylDiv_truncField (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (N : ℕ) :
    MemLp (cylDiv c N (truncField c s G N)) 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hg := contDiff_truncField c s G hG N
  refine (memLp_two_iff_integrable_sq
    (aestronglyMeasurable_cylDiv c _ (hg.of_le (by norm_num)))).2 ?_
  exact (integral_sq_cylDiv_le_of_growth c N _ hg B 0
    (fun v => by rw [pow_zero, mul_one]; exact norm_truncField_le c s G B hB N v)
    (fun v => by rw [pow_zero, mul_one]; exact norm_fderiv_truncField_le c s hs0 G hG B hDB N v)).1

theorem eLpNorm_sq_cylDiv_truncField_diff_le (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs0 : 0 ≤ s) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (N M : ℕ) :
    eLpNorm (cylDiv c N (truncField c s G N) - cylDiv c M (truncField c s G M)) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) ^ 2 ≤
      2 * (∫⁻ z, fieldErr c s G N z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
        ∫⁻ z, derivErr c s hs0 G N z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) +
      2 * (∫⁻ z, fieldErr c s G M z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
        ∫⁻ z, derivErr c s hs0 G M z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) := by
  have hN := memLp_cylDiv_truncField c s hs0 G hG B hB hDB N
  have hM := memLp_cylDiv_truncField c s hs0 G hG B hB hDB M
  rcases le_total N M with h | h
  · rw [eLpNorm_two_pow_two _ _ (hN.sub hM).aestronglyMeasurable]
    exact lintegral_sq_cylDiv_truncField_diff_le c s hs0 G hG B hB hDB h
  · rw [eLpNorm_sub_comm, eLpNorm_two_pow_two _ _ (hM.sub hN).aestronglyMeasurable, add_comm]
    exact lintegral_sq_cylDiv_truncField_diff_le c s hs0 G hG B hB hDB h


/-- **Divergences of the truncated fields converge in `L²(γ)`** (v2: `δ G_N` is Cauchy in
`L²(γ)` for `G_N(x) = P_N G(P_N x)`, `G` a `C²` field `E_s → H` with bounded value and
derivative, `s > 1/2`). The limit `η` is an `L²(γ)` function and
`‖δ_cyl G_N − η‖_{L²(γ)} → 0`. -/
theorem exists_tendsto_cylDiv_truncField {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : (1:ℝ)/2 < s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    ∃ η : (ℤ → ℂ) → ℝ, MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      Tendsto (fun N => eLpNorm (fun z => cylDiv c N (truncField c s G N) z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : 0 < s)
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set E : ℕ → ℝ≥0∞ := fun K => ∫⁻ z, fieldErr c s G K z ∂γ + ∫⁻ z, derivErr c s hs0 G K z ∂γ
    with hE
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have := (tendsto_lintegral_fieldErr c s hs G hG.continuous B hB).add
      (tendsto_lintegral_derivErr c s hs G (hG.of_le (by norm_num)) B hDB)
    simpa using this
  have hf := memLp_cylDiv_truncField c s hs0 G hG B hB hDB
  have hbound := eLpNorm_sq_cylDiv_truncField_diff_le c s hs0 G hG B hB hDB
  set u : ℕ → MeasureTheory.Lp ℝ 2 γ := fun N => (hf N).toLp _ with hu
  have hcauchy : CauchySeq u := by
    rw [EMetric.cauchySeq_iff_NNReal]
    intro ε hε
    set δ : NNReal := ε ^ 2 / 4 with hδ
    have hδ0 : (0 : ℝ≥0∞) < δ := by
      rw [ENNReal.coe_pos, hδ]; positivity
    have h4 : (2 : ℝ≥0∞) * δ + 2 * δ = (ε : ℝ≥0∞) ^ 2 := by
      have : (2 : NNReal) * δ + 2 * δ = ε ^ 2 := by rw [hδ]; ring
      exact_mod_cast this
    obtain ⟨N, hN⟩ := (eventually_atTop.1 ((hE0.eventually (gt_mem_nhds hδ0))))
    refine ⟨N, fun n hn => ?_⟩
    rw [hu]
    simp only [Lp.edist_toLp_toLp]
    have h1 := hbound n N
    have h2 : 2 * E n + 2 * E N < (ε : ℝ≥0∞) ^ 2 := by
      rw [← h4]
      exact ENNReal.add_lt_add (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) (hN n hn))
        (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) (hN N le_rfl))
    by_contra hcon
    have h3 := pow_le_pow_left₀ (zero_le) (not_lt.1 hcon) 2
    exact absurd (lt_of_le_of_lt h1 h2) (not_lt.2 h3)
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨F, Lp.memLp F, ?_⟩
  rw [tendsto_iff_edist_tendsto_0] at hF
  refine hF.congr (fun N => ?_)
  rw [Lp.edist_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hf N).coeFn_toLp] with z hz
  simp only [Pi.sub_apply, hu, hz]

end NlsGge.Ramer
