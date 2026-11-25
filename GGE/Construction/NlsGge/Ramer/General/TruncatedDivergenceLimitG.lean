import NlsGge.Ramer.General.TruncatedDerivConvergenceG
import NlsGge.Ramer.General.CylindricalClosabilityG

/-!
# The divergences of the truncated fields converge in `L²(γ)` (GB3)

Generalization of `NlsGge/Ramer/TruncatedDivergenceLimit.lean` to a `RamerSetting S`.
`G : S.E → S.H`, `γ = S.γ`, `ξ = S.R`, `i = S.incl`. The only constant change is the head
inclusion bound `‖headToE v‖ ≤ √ratioSup ‖v‖` (replacing `≤ ‖v‖`), so the derivative bound of the
truncated field is `B √ratioSup`; the final theorem keeps the hypotheses `‖G‖ ≤ B`,
`‖DG‖ ≤ B` unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- v2's truncated field `G_N(x) = P_N G(P_N x)` on the finite head `V_N = P_N H`. -/
def truncField (G : S.E → S.H) (N : ℕ) : S.head N → S.head N :=
  fun v => S.cmTrunc N (G (S.headToE N v))

theorem contDiff_truncField (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (N : ℕ) :
    ContDiff ℝ 2 (S.truncField G N) :=
  (S.cmTrunc N).contDiff.comp (hG.comp (S.headToE N).contDiff)

theorem norm_truncField_le (G : S.E → S.H) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (N : ℕ)
    (v : S.head N) : ‖S.truncField G N v‖ ≤ B :=
  (S.norm_cmTrunc_le N _).trans (hB _)

theorem fderiv_truncField (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (N : ℕ) (v : S.head N) :
    fderiv ℝ (S.truncField G N) v =
      (S.cmTrunc N).comp ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N)) :=
  ((S.cmTrunc N).hasFDerivAt.comp v
    (((hG.differentiable (by norm_num)) (S.headToE N v)).hasFDerivAt.comp v
      (S.headToE N).hasFDerivAt)).fderiv

theorem norm_fderiv_truncField_le (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (N : ℕ) (v : S.head N) :
    ‖fderiv ℝ (S.truncField G N) v‖ ≤ B * Real.sqrt S.ratioSup := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  have hκ : 0 ≤ Real.sqrt S.ratioSup := Real.sqrt_nonneg _
  rw [S.fderiv_truncField G hG]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB0 hκ) (fun w => ?_)
  calc ‖((S.cmTrunc N).comp ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) w‖
      = ‖S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.headToE N w))‖ := rfl
    _ ≤ ‖fderiv ℝ G (S.headToE N v) (S.headToE N w)‖ := S.norm_cmTrunc_le N _
    _ ≤ ‖fderiv ℝ G (S.headToE N v)‖ * ‖S.headToE N w‖ := (fderiv ℝ G _).le_opNorm _
    _ ≤ B * (Real.sqrt S.ratioSup * ‖w‖) :=
        mul_le_mul (hDB _) (S.norm_headToE_le N w) (norm_nonneg _) hB0
    _ = B * Real.sqrt S.ratioSup * ‖w‖ := by ring


/-! ### The Hilbert-Schmidt term of the lifted difference -/

theorem levelProj_eq_cmTrunc (N M : ℕ) (u : S.head M) :
    S.levelProj N M u = S.cmTrunc N (u : S.H) := by
  apply Subtype.ext
  apply S.hcoord_ext
  intro n
  rw [S.hcoord_levelProj, S.hcoord_cmTrunc]

/-- The `p`-th basis column of the truncated derivative at `w`. -/
def truncDerivBasis (G : S.E → S.H) (N : ℕ) (w : S.head N) (p : ℤ × Fin 2) : S.H :=
  ((S.cmTrunc N (fderiv ℝ G (S.headToE N w)
    (S.incl ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) : S.H))) :
      S.head N) : S.H)

theorem fderiv_lift_apply {N M : ℕ} (h : N ≤ M)
    (g : S.head N → S.head N) (hg : Differentiable ℝ g) (x u : S.head M) :
    fderiv ℝ (S.liftField h g) x u =
      S.levelIncl h (fderiv ℝ g (S.levelProj N M x) (S.levelProj N M u)) := by
  have hGD : fderiv ℝ (S.liftField h g) x =
      (S.levelIncl h).comp ((fderiv ℝ g (S.levelProj N M x)).comp (S.levelProj N M)) := by
    have h1 := (hg (S.levelProj N M x)).hasFDerivAt.comp x (S.levelProj N M).hasFDerivAt
    exact ((S.levelIncl h).hasFDerivAt.comp x h1).fderiv
  rw [hGD]; rfl

theorem norm_fderiv_diff_basis (G : S.E → S.H) (hG : ContDiff ℝ 2 G) {N M : ℕ} (h : N ≤ M)
    (x : S.head M) (q : headIndex M) :
    ‖fderiv ℝ (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y) x
        (S.headBasis M q)‖ =
      ‖S.truncDerivBasis G N (S.levelProj N M x) q.1 - S.truncDerivBasis G M x q.1‖ := by
  have hq := mem_headIndex.1 q.2
  have hgN : Differentiable ℝ (S.truncField G N) :=
    (S.contDiff_truncField G hG N).differentiable (by norm_num)
  have hgM : Differentiable ℝ (S.truncField G M) :=
    (S.contDiff_truncField G hG M).differentiable (by norm_num)
  have hL : Differentiable ℝ (S.liftField h (S.truncField G N)) :=
    (S.levelIncl h).differentiable.comp (hgN.comp (S.levelProj N M).differentiable)
  have hb : (S.headBasis M q : S.head M) =
      ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head M q.1 hq⟩ :=
    congrFun (OrthonormalBasis.coe_mk _ _) q
  rw [fderiv_fun_sub (hL x) (hgM x), sub_apply,
    S.fderiv_lift_apply h _ hgN]
  rw [hb]
  have hN1 : ((S.levelIncl h (fderiv ℝ (S.truncField G N) (S.levelProj N M x)
      (S.levelProj N M ⟨weightedRealHilbertBasis S.cmWeight q.1,
        S.basis_mem_head M q.1 hq⟩)) : S.head M) : S.H) =
      S.truncDerivBasis G N (S.levelProj N M x) q.1 := by
    rw [S.coe_levelIncl, S.fderiv_truncField G hG]
    unfold truncDerivBasis
    change ((S.cmTrunc N (fderiv ℝ G (S.headToE N (S.levelProj N M x))
      (S.headToE N (S.levelProj N M ⟨weightedRealHilbertBasis S.cmWeight q.1,
        S.basis_mem_head M q.1 hq⟩))) : S.head N) : S.H) = _
    have e : S.headToE N (S.levelProj N M ⟨weightedRealHilbertBasis S.cmWeight q.1,
        S.basis_mem_head M q.1 hq⟩) = S.incl
        ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight q.1) : S.head N) : S.H) := by
      rw [S.headToE_apply, S.levelProj_eq_cmTrunc]
    rw [e]
  have hN2 : ((fderiv ℝ (S.truncField G M) x
      ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head M q.1 hq⟩ : S.head M) :
        S.H) = S.truncDerivBasis G M x q.1 := by
    rw [S.fderiv_truncField G hG]
    unfold truncDerivBasis
    change ((S.cmTrunc M (fderiv ℝ G (S.headToE M x)
      (S.headToE M ⟨weightedRealHilbertBasis S.cmWeight q.1,
        S.basis_mem_head M q.1 hq⟩))) : S.H) = _
    rw [S.headToE_basis M q.1 hq, S.cmTrunc_basis_of_mem M q.1 hq]
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

theorem ofReal_hsNormSq_diff_le (G : S.E → S.H) (hG : ContDiff ℝ 2 G) {N M : ℕ} (h : N ≤ M)
    (x : S.head M) (t : ℤ × Fin 2 → S.H) :
    ENNReal.ofReal (hsNormSq (fderiv ℝ
        (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y) x)) ≤
      2 * ∑' p : ℤ × Fin 2, ENNReal.ofReal
          (‖S.truncDerivBasis G N (S.levelProj N M x) p - t p‖ ^ 2) +
      2 * ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖S.truncDerivBasis G M x p - t p‖ ^ 2) := by
  rw [hsNormSq_eq_sum_norm_sq (S.headBasis M)]
  simp_rw [S.norm_fderiv_diff_basis G hG h x]
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => sq_nonneg _)]
  calc ∑ q : headIndex M, ENNReal.ofReal (‖S.truncDerivBasis G N (S.levelProj N M x) q.1 -
        S.truncDerivBasis G M x q.1‖ ^ 2)
      ≤ ∑ q : headIndex M, (2 * ENNReal.ofReal
          (‖S.truncDerivBasis G N (S.levelProj N M x) q.1 - t q.1‖ ^ 2) +
          2 * ENNReal.ofReal (‖S.truncDerivBasis G M x q.1 - t q.1‖ ^ 2)) :=
        Finset.sum_le_sum fun q _ => ofReal_norm_sub_sq_le _ _ _
    _ = ∑ p ∈ headIndex M, (2 * ENNReal.ofReal
          (‖S.truncDerivBasis G N (S.levelProj N M x) p - t p‖ ^ 2) +
          2 * ENNReal.ofReal (‖S.truncDerivBasis G M x p - t p‖ ^ 2)) :=
        Finset.sum_coe_sort (headIndex M) (fun p => 2 * ENNReal.ofReal
          (‖S.truncDerivBasis G N (S.levelProj N M x) p - t p‖ ^ 2) +
          2 * ENNReal.ofReal (‖S.truncDerivBasis G M x p - t p‖ ^ 2))
    _ ≤ ∑' p : ℤ × Fin 2, (2 * ENNReal.ofReal
          (‖S.truncDerivBasis G N (S.levelProj N M x) p - t p‖ ^ 2) +
          2 * ENNReal.ofReal (‖S.truncDerivBasis G M x p - t p‖ ^ 2)) :=
        ENNReal.sum_le_tsum _
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]


/-! ### The mixed-level `L²` estimate -/

theorem integral_sq_cylDiv_truncField_diff_le (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) {N M : ℕ} (h : N ≤ M) :
    Integrable (fun z => (S.cylDiv N (S.truncField G N) z -
        S.cylDiv M (S.truncField G M) z) ^ 2) S.γ ∧
    Integrable (fun z => ‖S.cylField N (S.truncField G N) z -
        S.cylField M (S.truncField G M) z‖ ^ 2) S.γ ∧
    Integrable (fun z => hsNormSq (fderiv ℝ
        (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y)
        (S.headPt M z))) S.γ ∧
    ∫ z, (S.cylDiv N (S.truncField G N) z - S.cylDiv M (S.truncField G M) z) ^ 2 ∂S.γ ≤
      ∫ z, ‖S.cylField N (S.truncField G N) z - S.cylField M (S.truncField G M) z‖ ^ 2 ∂S.γ +
      ∫ z, hsNormSq (fderiv ℝ
          (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y)
          (S.headPt M z)) ∂S.γ := by
  set gN := S.truncField G N with hgN
  set gM := S.truncField G M with hgM
  set κ := Real.sqrt S.ratioSup with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hgN2 : ContDiff ℝ 2 gN := S.contDiff_truncField G hG N
  have hgM2 : ContDiff ℝ 2 gM := S.contDiff_truncField G hG M
  have hgN1 : ContDiff ℝ 1 gN := hgN2.of_le (by norm_num)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set C := B * (1 + κ) with hC
  have hBC : B ≤ C := by rw [hC]; nlinarith
  have hκC : B * κ ≤ C := by rw [hC]; nlinarith
  have hgb : ∀ K v, ‖S.truncField G K v‖ ≤ C * (1 + ‖v‖) ^ 0 := fun K v => by
    rw [pow_zero, mul_one]; exact (S.norm_truncField_le G B hB K v).trans hBC
  have hDb : ∀ K v, ‖fderiv ℝ (S.truncField G K) v‖ ≤ C * (1 + ‖v‖) ^ 0 := fun K v => by
    rw [pow_zero, mul_one]; exact (S.norm_fderiv_truncField_le G hG B hDB K v).trans hκC
  obtain ⟨hL1, hLg, hLD⟩ := S.liftField_growth h gN hgN1 C 0 (hgb N) (hDb N)
  have hL2 : ContDiff ℝ 2 (S.liftField h gN) :=
    (S.levelIncl h).contDiff.comp (hgN2.comp (S.levelProj N M).contDiff)
  have hΔ : ContDiff ℝ 2 (fun y => S.liftField h gN y - gM y) := hL2.sub hgM2
  have hLd : Differentiable ℝ (S.liftField h gN) := hL2.differentiable (by norm_num)
  have hMd : Differentiable ℝ gM := hgM2.differentiable (by norm_num)
  have hΔg : ∀ v, ‖S.liftField h gN v - gM v‖ ≤ (2 * C) * (1 + ‖v‖) ^ 0 := by
    intro v
    rw [pow_zero, mul_one]
    have h1 := hLg v
    rw [pow_zero, mul_one] at h1
    have h2 := hgb M v
    rw [pow_zero, mul_one] at h2
    calc ‖S.liftField h gN v - gM v‖ ≤ ‖S.liftField h gN v‖ + ‖gM v‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  have hΔD : ∀ v, ‖fderiv ℝ (fun y => S.liftField h gN y - gM y) v‖ ≤
      (2 * C) * (1 + ‖v‖) ^ 0 := by
    intro v
    rw [pow_zero, mul_one, fderiv_fun_sub (hLd v) (hMd v)]
    have h1 := hLD v
    rw [pow_zero, mul_one] at h1
    have h2 := hDb M v
    rw [pow_zero, mul_one] at h2
    calc ‖fderiv ℝ (S.liftField h gN) v - fderiv ℝ gM v‖
        ≤ ‖fderiv ℝ (S.liftField h gN) v‖ + ‖fderiv ℝ gM v‖ := by
          rw [sub_eq_add_neg]
          exact (ContinuousLinearMap.opNorm_add_le _ _).trans
            (by rw [ContinuousLinearMap.opNorm_neg])
      _ ≤ 2 * C := by linarith
  have key := S.integral_sq_cylDiv_le_of_growth M (fun y => S.liftField h gN y - gM y) hΔ
    (2 * C) 0 hΔg hΔD
  have hdiv : ∀ z, S.cylDiv M (fun y => S.liftField h gN y - gM y) z =
      S.cylDiv N gN z - S.cylDiv M gM z := fun z => by
    unfold cylDiv
    rw [finiteGaussianDivergence_sub _ _ _ (hLd _) (hMd _)]
    have := S.cylDiv_lift h gN (hgN2.differentiable (by norm_num)) z
    unfold cylDiv at this
    rw [this]
  have hfield : ∀ z, S.cylField M (fun y => S.liftField h gN y - gM y) z =
      S.cylField N gN z - S.cylField M gM z := fun z => by
    rw [← S.cylField_lift h gN z]; rfl
  simp only [hdiv, hfield] at key
  exact key


/-! ### The two error terms -/

/-- Squared `H`-distance of the truncated field to `G ∘ ξ`, in `ℝ≥0∞`. -/
def fieldErr (G : S.E → S.H) (N : ℕ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖S.cylField N (S.truncField G N) z - G (S.R z)‖ ^ 2)

/-- Squared Hilbert-Schmidt distance (as an `ℝ≥0∞` basis sum) of the truncated derivative to
`DG(ξ(z)) ∘ i`. -/
def derivErr (G : S.E → S.H) (N : ℕ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖S.truncDerivBasis G N (S.headPt N z) p -
    fderiv ℝ G (S.R z) (S.incl (weightedRealHilbertBasis S.cmWeight p))‖ ^ 2)

theorem measurable_fieldDist (G : S.E → S.H) (hG : Continuous G) (N : ℕ) :
    Measurable (fun z => ‖S.cylField N (S.truncField G N) z - G (S.R z)‖) := by
  let _ : MeasurableSpace S.H := borel _
  have _ : BorelSpace S.H := ⟨rfl⟩
  have hRm := S.measurable_R
  have hc : Continuous (fun v : S.head N => ((S.cmTrunc N (G (S.headToE N v)) : S.head N) : S.H)) :=
    continuous_subtype_val.comp ((S.cmTrunc N).continuous.comp
      (hG.comp (S.headToE N).continuous))
  have h1 : Measurable (fun z => S.cylField N (S.truncField G N) z) :=
    hc.measurable.comp (S.measurable_headPt N)
  have h2 : Measurable (fun z => G (S.R z)) := hG.measurable.comp hRm
  exact (h1.sub h2).norm

theorem measurable_fieldErr (G : S.E → S.H) (hG : Continuous G) (N : ℕ) :
    Measurable (S.fieldErr G N) :=
  ENNReal.measurable_ofReal.comp ((S.measurable_fieldDist G hG N).pow_const 2)

theorem measurable_derivErr (G : S.E → S.H) (hG : ContDiff ℝ 1 G) (N : ℕ) :
    Measurable (S.derivErr G N) := by
  let _ : MeasurableSpace S.H := borel _
  have _ : BorelSpace S.H := ⟨rfl⟩
  have hRm := S.measurable_R
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  refine Measurable.tsum (fun p => ?_)
  have hc : Continuous (fun v : S.head N => S.truncDerivBasis G N v p) :=
    continuous_subtype_val.comp ((S.cmTrunc N).continuous.comp
      ((hD.comp (S.headToE N).continuous).clm_apply continuous_const))
  have h1 := hc.measurable.comp (S.measurable_headPt N)
  have hc2 : Continuous (fun x : S.E => fderiv ℝ G x
      (S.incl (weightedRealHilbertBasis S.cmWeight p))) :=
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

theorem tendsto_lintegral_fieldErr (G : S.E → S.H) (hG : Continuous G)
    (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N => ∫⁻ z, S.fieldErr G N z ∂S.γ) atTop (𝓝 0) := by
  have h := S.tendsto_eLpNorm_truncatedField G hG B hB
  have h2 := (ENNReal.continuous_pow 2).tendsto 0 |>.comp h
  simp only [Function.comp_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h2
  refine h2.congr (fun N => ?_)
  rw [eLpNorm_two_pow_two]
  · rfl
  · exact (S.measurable_fieldDist G hG N).aestronglyMeasurable


theorem tendsto_lintegral_derivErr (G : S.E → S.H) (hG : ContDiff ℝ 1 G)
    (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N => ∫⁻ z, S.derivErr G N z ∂S.γ) atTop (𝓝 0) :=
  S.tendsto_lintegral_hs_truncatedDeriv G hG B hDB

theorem lintegral_two_mul_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ z, (2 * f z + 2 * g z) ∂μ = 2 * ∫⁻ z, f z ∂μ + 2 * ∫⁻ z, g z ∂μ := by
  rw [lintegral_add_left (hf.const_mul 2), lintegral_const_mul 2 hf, lintegral_const_mul 2 hg]

/-- **Mixed-level `L²` estimate** (v2 Cauchy argument): for `N ≤ M`,
`‖δ_cyl G_N − δ_cyl G_M‖²_{L²(γ)} ≤ 2 (E_N + E_M)` with `E_N` the sum of the field and
derivative errors of the truncation at level `N`. -/
theorem lintegral_sq_cylDiv_truncField_diff_le (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) {N M : ℕ} (h : N ≤ M) :
    ∫⁻ z, ENNReal.ofReal ((S.cylDiv N (S.truncField G N) z -
        S.cylDiv M (S.truncField G M) z) ^ 2) ∂S.γ ≤
    2 * (∫⁻ z, S.fieldErr G N z ∂S.γ + ∫⁻ z, S.derivErr G N z ∂S.γ) +
    2 * (∫⁻ z, S.fieldErr G M z ∂S.γ + ∫⁻ z, S.derivErr G M z ∂S.γ) := by
  set γ := S.γ with hγ
  obtain ⟨i1, i2, i3, hle⟩ := S.integral_sq_cylDiv_truncField_diff_le G hG B hB hDB h
  have hG0 : Continuous G := hG.continuous
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hfe : ∀ K, Measurable (S.fieldErr G K) := fun K => S.measurable_fieldErr G hG0 K
  have hde : ∀ K, Measurable (S.derivErr G K) := fun K => S.measurable_derivErr G hG1 K
  have hpt1 : ∀ z, ENNReal.ofReal (‖S.cylField N (S.truncField G N) z -
      S.cylField M (S.truncField G M) z‖ ^ 2) ≤
      2 * S.fieldErr G N z + 2 * S.fieldErr G M z :=
    fun z => ofReal_norm_sub_sq_le _ _ _
  have hpt2 : ∀ z, ENNReal.ofReal (hsNormSq (fderiv ℝ
      (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y) (S.headPt M z))) ≤
      2 * S.derivErr G N z + 2 * S.derivErr G M z := by
    intro z
    have := S.ofReal_hsNormSq_diff_le G hG h (S.headPt M z)
      (fun p => fderiv ℝ G (S.R z) (S.incl (weightedRealHilbertBasis S.cmWeight p)))
    rw [S.levelProj_headPt h] at this
    exact this
  calc ∫⁻ z, ENNReal.ofReal ((S.cylDiv N (S.truncField G N) z -
        S.cylDiv M (S.truncField G M) z) ^ 2) ∂γ
      = ENNReal.ofReal (∫ z, (S.cylDiv N (S.truncField G N) z -
        S.cylDiv M (S.truncField G M) z) ^ 2 ∂γ) :=
        (ofReal_integral_eq_lintegral_ofReal i1 (Eventually.of_forall fun z => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (∫ z, ‖S.cylField N (S.truncField G N) z -
          S.cylField M (S.truncField G M) z‖ ^ 2 ∂γ +
        ∫ z, hsNormSq (fderiv ℝ
          (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y)
          (S.headPt M z)) ∂γ) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (∫ z, ‖S.cylField N (S.truncField G N) z -
          S.cylField M (S.truncField G M) z‖ ^ 2 ∂γ) +
        ENNReal.ofReal (∫ z, hsNormSq (fderiv ℝ
          (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y)
          (S.headPt M z)) ∂γ) :=
        ENNReal.ofReal_add (integral_nonneg fun z => sq_nonneg _)
          (integral_nonneg fun z => hsNormSq_nonneg _)
    _ = ∫⁻ z, ENNReal.ofReal (‖S.cylField N (S.truncField G N) z -
          S.cylField M (S.truncField G M) z‖ ^ 2) ∂γ +
        ∫⁻ z, ENNReal.ofReal (hsNormSq (fderiv ℝ
          (fun y => S.liftField h (S.truncField G N) y - S.truncField G M y)
          (S.headPt M z))) ∂γ := by
        rw [ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun z => sq_nonneg _),
          ofReal_integral_eq_lintegral_ofReal i3
            (Eventually.of_forall fun z => hsNormSq_nonneg _)]
    _ ≤ ∫⁻ z, (2 * S.fieldErr G N z + 2 * S.fieldErr G M z) ∂γ +
        ∫⁻ z, (2 * S.derivErr G N z + 2 * S.derivErr G M z) ∂γ :=
        add_le_add (lintegral_mono hpt1) (lintegral_mono hpt2)
    _ = _ := by
        rw [lintegral_two_mul_add (hfe N) (hfe M), lintegral_two_mul_add (hde N) (hde M)]
        ring


/-! ### The divergences of the truncated fields converge in `L²(γ)` -/

theorem memLp_cylDiv_truncField (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (N : ℕ) :
    MemLp (S.cylDiv N (S.truncField G N)) 2 S.γ := by
  have hg := S.contDiff_truncField G hG N
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hκ0 : 0 ≤ Real.sqrt S.ratioSup := Real.sqrt_nonneg _
  set C := B * (1 + Real.sqrt S.ratioSup) with hC
  have hBC : B ≤ C := by rw [hC]; nlinarith
  have hκC : B * Real.sqrt S.ratioSup ≤ C := by rw [hC]; nlinarith
  refine (memLp_two_iff_integrable_sq
    (S.aestronglyMeasurable_cylDiv _ (hg.of_le (by norm_num)))).2 ?_
  exact (S.integral_sq_cylDiv_le_of_growth N _ hg C 0
    (fun v => by
      rw [pow_zero, mul_one]; exact (S.norm_truncField_le G B hB N v).trans hBC)
    (fun v => by
      rw [pow_zero, mul_one]
      exact (S.norm_fderiv_truncField_le G hG B hDB N v).trans hκC)).1

theorem eLpNorm_sq_cylDiv_truncField_diff_le (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (N M : ℕ) :
    eLpNorm (S.cylDiv N (S.truncField G N) - S.cylDiv M (S.truncField G M)) 2 S.γ ^ 2 ≤
      2 * (∫⁻ z, S.fieldErr G N z ∂S.γ + ∫⁻ z, S.derivErr G N z ∂S.γ) +
      2 * (∫⁻ z, S.fieldErr G M z ∂S.γ + ∫⁻ z, S.derivErr G M z ∂S.γ) := by
  have hN := S.memLp_cylDiv_truncField G hG B hB hDB N
  have hM := S.memLp_cylDiv_truncField G hG B hB hDB M
  rcases le_total N M with h | h
  · rw [eLpNorm_two_pow_two _ _ (hN.sub hM).aestronglyMeasurable]
    exact S.lintegral_sq_cylDiv_truncField_diff_le G hG B hB hDB h
  · rw [eLpNorm_sub_comm, eLpNorm_two_pow_two _ _ (hM.sub hN).aestronglyMeasurable, add_comm]
    exact S.lintegral_sq_cylDiv_truncField_diff_le G hG B hB hDB h


/-- **Divergences of the truncated fields converge in `L²(γ)`** (v2: `δ G_N` is Cauchy in
`L²(γ)` for `G_N(x) = P_N G(P_N x)`, `G` a `C²` field `E → H` with bounded value and
derivative). The limit `η` is an `L²(γ)` function and
`‖δ_cyl G_N − η‖_{L²(γ)} → 0`. -/
theorem exists_tendsto_cylDiv_truncField
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    ∃ η : (ℤ → ℂ) → ℝ, MemLp η 2 S.γ ∧
      Tendsto (fun N => eLpNorm (fun z => S.cylDiv N (S.truncField G N) z - η z) 2 S.γ)
        atTop (𝓝 0) := by
  set γ := S.γ with hγ
  set E : ℕ → ℝ≥0∞ := fun K => ∫⁻ z, S.fieldErr G K z ∂γ + ∫⁻ z, S.derivErr G K z ∂γ
    with hE
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have := (S.tendsto_lintegral_fieldErr G hG.continuous B hB).add
      (S.tendsto_lintegral_derivErr G (hG.of_le (by norm_num)) B hDB)
    simpa using this
  have hf := S.memLp_cylDiv_truncField G hG B hB hDB
  have hbound := S.eLpNorm_sq_cylDiv_truncField_diff_le G hG B hB hDB
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

end NlsGge.Ramer.General.RamerSetting
