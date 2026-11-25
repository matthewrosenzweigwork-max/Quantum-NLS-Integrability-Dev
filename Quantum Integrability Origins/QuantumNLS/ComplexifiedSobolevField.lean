import QuantumNLS.ComplexifiedConjugation
import QuantumNLS.RiccatiSobolevBanach
import QuantumNLS.Fourier

/-!
# Complexified analytic infrastructure, stage X6: the H^s Fourier model, its conjugation, and the discriminant

For R-3FEAD88B E5 (the auxiliary construction `RiccatiFloquet`). the auxiliary construction's Banach model is `Ell2 = ℓ²(ℤ)` (frozen `RiccatiSobolevBanach`);
a point `x` represents the field with report Fourier coefficients `toField L s x k = x_k / pw L s k`
(DEF-002 weight, `pw L s k = (1 + |2πk/L|)^s`). This module proves, for `0 ≤ s`:
* `ellConj`: the conjugation `(J x)_k = conj(x_{−k})` on `Ell2` (a `Conj` of stage X4: conjugate-linear, involutive,
  isometric), the `H^s` complexified conjugation;
* `eL n`: the orthonormal report modes `e_n = L^{-1/2} exp(2πinx/L)` in `L²(𝕋_L)` (`orthonormal_eL`,
  `inner_eL`: `⟪e_n, u⟫ = Fourier.coeff L u n`);
* **`fieldMap L s hs : Ell2 →L[ℂ] L²(𝕋_L)`**, `x ↦ Σ_k (x_k / pw_k) e_k` (norm ≤ 1), with
  `coeff_fieldMap`: the report coefficients of `fieldMap x` are exactly `toField L s x`, and
  `fieldMap_jEll`: `fieldMap (J x) = star (fieldMap x)` (the `H^s` conjugation is the pointwise conjugation);
* **`cxDisc_field_analytic`**: `(x, y, z) ↦ cxDisc κ (fieldMap x) (fieldMap y) z` is complex analytic on all of
  `Ell2 × Ell2 × ℂ`; **`cxDisc_field_real`**: on the real slice `y = J x` it equals the physical discriminant
  `L2SpatialTransfer.discriminant κ (fieldMap x) z`; **`cxDisc_field_local`** (importable): near any
  `p₀ = (x₀, y₀, z₀)` (in particular `(φ₀, J φ₀, z₀)`) and for any radius, complex differentiable, complex analytic
  and bounded on the ball, with the real-slice agreement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

open Set Metric MeasureTheory ComplexConjugate

namespace QuantumNLS.ComplexifiedSobolevField

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
  QuantumNLS.ComplexifiedConjugation QuantumNLS.ComplexifiedDiscriminant
open PhysicalTensor (L2T)

/-! ### The conjugation on the Fourier model -/

theorem summable_jFun (x : Ell2) : Summable (fun k : ℤ => ‖conj (x (-k))‖ ^ 2) := by
  have h := (summable_sq x).comp_injective neg_injective
  refine h.congr fun k => ?_
  simp

/-- `(J x)_k = conj (x_{−k})`. -/
def jEll (x : Ell2) : Ell2 :=
  ⟨fun k => conj (x (-k)), by
    apply memℓp_gen
    rw [two_toReal]
    simp only [Real.rpow_two]
    exact summable_jFun x⟩

@[simp] theorem jEll_apply (x : Ell2) (k : ℤ) : jEll x k = conj (x (-k)) := rfl

theorem norm_jEll (x : Ell2) : ‖jEll x‖ = ‖x‖ := by
  have h1 := norm_sq_eq_tsum (jEll x)
  have e : ∑' k, ‖jEll x k‖ ^ 2 = ∑' k, ‖x k‖ ^ 2 := by
    rw [show (fun k => ‖jEll x k‖ ^ 2) = fun k => ‖x (-k)‖ ^ 2 from funext fun k => by simp]
    exact (Equiv.neg ℤ).tsum_eq (fun k => ‖x k‖ ^ 2)
  rw [e, ← norm_sq_eq_tsum x] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- The `H^s` complexified conjugation on the auxiliary construction's model. -/
def ellConj : Conj Ell2 where
  J :=
    { toFun := jEll
      map_add' := fun x y => by
        ext k
        simp
      map_smul' := fun c x => by
        ext k
        simp }
  invol := fun x => by
    ext k
    simp
  norm_eq := norm_jEll

theorem ellConj_apply (x : Ell2) : ellConj.J x = jEll x := rfl

/-! ### The diagonal weight division -/

theorem pw_neg (L s : ℝ) (k : ℤ) : pw L s (-k) = pw L s k := by
  simp [pw, freq, neg_div]

theorem norm_div_pw_le (L s : ℝ) (hs : 0 ≤ s) (w : ℂ) (k : ℤ) : ‖w / ((pw L s k : ℝ) : ℂ)‖ ≤ ‖w‖ := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (pw_pos L s k).le]
  exact div_le_self (norm_nonneg _) (by
    unfold pw
    exact Real.one_le_rpow (by linarith [abs_nonneg (freq L k)]) hs)

/-- `x ↦ (x_k / pw_k)_k`. -/
def divEll (L s : ℝ) (hs : 0 ≤ s) (x : Ell2) : Ell2 :=
  ⟨fun k => x k / ((pw L s k : ℝ) : ℂ), by
    apply memℓp_gen
    rw [two_toReal]
    simp only [Real.rpow_two]
    exact (summable_sq x).of_nonneg_of_le (fun k => by positivity)
      (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_div_pw_le L s hs (x k) k) 2)⟩

@[simp] theorem divEll_apply (L s : ℝ) (hs : 0 ≤ s) (x : Ell2) (k : ℤ) :
    divEll L s hs x k = x k / ((pw L s k : ℝ) : ℂ) := rfl

def divW (L s : ℝ) (hs : 0 ≤ s) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := divEll L s hs
      map_add' := fun x y => by
        ext k
        simp [add_div]
      map_smul' := fun c x => by
        ext k
        simp [mul_div_assoc] }
    1 (fun x => norm_le_of_pointwise zero_le_one fun k => by
      rw [one_mul]
      exact norm_div_pw_le L s hs (x k) k)

/-! ### Orthonormal report modes in `L²(𝕋_L)` -/

variable (L : ℝ) [Fact (0 < L)]

/-- `e_n = L^{-1/2} exp(2πinx/L)` as a continuous function. -/
def modeC (n : ℤ) : C(AddCircle L, ℂ) := (((Real.sqrt L)⁻¹ : ℝ) : ℂ) • fourier n

/-- `e_n` in `L²(𝕋_L)` (mass-`L` measure). -/
def eL (n : ℤ) : L2T L := ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ (modeC L n)

theorem eL_ae (n : ℤ) : (eL L n : AddCircle L → ℂ) =ᵐ[volume] Fourier.mode L n :=
  (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (μ := (volume : Measure (AddCircle L))) (modeC L n)).trans
    (Filter.Eventually.of_forall fun _ => rfl)

theorem inner_eL (u : L2T L) (n : ℤ) : inner ℂ (eL L n) u = Fourier.coeff L u n := by
  rw [MeasureTheory.L2.inner_def]
  unfold Fourier.coeff
  refine integral_congr_ae ?_
  filter_upwards [eL_ae L n] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

theorem orthonormal_eL : Orthonormal ℂ (eL L) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [inner_eL, Fourier.coeff_congr_ae L (eL_ae L n) m, Fourier.coeff_mode]

/-! ### The field map -/

/-- **The field map** `x ↦ Σ_k (x_k / pw_k) e_k` from the auxiliary construction's `H^s` model to `L²(𝕋_L)`. -/
def fieldMap (s : ℝ) (hs : 0 ≤ s) : Ell2 →L[ℂ] L2T L :=
  ((orthonormal_eL L).orthogonalFamily.linearIsometry).toContinuousLinearMap.comp (divW L s hs)

theorem hasSum_fieldMap (s : ℝ) (hs : 0 ≤ s) (x : Ell2) :
    HasSum (fun k => (x k / ((pw L s k : ℝ) : ℂ)) • eL L k) (fieldMap L s hs x) :=
  (orthonormal_eL L).orthogonalFamily.hasSum_linearIsometry (divEll L s hs x)

theorem norm_fieldMap_le (s : ℝ) (hs : 0 ≤ s) : ‖fieldMap L s hs‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  show ‖(orthonormal_eL L).orthogonalFamily.linearIsometry (divW L s hs x)‖ ≤ 1 * ‖x‖
  rw [LinearIsometry.norm_map]
  exact (divW L s hs).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ zero_le_one _) x

/-- The report Fourier coefficients of `fieldMap x` are the auxiliary construction's `toField L s x`. -/
theorem coeff_fieldMap (s : ℝ) (hs : 0 ≤ s) (x : Ell2) (n : ℤ) :
    Fourier.coeff L (fieldMap L s hs x) n = toField L s x n := by
  rw [← inner_eL]
  have h := (innerSL ℂ (eL L n)).hasSum (hasSum_fieldMap L s hs x)
  simp only [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.1 (orthonormal_eL L) n,
    mul_ite, mul_one, mul_zero] at h
  refine h.unique ?_
  have e : toField L s x n = x n / ((pw L s n : ℝ) : ℂ) := rfl
  rw [e]
  convert hasSum_ite_eq n (x n / ((pw L s n : ℝ) : ℂ)) using 1
  funext k
  by_cases hk : n = k
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

theorem star_eL (n : ℤ) : star (eL L n) = eL L (-n) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (eL L n), eL_ae L n, eL_ae L (-n)] with x h1 h2 h3
  rw [h1, Pi.star_apply, h2, h3]
  simp [Fourier.mode]

/-- Pointwise conjugation on `L²(𝕋_L)` as a bounded conjugate-linear map. -/
def starL : L2T L →L⋆[ℂ] L2T L :=
  LinearMap.mkContinuous (starConj (L := L)).J 1 fun f => by
    rw [one_mul]
    exact ((starConj (L := L)).norm_eq f).le

/-- **The `H^s` conjugation is the pointwise conjugation**: `fieldMap (J x) = star (fieldMap x)`. -/
theorem fieldMap_jEll (s : ℝ) (hs : 0 ≤ s) (x : Ell2) : fieldMap L s hs (jEll x) = star (fieldMap L s hs x) := by
  have h1 := (starL L).hasSum (hasSum_fieldMap L s hs x)
  have h2 : HasSum (fun k => (conj (x (-k)) / ((pw L s k : ℝ) : ℂ)) • eL L k) (star (fieldMap L s hs x)) := by
    have h3 := (Equiv.neg ℤ).hasSum_iff.2 h1
    refine h3.congr_fun fun k => ?_
    show (conj (x (-k)) / ((pw L s k : ℝ) : ℂ)) • eL L k =
      star ((x (-k) / ((pw L s (-k) : ℝ) : ℂ)) • eL L (-k))
    rw [star_smul', star_eL, neg_neg, map_div₀, Complex.conj_ofReal, pw_neg]
  exact (hasSum_fieldMap L s hs (jEll x)).unique (by simpa using h2)

/-! ### The discriminant in the auxiliary construction's coordinates -/

/-- The bounded complex-linear map `(x, y, z) ↦ (fieldMap x, fieldMap y, z)`. -/
def fieldTriple (s : ℝ) (hs : 0 ≤ s) : Ell2 × Ell2 × ℂ →L[ℂ] L2T L × L2T L × ℂ :=
  ((fieldMap L s hs).comp (ContinuousLinearMap.fst ℂ Ell2 (Ell2 × ℂ))).prod
    (((fieldMap L s hs).comp ((ContinuousLinearMap.fst ℂ Ell2 ℂ).comp (ContinuousLinearMap.snd ℂ Ell2 (Ell2 × ℂ)))).prod
      ((ContinuousLinearMap.snd ℂ Ell2 ℂ).comp (ContinuousLinearMap.snd ℂ Ell2 (Ell2 × ℂ))))

/-- **Holomorphy of the discriminant in the auxiliary construction's `H^s` coordinates**, jointly in `(x, y, z)`, everywhere. -/
theorem cxDisc_field_analytic (s : ℝ) (hs : 0 ≤ s) (κ : ℝ) :
    AnalyticOnNhd ℂ (fun p : Ell2 × Ell2 × ℂ =>
      cxDisc κ (fieldMap L s hs p.1) (fieldMap L s hs p.2.1) p.2.2) univ := fun p _ => by
  change AnalyticAt ℂ ((fun q : L2T L × L2T L × ℂ => cxDisc κ q.1 q.2.1 q.2.2) ∘ fieldTriple L s hs) p
  exact (analyticOnNhd_cxDisc κ _ (mem_univ _)).comp ((fieldTriple L s hs).analyticAt p)

/-- **Real slice** `y = J x`: the extension equals the physical discriminant of the field `fieldMap x`. -/
theorem cxDisc_field_real (s : ℝ) (hs : 0 ≤ s) (κ : ℝ) (x : Ell2) (z : ℂ) :
    cxDisc κ (fieldMap L s hs x) (fieldMap L s hs (jEll x)) z =
      L2SpatialTransfer.discriminant κ (fieldMap L s hs x) z := by
  rw [fieldMap_jEll]
  exact cxDisc_star κ _ z

/-- **Importable packaging for the auxiliary construction's `RiccatiFloquet`.** Near any `p₀ = (x₀, y₀, z₀) ∈ Ell2 × Ell2 × ℂ`
(in particular `(φ₀, J φ₀, z₀)`) and for any radius `r`, the map `(x, y, z) ↦ cxDisc κ (fieldMap x) (fieldMap y) z`
is complex differentiable and complex analytic on `B(p₀, r)`, bounded there by one constant, and on the real slice
`y = J x` equals the physical discriminant of `fieldMap x`, whose report coefficients are `toField L s x`. -/
theorem cxDisc_field_local (s : ℝ) (hs : 0 ≤ s) (κ : ℝ) (p₀ : Ell2 × Ell2 × ℂ) (r : ℝ) :
    ∃ M : ℝ,
      DifferentiableOn ℂ (fun p : Ell2 × Ell2 × ℂ =>
        cxDisc κ (fieldMap L s hs p.1) (fieldMap L s hs p.2.1) p.2.2) (ball p₀ r) ∧
      AnalyticOnNhd ℂ (fun p : Ell2 × Ell2 × ℂ =>
        cxDisc κ (fieldMap L s hs p.1) (fieldMap L s hs p.2.1) p.2.2) (ball p₀ r) ∧
      (∀ p ∈ ball p₀ r, ‖cxDisc κ (fieldMap L s hs p.1) (fieldMap L s hs p.2.1) p.2.2‖ ≤ M) ∧
      (∀ (x : Ell2) (z : ℂ), cxDisc κ (fieldMap L s hs x) (fieldMap L s hs (jEll x)) z =
        L2SpatialTransfer.discriminant κ (fieldMap L s hs x) z) ∧
      (∀ (x : Ell2) (n : ℤ), Fourier.coeff L (fieldMap L s hs x) n = toField L s x n) := by
  obtain ⟨C, B, hC, hB, hbd⟩ := cxDisc_bound (L := L) κ
  have han := cxDisc_field_analytic L s hs κ
  refine ⟨C * Real.exp (B * (‖fieldTriple L s hs‖ * (‖p₀‖ + r))), han.differentiableOn.mono (subset_univ _),
    han.mono (subset_univ _), fun p hp => ?_, cxDisc_field_real L s hs κ, coeff_fieldMap L s hs⟩
  have h1 : ‖p‖ ≤ ‖p₀‖ + r := by
    have := norm_sub_norm_le p p₀
    linarith [mem_ball_iff_norm.1 hp]
  have h2 : ‖fieldTriple L s hs p‖ ≤ ‖fieldTriple L s hs‖ * (‖p₀‖ + r) :=
    ((fieldTriple L s hs).le_opNorm p).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  exact (hbd (fieldTriple L s hs p)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hB)) hC)

end QuantumNLS.ComplexifiedSobolevField

#print axioms QuantumNLS.ComplexifiedSobolevField.ellConj
#print axioms QuantumNLS.ComplexifiedSobolevField.orthonormal_eL
#print axioms QuantumNLS.ComplexifiedSobolevField.coeff_fieldMap
#print axioms QuantumNLS.ComplexifiedSobolevField.fieldMap_jEll
#print axioms QuantumNLS.ComplexifiedSobolevField.cxDisc_field_analytic
#print axioms QuantumNLS.ComplexifiedSobolevField.cxDisc_field_real
#print axioms QuantumNLS.ComplexifiedSobolevField.cxDisc_field_local
