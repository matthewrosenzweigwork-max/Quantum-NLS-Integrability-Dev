import Mathlib
import QuantumNLS.Local003Neumann
import QuantumNLS.Local003Taylor

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage H2b: the complexified reduced map.

On the open ball `‖X‖ < 1/3` of the complex Banach algebra `𝒜 = C(Γ_n, B(H_σ))` we define (all complex-analytic in `X`)
`Pn X = (2πi)⁻¹∮ F0 (1-X)⁻¹`, `Dn X = (2πi)⁻¹∮ (z-p_n) F0 (1-X)⁻¹`, `Sn X = (E* Pn X E)^{-1/2}`,
`Bn X = Sn X · E*(Pn X Dn X Pn X)E · Sn X`, and the entry `bn X = (Bn X e₀)₁`.  We prove (uniformly in `n`, given
`‖F0‖ ≤ 1/r` and `Jclm F0 = E E*`):
* `analytic_bn`: `bn` is `AnalyticOnNhd ℂ` on `ball 0 (1/3)` ("bounded on a common complex ball");
* `bound_bn`: `‖bn X‖ ≤ 27 r / 2` there, a bound independent of `n`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Holo
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local003Analytic QuantumNLS.Local003Neumann

variable {L r : ℝ}

/-- The weight `z ↦ (z - p_n)·1` as an element of the algebra. -/
def wA (L : ℝ) (n : ℤ) (r : ℝ) : Alg L (center L n) r :=
  ⟨fun z => ((z : ℂ) - center L n) • (1 : H2 L →L[ℂ] H2 L),
    (continuous_subtype_val.sub continuous_const).smul continuous_const⟩

section Defs
variable (L) (n : ℤ) (hr : 0 < r) (F0 : Alg L (center L n) r)

def Pn (X : Alg L (center L n) r) : H2 L →L[ℂ] H2 L :=
  Jclm L (center L n) hr (F0 * Ring.inverse (1 - X))

def Dn (X : Alg L (center L n) r) : H2 L →L[ℂ] H2 L :=
  Jclm L (center L n) hr (wA L n r * (F0 * Ring.inverse (1 - X)))

def Sn (X : Alg L (center L n) r) : E2 →L[ℂ] E2 := invSqrtM (Fm L n (Pn L n hr F0 X))

def Bn (X : Alg L (center L n) r) : E2 →L[ℂ] E2 :=
  Sn L n hr F0 X * Fm L n (Pn L n hr F0 X * Dn L n hr F0 X * Pn L n hr F0 X) * Sn L n hr F0 X

def bn (X : Alg L (center L n) r) : ℂ := (Bn L n hr F0 X (vec2 1 0)) 1

end Defs

/-! ### Norm estimates -/

lemma norm_one_alg_le {c : ℂ} : ‖(1 : Alg L c r)‖ ≤ 1 := by
  refine (ContinuousMap.norm_le _ zero_le_one).2 fun z => ?_
  show ‖(1 : H2 L →L[ℂ] H2 L)‖ ≤ 1
  exact ContinuousLinearMap.norm_id_le

lemma norm_inv_le {c : ℂ} {X : Alg L c r} (h : ‖X‖ < 1) : ‖Ring.inverse (1 - X)‖ ≤ (1 - ‖X‖)⁻¹ := by
  rw [← geom_series_eq_inverse X h]
  have := tsum_geometric_le_of_norm_lt_one X h
  have h1 := norm_one_alg_le (L := L) (r := r) (c := c)
  linarith

lemma inv_sub_one {c : ℂ} {X : Alg L c r} (h : ‖X‖ < 1) :
    Ring.inverse (1 - X) - 1 = X * Ring.inverse (1 - X) := by
  have hu : (1 - X) * Ring.inverse (1 - X) = 1 := by
    rw [← geom_series_eq_inverse X h]
    exact mul_neg_geom_series X h
  have e : X * Ring.inverse (1 - X) = Ring.inverse (1 - X) - (1 - X) * Ring.inverse (1 - X) := by
    ext z : 1
    simp [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply, sub_mul]
  rw [e, hu]

lemma norm_wA_le (n : ℤ) (hr : 0 < r) : ‖wA L n r‖ ≤ r := by
  refine (ContinuousMap.norm_le _ hr.le).2 fun z => ?_
  show ‖((z : ℂ) - center L n) • (1 : H2 L →L[ℂ] H2 L)‖ ≤ r
  rw [norm_smul]
  have hz : ‖(z : ℂ) - center L n‖ = r := mem_sphere_iff_norm.mp z.2
  rw [hz]
  have h1 : ‖(1 : H2 L →L[ℂ] H2 L)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc r * ‖(1 : H2 L →L[ℂ] H2 L)‖ ≤ r * 1 := by gcongr
    _ = r := mul_one r

lemma norm_embed_le (hL : 0 < L) (n : ℤ) : ‖embed L n‖ ≤ 1 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (embed L n)
  rw [adjoint_embed_comp_embed hL n] at h
  have h1 : ‖ContinuousLinearMap.id ℂ E2‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (embed L n)]

lemma norm_Fm_le (hL : 0 < L) (n : ℤ) (Y : H2 L →L[ℂ] H2 L) : ‖Fm L n Y‖ ≤ ‖Y‖ := by
  have hE := norm_embed_le hL n
  have hA : ‖ContinuousLinearMap.adjoint (embed L n)‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact hE
  show ‖ContinuousLinearMap.adjoint (embed L n) ∘L (Y ∘L embed L n)‖ ≤ ‖Y‖
  calc ‖ContinuousLinearMap.adjoint (embed L n) ∘L (Y ∘L embed L n)‖
      ≤ ‖ContinuousLinearMap.adjoint (embed L n)‖ * ‖Y ∘L embed L n‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖Y‖ * ‖embed L n‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖Y‖ * 1) := by gcongr
    _ = ‖Y‖ := by ring

lemma norm_invSqrtM_le {T : E2 →L[ℂ] E2} (h : ‖T - 1‖ ≤ 1 / 2) : ‖invSqrtM T‖ ≤ 2 := by
  have hq : ‖T - 1‖ < 1 := by linarith
  have hn := QuantumNLS.Local003InvSqrt.summable_norm_invSqrtM hq
  have hgeom : HasSum (fun k : ℕ => ‖T - 1‖ ^ k) (1 - ‖T - 1‖)⁻¹ :=
    hasSum_geometric_of_lt_one (norm_nonneg _) hq
  have := tsum_of_norm_bounded hgeom (f := fun k : ℕ => (invSqrtCoeff k : ℂ) • (T - 1) ^ k) (fun k => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |invSqrtCoeff k| * ‖(T - 1) ^ k‖ ≤ 1 * ‖T - 1‖ ^ k :=
          mul_le_mul (abs_invSqrtCoeff_le k) (norm_pow_le _ _) (norm_nonneg _) zero_le_one
      _ = ‖T - 1‖ ^ k := one_mul _)
  have h2 : (1 - ‖T - 1‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  exact le_trans this h2

/-! ### Bounds on the ball `‖X‖ < 1/3` -/

section Bounds
variable (L) (n : ℤ) (hr : 0 < r) (F0 : Alg L (center L n) r) (hF0 : ‖F0‖ ≤ 1 / r)
  (hL : 0 < L) (hP0 : Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n))
include hr hF0

lemma norm_Rn_le {X : Alg L (center L n) r} (hX : ‖X‖ < 1 / 3) :
    ‖F0 * Ring.inverse (1 - X)‖ ≤ 1 / r * (3 / 2) := by
  have h1 : ‖X‖ < 1 := by linarith
  have hI := norm_inv_le (L := L) (r := r) h1
  have hI' : ‖Ring.inverse (1 - X)‖ ≤ 3 / 2 := by
    refine hI.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hr0 : 0 ≤ 1 / r := by positivity
  calc ‖F0 * Ring.inverse (1 - X)‖ ≤ ‖F0‖ * ‖Ring.inverse (1 - X)‖ := norm_mul_le F0 _
    _ ≤ 1 / r * (3 / 2) := by gcongr

lemma norm_Pn_le {X : Alg L (center L n) r} (hX : ‖X‖ < 1 / 3) : ‖Pn L n hr F0 X‖ ≤ 3 / 2 := by
  have h := Jfun_norm_le (L := L) hr (F0 * Ring.inverse (1 - X))
  have := norm_Rn_le L n hr F0 hF0 hX
  show ‖Jclm L (center L n) hr (F0 * Ring.inverse (1 - X))‖ ≤ 3 / 2
  rw [Jclm_apply]
  calc ‖Jfun (center L n) r (F0 * Ring.inverse (1 - X))‖ ≤ r * ‖F0 * Ring.inverse (1 - X)‖ := h
    _ ≤ r * (1 / r * (3 / 2)) := by gcongr
    _ = 3 / 2 := by field_simp

lemma norm_Dn_le {X : Alg L (center L n) r} (hX : ‖X‖ < 1 / 3) : ‖Dn L n hr F0 X‖ ≤ 3 * r / 2 := by
  have := norm_Rn_le L n hr F0 hF0 hX
  show ‖Jclm L (center L n) hr (wA L n r * (F0 * Ring.inverse (1 - X)))‖ ≤ 3 * r / 2
  rw [Jclm_apply]
  have h := Jfun_norm_le (L := L) hr (wA L n r * (F0 * Ring.inverse (1 - X)))
  have hw := norm_wA_le (L := L) n hr
  calc ‖Jfun (center L n) r (wA L n r * (F0 * Ring.inverse (1 - X)))‖
      ≤ r * ‖wA L n r * (F0 * Ring.inverse (1 - X))‖ := h
    _ ≤ r * (‖wA L n r‖ * ‖F0 * Ring.inverse (1 - X)‖) := by gcongr; exact norm_mul_le (wA L n r) (F0 * Ring.inverse (1 - X))
    _ ≤ r * (r * (1 / r * (3 / 2))) := by gcongr
    _ = 3 * r / 2 := by field_simp

include hL hP0

lemma norm_C_sub_one {X : Alg L (center L n) r} (hX : ‖X‖ < 1 / 3) :
    ‖Fm L n (Pn L n hr F0 X) - 1‖ ≤ 1 / 2 := by
  have h1 : ‖X‖ < 1 := by linarith
  have hE := adjoint_embed_comp_embed hL n
  have hFm0 : Fm L n (Jclm L (center L n) hr F0) = 1 := by
    rw [hP0]
    refine ContinuousLinearMap.ext fun v => ?_
    show ContinuousLinearMap.adjoint (embed L n) (embed L n (ContinuousLinearMap.adjoint (embed L n)
      (embed L n v))) = v
    have e : ∀ w, ContinuousLinearMap.adjoint (embed L n) (embed L n w) = w := fun w =>
      congrArg (fun T : E2 →L[ℂ] E2 => T w) hE
    rw [e, e]
  have hdiff : Fm L n (Pn L n hr F0 X) - 1 =
      Fm L n (Jclm L (center L n) hr (F0 * (X * Ring.inverse (1 - X)))) := by
    rw [← hFm0, ← map_sub]
    congr 1
    show Jclm L (center L n) hr (F0 * Ring.inverse (1 - X)) - Jclm L (center L n) hr F0 = _
    have e : F0 * Ring.inverse (1 - X) - F0 = F0 * (X * Ring.inverse (1 - X)) := by
      rw [← inv_sub_one h1]
      ext z : 1
      simp [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply, mul_sub]
    rw [← map_sub, e]
  rw [hdiff]
  refine (norm_Fm_le hL n _).trans ?_
  rw [Jclm_apply]
  refine (Jfun_norm_le (L := L) hr _).trans ?_
  have hI := norm_inv_le (L := L) (r := r) h1
  have hI' : ‖Ring.inverse (1 - X)‖ ≤ 3 / 2 := by
    refine hI.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc r * ‖F0 * (X * Ring.inverse (1 - X))‖
      ≤ r * (‖F0‖ * (‖X‖ * ‖Ring.inverse (1 - X)‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hr.le
        exact (norm_mul_le F0 (X * Ring.inverse (1 - X))).trans
          (mul_le_mul_of_nonneg_left (norm_mul_le X (Ring.inverse (1 - X))) (norm_nonneg F0))
    _ ≤ r * (1 / r * ((1 / 3) * (3 / 2))) := by gcongr
    _ = 1 / 2 := by field_simp

lemma bound_bn {X : Alg L (center L n) r} (hX : ‖X‖ < 1 / 3) : ‖bn L n hr F0 X‖ ≤ 27 * r / 2 := by
  have hC := norm_C_sub_one L n hr F0 hF0 hL hP0 hX
  have hS : ‖Sn L n hr F0 X‖ ≤ 2 := norm_invSqrtM_le hC
  have hP := norm_Pn_le L n hr F0 hF0 hX
  have hD := norm_Dn_le L n hr F0 hF0 hX
  have hr0 := hr
  have hFm := norm_Fm_le hL n (Pn L n hr F0 X * Dn L n hr F0 X * Pn L n hr F0 X)
  have hPDP : ‖Pn L n hr F0 X * Dn L n hr F0 X * Pn L n hr F0 X‖ ≤ 3 / 2 * (3 * r / 2) * (3 / 2) :=
    (norm_mul_le _ _).trans (by
      gcongr
      exact (norm_mul_le _ _).trans (by gcongr))
  have hB : ‖Bn L n hr F0 X‖ ≤ 2 * (3 / 2 * (3 * r / 2) * (3 / 2)) * 2 := by
    unfold Bn
    refine (norm_mul_le _ _).trans ?_
    calc ‖Sn L n hr F0 X * Fm L n _‖ * ‖Sn L n hr F0 X‖
        ≤ (‖Sn L n hr F0 X‖ * ‖Fm L n (Pn L n hr F0 X * Dn L n hr F0 X * Pn L n hr F0 X)‖) *
            ‖Sn L n hr F0 X‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ 2 * (3 / 2 * (3 * r / 2) * (3 / 2)) * 2 := by
          gcongr
          exact hFm.trans hPDP
  have he : ‖vec2 1 0‖ = 1 := by
    simp [vec2, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  calc ‖bn L n hr F0 X‖ = ‖(Bn L n hr F0 X (vec2 1 0)) 1‖ := rfl
    _ ≤ ‖Bn L n hr F0 X (vec2 1 0)‖ := by
        simpa using PiLp.norm_apply_le (Bn L n hr F0 X (vec2 1 0)) 1
    _ ≤ ‖Bn L n hr F0 X‖ * ‖vec2 1 0‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 * (3 / 2 * (3 * r / 2) * (3 / 2)) * 2 * 1 := by rw [he]; gcongr
    _ = 27 * r / 2 := by ring

end Bounds

/-! ### Analyticity -/

lemma analyticAt_Rn {c : ℂ} (F0 : Alg L c r) {X : Alg L c r} (h : ‖X‖ < 1) :
    AnalyticAt ℂ (fun Y : Alg L c r => F0 * Ring.inverse (1 - Y)) X := by
  have h1 : AnalyticAt ℂ (fun Y : Alg L c r => (1 : Alg L c r) - Y) X := analyticAt_const.sub analyticAt_id
  have h2 : AnalyticAt ℂ (Ring.inverse : Alg L c r → _) (1 - X) := by
    have := analyticAt_inverse (𝕜 := ℂ) (Units.oneSub X h)
    rwa [Units.val_oneSub] at this
  have h3 : AnalyticAt ℂ (fun Y : Alg L c r => Ring.inverse (1 - Y)) X :=
    AnalyticAt.comp (f := fun Y : Alg L c r => (1 : Alg L c r) - Y) (x := X) h2 h1
  exact AnalyticAt.mul (𝕜 := ℂ) (A := Alg L c r) analyticAt_const h3

section Analytic
variable (L) (n : ℤ) (hr : 0 < r) (F0 : Alg L (center L n) r) (hF0 : ‖F0‖ ≤ 1 / r)
  (hL : 0 < L) (hP0 : Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n))
include hF0 hL hP0

theorem analyticAt_bn {X : Alg L (center L n) r} (hX : ‖X‖ < 1 / 3) :
    AnalyticAt ℂ (bn L n hr F0) X := by
  have h1 : ‖X‖ < 1 := by linarith
  have hR := analyticAt_Rn F0 h1
  have hJ : AnalyticAt ℂ (⇑(Jclm L (center L n) hr)) ((fun Y : Alg L (center L n) r => F0 * Ring.inverse (1 - Y)) X) :=
    by first
      | exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (Jclm L (center L n) hr) _
      | apply ContinuousLinearMap.analyticAt
      | exact ((Jclm L (center L n) hr).restrictScalars ℂ).analyticAt _
  have hP : AnalyticAt ℂ (Pn L n hr F0) X :=
    AnalyticAt.comp (f := fun Y : Alg L (center L n) r => F0 * Ring.inverse (1 - Y)) hJ hR
  have h3 : AnalyticAt ℂ (fun Y : Alg L (center L n) r => wA L n r * (F0 * Ring.inverse (1 - Y))) X :=
    AnalyticAt.mul (𝕜 := ℂ) (A := Alg L (center L n) r) analyticAt_const hR
  have hJ2 : AnalyticAt ℂ (⇑(Jclm L (center L n) hr))
      ((fun Y : Alg L (center L n) r => wA L n r * (F0 * Ring.inverse (1 - Y))) X) :=
    by first
      | exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (Jclm L (center L n) hr) _
      | apply ContinuousLinearMap.analyticAt
      | exact ((Jclm L (center L n) hr).restrictScalars ℂ).analyticAt _
  have hD : AnalyticAt ℂ (Dn L n hr F0) X :=
    AnalyticAt.comp (f := fun Y : Alg L (center L n) r => wA L n r * (F0 * Ring.inverse (1 - Y))) hJ2 h3
  have hC : AnalyticAt ℂ (fun Y => Fm L n (Pn L n hr F0 Y)) X :=
    ((Fm L n).analyticAt (Pn L n hr F0 X)).comp hP
  have hCs := norm_C_sub_one L n hr F0 hF0 hL hP0 hX
  have hS : AnalyticAt ℂ (Sn L n hr F0) X := by
    have h1' : AnalyticAt ℂ (fun Y => Fm L n (Pn L n hr F0 Y) - 1) X := hC.sub analyticAt_const
    have h2 := invSqrt_analyticAt (T0 := Fm L n (Pn L n hr F0 X) - 1) (by linarith)
    exact AnalyticAt.comp (f := fun Y => Fm L n (Pn L n hr F0 Y) - 1) (x := X) h2 h1'
  have hQ : AnalyticAt ℂ (fun Y => Fm L n (Pn L n hr F0 Y * Dn L n hr F0 Y * Pn L n hr F0 Y)) X :=
    AnalyticAt.comp (f := fun Y => Pn L n hr F0 Y * Dn L n hr F0 Y * Pn L n hr F0 Y)
      ((Fm L n).analyticAt _) ((hP.mul hD).mul hP)
  have hB : AnalyticAt ℂ (Bn L n hr F0) X := (hS.mul hQ).mul hS
  let Λ : (E2 →L[ℂ] E2) →L[ℂ] ℂ :=
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ E2 (vec2 1 0))
  exact (Λ.analyticAt (Bn L n hr F0 X)).comp hB

end Analytic

end QuantumNLS.Local003Holo
#print axioms QuantumNLS.Local003Holo.bound_bn
#print axioms QuantumNLS.Local003Holo.analyticAt_bn
