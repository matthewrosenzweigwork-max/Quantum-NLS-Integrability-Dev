import QuantumNLS.ProductTorusRealAverage
import QuantumNLS.ProductTorusAnalytic

/-!
# R-4C2E4AC7, stage T9b (CONDITIONAL on the held GP-04 clause): `ᾱ` is real analytic in the full dual norm

Source: `chapters/global/product_torus.tex`, theorem ("defines a real-analytic bounded one-form, with analyticity in
the full dual norm") and "Averaging the primitive" ("On the common complex initial ball just proved, the holomorphic
continuation of the real-bilinear expression defining `α` and of `T_θ` is uniformly bounded, as are the required
derivatives. Its Taylor coefficients can be integrated against Haar measure after evaluation on fixed tangent vectors.
The Cauchy coefficient bounds are uniform in `θ` and in unit tangent vectors, so these integrals define bounded
multilinear coefficients with a norm-convergent Taylor series on a smaller ball.").

Real route: the uniform Taylor majorant of the maps `T_ψ` at `u` (T6 `act_uniform_analytic`, conditional on
`HeldGP04AnalyticInitialDependence`) gives, through the Leibniz bound for the bilinear expression
`z ↦ α_{T_ψ z}(DT_ψ(z)·)` (mathlib `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`) and
`‖D^n T_ψ(u)‖ ≤ n! ‖p_ψ n‖` (T9a), a majorant of its canonical coefficients on the radius `r/4`, uniform in `ψ`;
T9a `real_covector_average` then gives the dual-norm power series of `ᾱ` at `u`. The GP-05 holomorphic-to-analytic
bridge is not used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace QuantumNLS.ProductTorusPrimitiveAnalytic

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusAction
  QuantumNLS.ProductTorusPrimitive QuantumNLS.ProductTorusAnalytic QuantumNLS.ProductTorusRealAverage
open QuantumNLS.Ext025B6TorusCoordinates (Torus)
open QuantumNLS.Ext025BHaar (productCircleHaar)

/-- The Leibniz-sum bound used for the canonical coefficients. -/
theorem leibniz_sum_bound {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s) (n : ℕ) (a : ℕ → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha : ∀ i, a i ≤ i.factorial * (C * s ^ i)) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * a (n - i + 1) ≤
      n.factorial * (((n : ℝ) + 1) * ((n : ℝ) + 1)) * (C ^ 2 * s ^ (n + 1)) := by
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * a (n - i + 1) ≤
      n.factorial * ((n : ℝ) + 1) * (C ^ 2 * s ^ (n + 1)) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : (n.choose i : ℝ) * i.factorial * (n - i).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
    have hid : (n.choose i : ℝ) * i.factorial * (n - i + 1).factorial =
        n.factorial * (((n - i : ℕ) : ℝ) + 1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, ← h1]
      push_cast
      ring
    have hpow : s ^ i * s ^ (n - i + 1) = s ^ (n + 1) := by
      rw [← pow_add, show i + (n - i + 1) = n + 1 by omega]
    have hle : (((n - i : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have : ((n - i : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n i
      linarith
    calc (n.choose i : ℝ) * a i * a (n - i + 1)
        ≤ (n.choose i : ℝ) * (i.factorial * (C * s ^ i)) * ((n - i + 1).factorial * (C * s ^ (n - i + 1))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (ha i) (by positivity)) (ha _) (ha0 _) (by positivity)
      _ = ((n.choose i : ℝ) * i.factorial * (n - i + 1).factorial) * (C ^ 2 * (s ^ i * s ^ (n - i + 1))) := by
          ring
      _ = n.factorial * (((n - i : ℕ) : ℝ) + 1) * (C ^ 2 * s ^ (n + 1)) := by rw [hid, hpow]
      _ ≤ n.factorial * ((n : ℝ) + 1) * (C ^ 2 * s ^ (n + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hle (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem sq_succ_mul_quarter_pow_le (n : ℕ) : ((n : ℝ) + 1) * ((n : ℝ) + 1) * (1 / 4) ^ n ≤ 1 := by
  have h2 : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.succ_le_of_lt n.lt_two_pow_self
  have hq : ((n : ℝ) + 1) * (1 / 2) ^ n ≤ 1 := by
    calc ((n : ℝ) + 1) * (1 / 2) ^ n ≤ 2 ^ n * (1 / 2) ^ n := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have h4 : ((1 : ℝ) / 4) ^ n = (1 / 2) ^ n * (1 / 2) ^ n := by rw [← mul_pow]; norm_num
  rw [h4]
  have hq0 : 0 ≤ ((n : ℝ) + 1) * (1 / 2) ^ n := by positivity
  calc ((n : ℝ) + 1) * ((n : ℝ) + 1) * ((1 / 2) ^ n * (1 / 2) ^ n)
      = (((n : ℝ) + 1) * (1 / 2) ^ n) * (((n : ℝ) + 1) * (1 / 2) ^ n) := by ring
    _ ≤ 1 * 1 := mul_le_mul hq hq hq0 zero_le_one
    _ = 1 := one_mul 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- A bounded bilinear form with `α_a(b) = Jα a b / 2` (GP-06). -/
def Jα : E →L[ℝ] E →L[ℝ] ℝ := Classical.choose (alpha_eq_J (E := E))

theorem Jα_spec (a b : E) : alpha a b = Jα a b / 2 := Classical.choose_spec (alpha_eq_J (E := E)) a b

/-- `Bα y M = α_y(M ·)` as a bounded bilinear map. -/
def Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ) := (1 / 2 : ℝ) • ((ContinuousLinearMap.compL ℝ E E ℝ).comp Jα)

theorem Bα_apply (y : E) (M : E →L[ℝ] E) (h : E) : Bα y M h = alpha y (M h) := by
  rw [Jα_spec]
  simp [Bα]
  ring

/-- The covector family `z ↦ α_{T_ψ z}(DT_ψ(z) ·)`. -/
def covec (DI : E → (E →L[ℝ] L1 ℝ)) (ψ : Torus) (z : E) : E →L[ℝ] ℝ :=
  Bα (act DI ψ z) (fderiv ℝ (act DI ψ) z)

theorem covec_apply (ψ : Torus) (z w : E) : covec DI ψ z w = alpha (act DI ψ z) (fderiv ℝ (act DI ψ) z w) :=
  Bα_apply _ _ _

theorem covec_analytic {ψ : Torus} (hA : AnalyticOnNhd ℝ (act DI ψ) univ) : AnalyticOnNhd ℝ (covec DI ψ) univ :=
  fun z _ => (Bα.analyticAt_bilinear (act DI ψ z, fderiv ℝ (act DI ψ) z)).comp₂ (hA z (mem_univ z))
    (hA.fderiv z (mem_univ z))

/-- Uniform majorant of the canonical coefficients of the covector family on the radius `r/4`. -/
theorem covec_coeff_bound {ψ : Torus} (hA : AnalyticOnNhd ℝ (act DI ψ) univ) {u : E}
    {p : FormalMultilinearSeries ℝ E E} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hp : HasFPowerSeriesOnBall (act DI ψ) p u (ENNReal.ofReal r)) (hpC : ∀ n, ‖p n‖ * r ^ n ≤ C) (n : ℕ) :
    ‖rcoeff (covec DI ψ) u n‖ * (r / 4) ^ n ≤ ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ * C ^ 2 * r⁻¹ := by
  set a : ℕ → ℝ := fun i => ‖iteratedFDeriv ℝ i (act DI ψ) u‖ with ha_def
  have ha : ∀ i, a i ≤ i.factorial * (C * r⁻¹ ^ i) := by
    intro i
    refine (norm_iteratedFDeriv_le_of_series hp i).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact hpC i
  have hL := (Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ)).norm_iteratedFDeriv_le_of_bilinear
    (f := act DI ψ) (g := fderiv ℝ (act DI ψ)) (N := ⊤) hA.contDiff hA.fderiv.contDiff u (n := n) le_top
  have hcov : covec DI ψ = fun y => Bα (act DI ψ y) (fderiv ℝ (act DI ψ) y) := rfl
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (act DI ψ) u‖ *
      ‖iteratedFDeriv ℝ (n - i) (fderiv ℝ (act DI ψ)) u‖ =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * a (n - i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_iteratedFDeriv_fderiv]
  have hLb := leibniz_sum_bound hC (inv_nonneg.2 hr.le) n a (fun i => norm_nonneg _) ha
  have hnD : ‖iteratedFDeriv ℝ n (covec DI ψ) u‖ ≤
      ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ *
        (n.factorial * (((n : ℝ) + 1) * ((n : ℝ) + 1)) * (C ^ 2 * r⁻¹ ^ (n + 1))) := by
    rw [hcov]
    exact hL.trans (mul_le_mul_of_nonneg_left (hsum ▸ hLb) (norm_nonneg _))
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hc : ‖rcoeff (covec DI ψ) u n‖ ≤
      ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ * (((n : ℝ) + 1) * ((n : ℝ) + 1)) * (C ^ 2 * r⁻¹ ^ (n + 1)) := by
    rw [rcoeff, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_le_iff₀ hf]
    calc ‖iteratedFDeriv ℝ n (covec DI ψ) u‖ ≤ _ := hnD
      _ = n.factorial * (‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ *
          (((n : ℝ) + 1) * ((n : ℝ) + 1)) * (C ^ 2 * r⁻¹ ^ (n + 1))) := by ring
  have hkey : r⁻¹ ^ (n + 1) * (r / 4) ^ n = r⁻¹ * (1 / 4) ^ n := by
    rw [pow_succ', div_eq_mul_one_div r 4, mul_pow]
    have : r⁻¹ ^ n * r ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    calc r⁻¹ * r⁻¹ ^ n * (r ^ n * (1 / 4) ^ n) = r⁻¹ * (r⁻¹ ^ n * r ^ n) * (1 / 4) ^ n := by ring
      _ = r⁻¹ * (1 / 4) ^ n := by rw [this, mul_one]
  have hq := sq_succ_mul_quarter_pow_le n
  calc ‖rcoeff (covec DI ψ) u n‖ * (r / 4) ^ n
      ≤ ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ * (((n : ℝ) + 1) * ((n : ℝ) + 1)) *
          (C ^ 2 * r⁻¹ ^ (n + 1)) * (r / 4) ^ n := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ * C ^ 2 * r⁻¹ *
          ((((n : ℝ) + 1) * ((n : ℝ) + 1)) * (1 / 4) ^ n) := by
        rw [mul_assoc _ (C ^ 2 * r⁻¹ ^ (n + 1)), mul_assoc (C ^ 2), hkey]
        ring
    _ ≤ ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ * C ^ 2 * r⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := mul_one _

/-- **`ᾱ` is real analytic in the full dual norm at every point** (conditional on the held GP-04 clause). -/
theorem alphaBar_analyticAt (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (u : E) :
    AnalyticAt ℝ (alphaBarCLM H) u := by
  obtain ⟨r, hr, C, hP⟩ := act_uniform_analytic H hDI hGP04 u
  have hA : ∀ ψ, AnalyticOnNhd ℝ (act DI ψ) univ := fun ψ z _ => act_analyticAt H hDI hGP04 ψ z
  have hC : 0 ≤ C := by
    obtain ⟨p, -, hp⟩ := hP 1
    have := hp 0
    rw [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hbound : ∀ ψ n, ‖rcoeff (covec DI ψ) u n‖ * (r / 4) ^ n ≤
      ‖(Bα : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ))‖ * C ^ 2 * r⁻¹ := by
    intro ψ n
    obtain ⟨p, hp, hpC⟩ := hP ψ
    exact covec_coeff_bound (hA ψ) hr hC hp hpC n
  obtain ⟨q, hq⟩ := real_covector_average productCircleHaar (covec DI) (alphaBarCLM H) u (r := r / 4)
    (by positivity) (by positivity) (fun ψ => (covec_analytic (hA ψ)).mono (subset_univ _))
    (fun z _ w => by
      have : (fun ψ => covec DI ψ z w) = fun ψ => alpha (act DI ψ z) (fderiv ℝ (act DI ψ) z w) :=
        funext fun ψ => covec_apply ψ z w
      rw [this]
      exact (continuous_integrand H z w).measurable)
    hbound
    (fun z _ w => by
      rw [alphaBarCLM_apply]
      unfold alphaBar
      exact integral_congr_ae (Eventually.of_forall fun ψ => (covec_apply ψ z w).symm))
  exact hq.analyticAt

/-- **`ᾱ` is a real-analytic one-form in the full dual norm** (conditional on the held GP-04 clause). -/
theorem alphaBar_analytic (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) : AnalyticOnNhd ℝ (alphaBarCLM H) univ :=
  fun u _ => alphaBar_analyticAt H hDI hGP04 u

end QuantumNLS.ProductTorusPrimitiveAnalytic

#print axioms QuantumNLS.ProductTorusPrimitiveAnalytic.leibniz_sum_bound
#print axioms QuantumNLS.ProductTorusPrimitiveAnalytic.covec_coeff_bound
#print axioms QuantumNLS.ProductTorusPrimitiveAnalytic.alphaBar_analyticAt
#print axioms QuantumNLS.ProductTorusPrimitiveAnalytic.alphaBar_analytic
