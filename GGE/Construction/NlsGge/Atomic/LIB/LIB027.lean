import NlsGge.Atomic.IntervalZSAction

/-!
# LIB-027: the real-type Dirac Green boundary form

The shared action is an actual L2 pair, constructed after proving the potential
products are L2 using the H1 representative bounds. Its pairings use the
conjugate-first Hilbert inner product. Almost-everywhere real-type conjugacy
cancels the potential terms; scalar H1 integration by parts gives the exact
`-i` upper-minus-lower endpoint bracket. No endpoint relation is imposed here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace NlsGge.Atomic.LIB027
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

lemma sourceInterval_inner_eq_integral (f g : SourceIntervalL2) :
    inner ℂ f g = ∫ x in (0 : ℝ)..1, star (f x) * g x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

lemma sourcePair_inner_eq_integral (f g : SourcePairL2) :
    inner ℂ f g = ∫ x in (0 : ℝ)..1,
      star (f true x) * g true x + star (f false x) * g false x := by
  have hi (b : Bool) : IntervalIntegrable (fun x => star (f b x) * g b x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((Lp.memLp (f b)).star.integrable_mul (Lp.memLp (g b)))
  rw [PiLp.inner_apply, Fintype.sum_bool, sourceInterval_inner_eq_integral,
    sourceInterval_inner_eq_integral, intervalIntegral.integral_add (hi true) (hi false)]

lemma zs_action_left_pairing (φ : SourcePairL2) (f g : H1Pair) :
    inner ℂ (zsApply φ f) (h1PairValue g) =
      ∫ x in (0 : ℝ)..1,
        star (zsExpression φ (fun c x => (f c).value x) (fun c x => (f c).derivative x) true x) *
          (g true).value x +
        star (zsExpression φ (fun c x => (f c).value x) (fun c x => (f c).derivative x) false x) *
          (g false).value x := by
  rw [sourcePair_inner_eq_integral]
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le zero_le_one]
  filter_upwards [zsApply_ae φ f true, zsApply_ae φ f false] with x ht hf
  change star (zsApply φ f true x) * (g true).value x +
    star (zsApply φ f false x) * (g false).value x = _
  rw [ht, hf]

lemma zs_action_right_pairing (φ : SourcePairL2) (f g : H1Pair) :
    inner ℂ (h1PairValue f) (zsApply φ g) =
      ∫ x in (0 : ℝ)..1,
        star ((f true).value x) *
          zsExpression φ (fun c x => (g c).value x) (fun c x => (g c).derivative x) true x +
        star ((f false).value x) *
          zsExpression φ (fun c x => (g c).value x) (fun c x => (g c).derivative x) false x := by
  rw [sourcePair_inner_eq_integral]
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le zero_le_one]
  filter_upwards [zsApply_ae φ g true, zsApply_ae φ g false] with x ht hf
  change star ((f true).value x) * zsApply φ g true x +
    star ((f false).value x) * zsApply φ g false x = _
  rw [ht, hf]

/-- The exact Dirac Green identity on unrestricted interval H1 pairs. -/
theorem zs_green_identity {φ : SourcePairL2} (hφ : IsRealType φ) (f g : H1Pair) :
    inner ℂ (zsApply φ f) (h1PairValue g) - inner ℂ (h1PairValue f) (zsApply φ g) =
      zsBoundaryForm f g := by
  let F : Bool → ℝ → ℂ := fun b x => (f b).value x
  let G : Bool → ℝ → ℂ := fun b x => (g b).value x
  let dF : Bool → ℝ → ℂ := fun b x => (f b).derivative x
  let dG : Bool → ℝ → ℂ := fun b x => (g b).derivative x
  let Ef := zsExpression φ F dF
  let Eg := zsExpression φ G dG
  let D : Bool → ℝ → ℂ := fun b x => star (dF b x) * G b x + star (F b x) * dG b x
  have hLi : IntervalIntegrable
      (fun x => star (Ef true x) * G true x + star (Ef false x) * G false x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (((zsExpression_memLp φ f true).star.integrable_mul (Lp.memLp (g true).value)).add
        ((zsExpression_memLp φ f false).star.integrable_mul (Lp.memLp (g false).value)))
  have hRi : IntervalIntegrable
      (fun x => star (F true x) * Eg true x + star (F false x) * Eg false x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (((Lp.memLp (f true).value).star.integrable_mul (zsExpression_memLp φ g true)).add
        ((Lp.memLp (f false).value).star.integrable_mul (zsExpression_memLp φ g false)))
  have hD (b : Bool) : IntervalIntegrable (D b) volume 0 1 :=
    interval_h1_pairing_integrable (f b) (g b)
  have hreal : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), φ false x = star (φ true x) := by
    change φ false = star (φ true) at hφ
    filter_upwards [Lp.coeFn_star (φ true)] with x hx
    rw [hφ]
    exact hx
  have hpoint : (fun x =>
      (star (Ef true x) * G true x + star (Ef false x) * G false x) -
        (star (F true x) * Eg true x + star (F false x) * Eg false x)) =ᵐ[
          volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => -Complex.I * D true x + Complex.I * D false x) := by
    filter_upwards [hreal] with x hx
    dsimp [Ef, Eg, D, zsExpression]
    simp [hx]
    ring
  calc
    _ = (∫ x in (0 : ℝ)..1,
        (star (Ef true x) * G true x + star (Ef false x) * G false x) -
          (star (F true x) * Eg true x + star (F false x) * Eg false x)) := by
      rw [zs_action_left_pairing, zs_action_right_pairing,
        intervalIntegral.integral_sub hLi hRi]
    _ = (∫ x in (0 : ℝ)..1, -Complex.I * D true x + Complex.I * D false x) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simpa only [uIoc_of_le zero_le_one] using hpoint
    _ = -Complex.I * (∫ x in (0 : ℝ)..1, D true x) +
        Complex.I * (∫ x in (0 : ℝ)..1, D false x) := by
      rw [intervalIntegral.integral_add ((hD true).const_mul _) ((hD false).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = zsBoundaryForm f g := by
      change -Complex.I * (∫ x in (0 : ℝ)..1,
          star ((f true).derivative x) * (g true).value x +
            star ((f true).value x) * (g true).derivative x) +
        Complex.I * (∫ x in (0 : ℝ)..1,
          star ((f false).derivative x) * (g false).value x +
            star ((f false).value x) * (g false).derivative x) = _
      rw [interval_h1_integrationByParts (f true) (g true),
        interval_h1_integrationByParts (f false) (g false)]
      dsimp [zsBoundaryForm]
      ring

end NlsGge.Atomic.LIB027
