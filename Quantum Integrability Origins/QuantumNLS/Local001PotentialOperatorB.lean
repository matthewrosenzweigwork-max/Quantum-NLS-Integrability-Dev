import QuantumNLS.Local001PotentialOutputB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

noncomputable def potentialResolventLinear {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) : VectorInterval L →ₗ[ℂ] VectorInterval L where
  toFun := potentialResolventOutput κ hκ hL n hr hsmall hz u
  map_add' f g := by
    apply Lp.ext
    have hleft := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u (f + g)
    have hrightf := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u f
    have hrightg := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u g
    have hsum := Lp.coeFn_add (potentialResolventOutput κ hκ hL n hr hsmall hz u f)
      (potentialResolventOutput κ hκ hL n hr hsmall hz u g)
    let R := LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z
    have hR : ∀ᵐ x ∂(LocalSpectral.μI L), R (f + g) x = R f x + R g x := by
      have hmap := congrArg (fun a : VectorInterval L => (a : ℝ → E2)) (map_add R f g)
      have hsumR := Lp.coeFn_add (R f) (R g)
      filter_upwards [hsumR] with x hx
      exact (congrFun hmap x).trans hx
    filter_upwards [hleft, hrightf, hrightg, hsum, hR] with x hleft hrightf hrightg hsum hR
    calc
      potentialResolventOutput κ hκ hL n hr hsmall hz u (f + g) x =
          potentialResolventFn κ u (R (f + g)) x := hleft
      _ = potentialPt κ (u x) (R f x + R g x) := by
          change potentialPt κ (u x) (R (f + g) x) = _
          rw [hR]
      _ = potentialResolventFn κ u (R f) x + potentialResolventFn κ u (R g) x := by
          exact potentialPt_add κ (u x) (R f x) (R g x)
      _ = (potentialResolventOutput κ hκ hL n hr hsmall hz u f +
            potentialResolventOutput κ hκ hL n hr hsmall hz u g) x := by
          rw [hsum, Pi.add_apply, hrightf, hrightg]
  map_smul' c f := by
    apply Lp.ext
    have hleft := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u (c • f)
    have hright := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u f
    have hsmul := Lp.coeFn_smul c
      (potentialResolventOutput κ hκ hL n hr hsmall hz u f)
    let R := LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z
    have hR : ∀ᵐ x ∂(LocalSpectral.μI L), R (c • f) x = c • R f x := by
      have hmap := congrArg (fun a : VectorInterval L => (a : ℝ → E2)) (map_smul R c f)
      have hsmulR := Lp.coeFn_smul c (R f)
      filter_upwards [hsmulR] with x hx
      exact (congrFun hmap x).trans hx
    filter_upwards [hleft, hright, hsmul, hR] with x hleft hright hsmul hR
    calc
      potentialResolventOutput κ hκ hL n hr hsmall hz u (c • f) x =
          potentialResolventFn κ u (R (c • f)) x := hleft
      _ = potentialPt κ (u x) (c • R f x) := by
          change potentialPt κ (u x) (R (c • f) x) = _
          rw [hR]
      _ = c • potentialResolventFn κ u (R f) x := potentialPt_smul κ (u x) c (R f x)
      _ = (c • potentialResolventOutput κ hκ hL n hr hsmall hz u f) x := by
          rw [hsmul, Pi.smul_apply, hright]

#print axioms potentialResolventLinear

theorem potentialResolventLinear_norm_le {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (f : VectorInterval L) :
    ‖potentialResolventLinear κ hκ hL n hr hsmall hz u f‖ ≤
      (2 * Real.sqrt κ * resolventConstant L r * ‖u‖) * ‖f‖ := by
  have hcoe := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u f
  have hbound := potentialResolventOutput_ae_bound κ hκ hL n hr hsmall hz u f
  have hnorm : ‖potentialResolventOutput κ hκ hL n hr hsmall hz u f‖ ≤
      (2 * Real.sqrt κ * resolventConstant L r * ‖f‖) * ‖u‖ := by
    exact Lp.norm_le_mul_norm_of_ae_le_mul hbound
  calc
    ‖potentialResolventLinear κ hκ hL n hr hsmall hz u f‖ =
        ‖potentialResolventOutput κ hκ hL n hr hsmall hz u f‖ := rfl
    _ ≤ (2 * Real.sqrt κ * resolventConstant L r * ‖f‖) * ‖u‖ := hnorm
    _ = (2 * Real.sqrt κ * resolventConstant L r * ‖u‖) * ‖f‖ := by ring


#print axioms potentialResolventLinear_norm_le

noncomputable def potentialResolvent {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) : VectorInterval L →L[ℂ] VectorInterval L :=
  (potentialResolventLinear κ hκ hL n hr hsmall hz u).mkContinuous
    (2 * Real.sqrt κ * resolventConstant L r * ‖u‖)
    (potentialResolventLinear_norm_le κ hκ hL n hr hsmall hz u)


#print axioms potentialResolvent

theorem potentialResolvent_norm_le {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) :
    ‖potentialResolvent κ hκ hL n hr hsmall hz u‖ ≤
      2 * Real.sqrt κ * resolventConstant L r * ‖u‖ := by
  have hC : 0 ≤ resolventConstant L r := Real.sqrt_nonneg _
  unfold potentialResolvent
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _


#print axioms potentialResolvent_norm_le

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
