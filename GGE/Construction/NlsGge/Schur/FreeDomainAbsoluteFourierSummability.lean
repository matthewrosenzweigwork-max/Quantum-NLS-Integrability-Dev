import NlsGge.Schur.FreeDomainH1CoefficientSummability
import NlsGge.Schur.FourierMultiplier

/-! NEW-F02.02: actual proper free-domain coefficients are absolutely
summable in each reflected channel. The continuous Fourier series therefore
converges in the uniform norm, which is needed for genuine endpoint traces.
The weak-H1/domain equivalence remains to be proved. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace NlsGge.Schur

lemma freeDomain_component_absolute_summable (n : ℤ) (x : SectorSquare n)
    (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool) :
    Summable (fun m : Sector n => ‖x (upper,m)‖) := by
  let w : Sector n → ℝ := fun m => 1 + (m.val : ℝ) ^ 2
  have hw (m : Sector n) : 0 < w m := by dsimp [w]; positivity
  have hrec : Summable (fun m : Sector n => 1 / w m) :=
    NlsGge.Analysis.summable_reciprocal_bracket_square.subtype
      (fun p : ℤ => p % 2 = n % 2)
  have hfnorm (m : Sector n) :
      ‖(Real.sqrt (w m) : ℂ) * x (upper,m)‖ ^ 2 = w m * ‖x (upper,m)‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hw m).le]
  have hgnorm (m : Sector n) :
      ‖(Real.sqrt (1 / w m) : ℂ)‖ ^ 2 = 1 / w m := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity : 0 ≤ 1 / w m)]
  have hfmem : Memℓp (fun m : Sector n => (Real.sqrt (w m) : ℂ) * x (upper,m)) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hfnorm] using
      freeDomain_component_h1_coefficients_summable n x hx upper
  have hgmem : Memℓp (fun m : Sector n => (Real.sqrt (1 / w m) : ℂ)) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hgnorm] using hrec
  let f : lp (fun _ : Sector n => ℂ) 2 := ⟨_,hfmem⟩
  let g : lp (fun _ : Sector n => ℂ) 2 := ⟨_,hgmem⟩
  have hp (m : Sector n) : ‖f m‖ * ‖g m‖ = ‖x (upper,m)‖ := by
    change ‖(Real.sqrt (w m) : ℂ) * x (upper,m)‖ *
      ‖(Real.sqrt (1 / w m) : ℂ)‖ = _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : Real.sqrt (w m) * Real.sqrt (1 / w m) = 1 := by
      rw [← Real.sqrt_mul (hw m).le, mul_one_div_cancel (hw m).ne', Real.sqrt_one]
    calc
      _ = (Real.sqrt (w m) * Real.sqrt (1 / w m)) * ‖x (upper,m)‖ := by ring
      _ = _ := by rw [hs, one_mul]
  simpa only [hp] using lp.summable_mul
    (by rw [Real.holderConjugate_iff]; norm_num) f g

lemma freeDomain_component_continuous_fourier_summable
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    Summable (fun m : Sector n => x (upper,m) •
      fourier (T := (2 : ℝ)) (if upper then m.val else -m.val)) := by
  have hnorm (m : Sector n) :
      ‖x (upper,m) • (fourier (T := (2 : ℝ))
        (if upper then m.val else -m.val) : C(SpectralCircle, ℂ))‖ =
        ‖x (upper,m)‖ := by
    rw [norm_smul, fourier_norm, mul_one]
  have hs : Summable (fun m : Sector n =>
      ‖x (upper,m) • (fourier (T := (2 : ℝ))
        (if upper then m.val else -m.val) : C(SpectralCircle, ℂ))‖) := by
    simpa only [hnorm] using freeDomain_component_absolute_summable n x hx upper
  exact hs.of_norm

end NlsGge.Schur
