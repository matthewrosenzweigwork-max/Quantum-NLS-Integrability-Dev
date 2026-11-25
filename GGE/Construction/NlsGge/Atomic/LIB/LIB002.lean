import NlsGge.Atomic.LIB.LIB001
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open NlsGge.Atomic.LIB001
open scoped ContDiff

namespace NlsGge.Atomic.LIB002

/-- The multiplier for differentiation on a circle of length `T`, using
Mathlib's coefficient convention `fourierCoeff f n = ∫ fourier (-n) • f`. -/
def fourierMultiplier (T : ℝ) (n : ℤ) : ℂ :=
  2 * Real.pi * Complex.I * (n : ℂ) / T

/-- Smooth periodic real-line representatives of test functions on a circle.
The periodicity is part of the test data, so its endpoint condition is never
silently replaced by a condition on Fourier coefficients. -/
structure SmoothPeriodicTest (T : ℝ) where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  periodic : Function.Periodic toFun T

namespace SmoothPeriodicTest

private theorem periodic_deriv {T : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have hbase : HasDerivAt f (deriv f x) x :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hshiftAt : HasDerivAt f (deriv f (x + T)) (x + T) :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hshift : HasDerivAt (fun y => f (y + T))
      (deriv f (x + T)) x := hshiftAt.comp_add_const x T
  have hfun : (fun y => f (y + T)) = f := funext hper
  rw [hfun] at hshift
  exact hshift.unique hbase

private theorem contDiff_iteratedDeriv (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv m hf

theorem periodic_iteratedDeriv {T : ℝ} (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f T) (m : ℕ) :
    Function.Periodic (iteratedDeriv m f) T := by
  induction m with
  | zero => simpa using hper
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact periodic_deriv (contDiff_iteratedDeriv f hf m) ih

/-- The descended continuous function on `AddCircle T` represented by this
smooth periodic test. -/
def toContinuousMap {T : ℝ} [hT : Fact (0 < T)] (φ : SmoothPeriodicTest T) : C(AddCircle T, ℂ) where
  toFun := AddCircle.liftIoc T 0 φ.toFun
  continuous_toFun := AddCircle.liftIoc_zero_continuous
    (by simpa using (φ.periodic 0).symm)
    (φ.smooth.continuous.continuousOn)

/-- A smooth test, or any of its iterated derivatives, viewed in the actual
normalized-Haar `L²(AddCircle T)` carrier. -/
def toL2 {T : ℝ} [hT : Fact (0 < T)] (φ : SmoothPeriodicTest T) :
    Lp ℂ 2 (@AddCircle.haarAddCircle T hT) :=
  ContinuousMap.toLp 2 (@AddCircle.haarAddCircle T hT) ℂ φ.toContinuousMap

/-- Differentiating a smooth periodic test preserves both smoothness and its
actual period. -/
def iterated {T : ℝ} (φ : SmoothPeriodicTest T) (m : ℕ) : SmoothPeriodicTest T :=
  ⟨iteratedDeriv m φ.toFun,
    contDiff_iteratedDeriv φ.toFun φ.smooth m,
    periodic_iteratedDeriv φ.toFun φ.smooth φ.periodic m⟩

@[simp] theorem toContinuousMap_apply {T : ℝ} [hT : Fact (0 < T)] (φ : SmoothPeriodicTest T)
    (x : AddCircle T) : φ.toContinuousMap x = AddCircle.liftIoc T 0 φ.toFun x := rfl

end SmoothPeriodicTest

/-- The literal weak periodic derivative relation: testing against every
smooth periodic function on the circle gives the integration-by-parts
identity in the normalized-Haar `L²` pairing. -/
def HasWeakDerivativeL2 (T : ℝ) [hT : Fact (0 < T)] (m : ℕ)
    (u v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) : Prop :=
  ∀ φ : SmoothPeriodicTest T,
    @inner ℂ _ _ (SmoothPeriodicTest.toL2 (SmoothPeriodicTest.iterated φ m)) u =
      (-1 : ℂ) ^ m *
        @inner ℂ _ _ (SmoothPeriodicTest.toL2 φ) v

end NlsGge.Atomic.LIB002

namespace NlsGge.Atomic.LIB002

section ClassicalFourierDerivative

variable {T : ℝ}

/-- One integration-by-parts step on an arbitrary positive period. The `n = 0`
case is proved from the fundamental theorem of calculus rather than by dividing
by the frequency. -/
theorem fourierCoeffOn_deriv_of_smooth_periodic
    (hT : 0 < T) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f T) (n : ℤ) :
    fourierCoeffOn hT (deriv f) n =
      fourierMultiplier T n * fourierCoeffOn hT f n := by
  letI : Fact (0 < T) := ⟨hT⟩
  have hderiv : ∀ x, HasDerivAt f (deriv f x) x := by
    intro x
    exact ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hderivCont : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hderivInt : IntervalIntegrable (deriv f) volume 0 T :=
    hderivCont.intervalIntegrable 0 T
  have hendpoint : f T = f 0 := by
    simpa using hper 0
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
    have hFTC : ∫ x in (0 : ℝ)..T, deriv f x = f T - f 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hderivInt
    simp [hendpoint, hFTC, fourierMultiplier]
  · have hparts := fourierCoeffOn_of_hasDerivAt_Ioo hT hn
      (hf.continuous.continuousOn)
      (fun x _ => hderiv x)
      hderivInt
    rw [hendpoint] at hparts
    simp only [sub_self, mul_zero, zero_sub, one_mul, sub_zero] at hparts
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hden : (-2 * Real.pi * Complex.I * (n : ℂ)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hnC
    have hmul : fourierMultiplier T n =
        -(-2 * Real.pi * Complex.I * (n : ℂ)) / T := by
      simp [fourierMultiplier]
    have hidentity : fourierCoeffOn hT (deriv f) n =
        fourierMultiplier T n * fourierCoeffOn hT f n := by
      rw [hmul]
      field_simp [hden, hT.ne'] at hparts ⊢
      simpa [mul_comm, mul_left_comm, mul_assoc] using hparts.symm
    exact hidentity

/-- Iterating the classical identity retains the full arbitrary-period
normalization and includes the zero frequency. -/
theorem fourierCoeffOn_iteratedDeriv_of_smooth_periodic
    (hT : 0 < T) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f T) (m : ℕ) (n : ℤ) :
    fourierCoeffOn hT (iteratedDeriv m f) n =
      fourierMultiplier T n ^ m * fourierCoeffOn hT f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hsm : ContDiff ℝ ∞ (iteratedDeriv m f) := by
        rw [iteratedDeriv_eq_iterate]
        exact ContDiff.iterate_deriv m hf
      have hper' := SmoothPeriodicTest.periodic_iteratedDeriv f hf hper m
      rw [fourierCoeffOn_deriv_of_smooth_periodic hT _ hsm hper' n, ih]
      rw [pow_succ]
      ring

end ClassicalFourierDerivative
end NlsGge.Atomic.LIB002

namespace NlsGge.Atomic.LIB002

section FourierTests

variable {T : ℝ}

/-- The smooth periodic test represented by the `n`th Fourier character. -/
def fourierTest (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) : SmoothPeriodicTest T :=
  ⟨(fun x : ℝ => fourier n (x : AddCircle T)),
    by
      simp_rw [fourier_coe_apply]
      have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) :=
        Complex.ofRealCLM.contDiff
      have hlin : ContDiff ℝ ∞
          (fun x : ℝ => (2 * Real.pi * Complex.I * (n : ℂ) / T) * (x : ℂ)) :=
        contDiff_const.mul hcoe
      convert Complex.contDiff_exp.comp hlin using 1 <;> ext x <;> simp <;> ring,
    by
      intro x
      change fourier n ((x + T : ℝ) : AddCircle T) = fourier n (x : AddCircle T)
      rw [AddCircle.coe_add_period]⟩

/-- Iterated differentiation of a Fourier character is multiplication by the
corresponding power of its actual period-`T` frequency. -/
theorem iteratedDeriv_fourierTest (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) (m : ℕ) :
    iteratedDeriv m (fourierTest T n).toFun =
      fun x => fourierMultiplier T n ^ m * (fourierTest T n).toFun x := by
  induction m with
  | zero =>
      funext x
      simp
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hderiv := hasDerivAt_fourier (T := T) n x
      have hconst := hderiv.const_mul (fourierMultiplier T n ^ m)
      calc
        deriv (fun y : ℝ => fourierMultiplier T n ^ m * fourier n (y : AddCircle T)) x =
            fourierMultiplier T n ^ m *
              (fourierMultiplier T n * fourier n (x : AddCircle T)) := hconst.deriv
        _ = fourierMultiplier T n ^ (m + 1) * fourier n (x : AddCircle T) := by
          rw [pow_succ]
          ring

/-- The continuous descent of a Fourier test is exactly Mathlib's Fourier
character on the circle. -/
theorem fourierTest_toContinuousMap (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) :
    (fourierTest T n).toContinuousMap = fourier n := by
  ext x
  change AddCircle.liftIoc T 0 (fourierTest T n).toFun x = fourier n x
  let y := AddCircle.equivIoc T 0 x
  have hy : ((y : ℝ) : AddCircle T) = x := by simp [y]
  rw [← hy, AddCircle.liftIoc_coe_apply y.property]
  rfl

/-- The `L²` representative of a smooth periodic test has its classical
interval coefficient. -/
theorem fourierCoeff_toL2 (T : ℝ) [hT : Fact (0 < T)]
    (φ : SmoothPeriodicTest T) (n : ℤ) :
    fourierCoeff (SmoothPeriodicTest.toL2 φ) n =
      fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT.out) φ.toFun n := by
  change fourierCoeff (ContinuousMap.toLp 2 (@AddCircle.haarAddCircle T hT)
    ℂ φ.toContinuousMap) n = _
  rw [fourierCoeff_toLp]
  change fourierCoeff (AddCircle.liftIoc T 0 φ.toFun) n = _
  rw [fourierCoeff_liftIoc_eq]

/-- The character test is the corresponding vector of the actual Fourier
Hilbert basis. -/
theorem toL2_fourierTest (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) :
    SmoothPeriodicTest.toL2 (fourierTest T n) = fourierLp 2 n := by
  change ContinuousMap.toLp 2 (@AddCircle.haarAddCircle T hT) ℂ
      (fourierTest T n).toContinuousMap = _
  rw [fourierTest_toContinuousMap]

/-- The iterated character test is the expected scalar multiple in `L²`. -/
theorem toL2_iterated_fourierTest (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) (m : ℕ) :
    SmoothPeriodicTest.toL2 ((fourierTest T n).iterated m) =
      fourierMultiplier T n ^ m • fourierLp 2 n := by
  have hmap : ((fourierTest T n).iterated m).toContinuousMap =
      fourierMultiplier T n ^ m • (fourier n : C(AddCircle T, ℂ)) := by
    ext x
    change AddCircle.liftIoc T 0 ((fourierTest T n).iterated m).toFun x = _
    let y := AddCircle.equivIoc T 0 x
    have hy : ((y : ℝ) : AddCircle T) = x := by simp [y]
    rw [← hy, AddCircle.liftIoc_coe_apply y.property]
    change iteratedDeriv m (fourierTest T n).toFun (y : ℝ) = _
    rw [iteratedDeriv_fourierTest]
    rfl
  change ContinuousMap.toLp 2 (@AddCircle.haarAddCircle T hT) ℂ
      ((fourierTest T n).iterated m).toContinuousMap = _
  rw [hmap, map_smul]

end FourierTests

end NlsGge.Atomic.LIB002

namespace NlsGge.Atomic.LIB002

section CoefficientCriterion

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Fourier coefficients are precisely the complex Hilbert-basis inner
products, with the conjugate-linear first-slot convention kept explicit. -/
theorem inner_fourierLp_eq_fourierCoeff
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (n : ℤ) :
    inner ℂ (fourierLp 2 n) f = fourierCoeff f n := by
  calc
    inner ℂ (fourierLp 2 n) f = inner ℂ (fourierBasis n) f := by
      rw [coe_fourierBasis]
    _ = fourierBasis.repr f n := (fourierBasis.repr_apply_apply f n).symm
    _ = fourierCoeff f n := fourierBasis_repr f n

/-- Testing a weak derivative against each Fourier character recovers every
coefficient, including `n = 0`, with no division by the frequency. -/
theorem weakDerivative_fourierCoeff
    {m : ℕ} {u v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)}
    (hweak : HasWeakDerivativeL2 T m u v) (n : ℤ) :
    fourierCoeff v n = fourierMultiplier T n ^ m * fourierCoeff u n := by
  have hw := hweak (fourierTest T n)
  rw [toL2_iterated_fourierTest, toL2_fourierTest, inner_smul_left,
    inner_fourierLp_eq_fourierCoeff, inner_fourierLp_eq_fourierCoeff] at hw
  have hfreqStar : star (fourierMultiplier T n) = -fourierMultiplier T n := by
    simp [fourierMultiplier] <;> ring
  have hstar : star (fourierMultiplier T n ^ m) =
      (-1 : ℂ) ^ m * fourierMultiplier T n ^ m := by
    calc
      star (fourierMultiplier T n ^ m) = star (fourierMultiplier T n) ^ m := by simp
      _ = (-fourierMultiplier T n) ^ m := by rw [hfreqStar]
      _ = (-1 : ℂ) ^ m * fourierMultiplier T n ^ m := by rw [neg_pow]
  change star (fourierMultiplier T n ^ m) * fourierCoeff u n =
    (-1 : ℂ) ^ m * fourierCoeff v n at hw
  rw [hstar] at hw
  have hmul : (-1 : ℂ) ^ m *
        (fourierMultiplier T n ^ m * fourierCoeff u n) =
      (-1 : ℂ) ^ m * fourierCoeff v n := by
    calc
      (-1 : ℂ) ^ m * (fourierMultiplier T n ^ m * fourierCoeff u n) =
          ((-1 : ℂ) ^ m * fourierMultiplier T n ^ m) * fourierCoeff u n := by ring
      _ = (-1 : ℂ) ^ m * fourierCoeff v n := hw
  have hsign : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_left_cancel₀ hsign hmul).symm

/-- A weak `m`th derivative in `L²` necessarily has square-summable weighted
Fourier coefficients. -/
theorem weakDerivative_fourier_summable
    {m : ℕ} {u v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)}
    (hweak : HasWeakDerivativeL2 T m u v) :
    Summable (fun n : ℤ =>
      ‖fourierMultiplier T n ^ m * fourierCoeff u n‖ ^ 2) := by
  have hv := (hasSum_sq_fourierCoeff v).summable
  apply hv.congr
  intro n
  rw [weakDerivative_fourierCoeff hweak n]

end CoefficientCriterion

end NlsGge.Atomic.LIB002

namespace NlsGge.Atomic.LIB002

section WeakFourierIff

open scoped ENNReal lp

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Fourier coefficients of the `m`th derivative of any smooth periodic
test obey the same classical multiplier identity. -/
theorem fourierCoeff_iterated_test
    (φ : SmoothPeriodicTest T) (m : ℕ) (n : ℤ) :
    fourierCoeff (SmoothPeriodicTest.toL2 (φ.iterated m)) n =
      fourierMultiplier T n ^ m * fourierCoeff (SmoothPeriodicTest.toL2 φ) n := by
  rw [fourierCoeff_toL2, fourierCoeff_toL2]
  simpa [SmoothPeriodicTest.iterated] using fourierCoeffOn_iteratedDeriv_of_smooth_periodic hT.out
    φ.toFun φ.smooth φ.periodic m n

/-- The Fourier isometry converts the literal weak test identity into an
identity of absolutely convergent Hilbert-basis pairings. -/
theorem weakTest_identity_of_fourier_coefficients
    {m : ℕ} {u v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)}
    (hcoeff : ∀ n : ℤ,
      fourierCoeff v n = fourierMultiplier T n ^ m * fourierCoeff u n) :
    HasWeakDerivativeL2 T m u v := by
  intro φ
  let F := normalizedFourierL2 T
  have hstar (n : ℤ) : star (fourierMultiplier T n ^ m) =
      (-1 : ℂ) ^ m * fourierMultiplier T n ^ m := by
    have hfreqStar : star (fourierMultiplier T n) = -fourierMultiplier T n := by
      simp [fourierMultiplier] <;> ring
    calc
      star (fourierMultiplier T n ^ m) = star (fourierMultiplier T n) ^ m := by simp
      _ = (-fourierMultiplier T n) ^ m := by rw [hfreqStar]
      _ = (-1 : ℂ) ^ m * fourierMultiplier T n ^ m := by rw [neg_pow]
  have hterm (n : ℤ) :
      inner ℂ (F (SmoothPeriodicTest.toL2 (φ.iterated m)) n) (F u n) =
        (-1 : ℂ) ^ m * inner ℂ (F (SmoothPeriodicTest.toL2 φ) n) (F v n) := by
    rw [normalizedFourierL2_apply, normalizedFourierL2_apply,
      normalizedFourierL2_apply, normalizedFourierL2_apply,
      fourierCoeff_iterated_test, hcoeff n]
    rw [RCLike.inner_apply', RCLike.inner_apply']
    change star (fourierMultiplier T n ^ m *
      fourierCoeff (SmoothPeriodicTest.toL2 φ) n) * fourierCoeff u n =
        (-1 : ℂ) ^ m * (star (fourierCoeff (SmoothPeriodicTest.toL2 φ) n) *
          (fourierMultiplier T n ^ m * fourierCoeff u n))
    rw [star_mul]
    change star (fourierCoeff (SmoothPeriodicTest.toL2 φ) n) *
      star (fourierMultiplier T n ^ m) * fourierCoeff u n =
        (-1 : ℂ) ^ m * (star (fourierCoeff (SmoothPeriodicTest.toL2 φ) n) *
          (fourierMultiplier T n ^ m * fourierCoeff u n))
    rw [hstar n]
    ring
  calc
    inner ℂ (SmoothPeriodicTest.toL2 (φ.iterated m)) u =
        inner ℂ (F (SmoothPeriodicTest.toL2 (φ.iterated m))) (F u) := by
          symm
          exact F.inner_map_map _ _
    _ = ∑' n : ℤ,
        inner ℂ (F (SmoothPeriodicTest.toL2 (φ.iterated m)) n) (F u n) :=
          lp.inner_eq_tsum _ _
    _ = ∑' n : ℤ,
        (-1 : ℂ) ^ m * inner ℂ (F (SmoothPeriodicTest.toL2 φ) n) (F v n) :=
          tsum_congr hterm
    _ = (-1 : ℂ) ^ m *
        inner ℂ (F (SmoothPeriodicTest.toL2 φ)) (F v) := by
          rw [tsum_mul_left, lp.inner_eq_tsum]
    _ = (-1 : ℂ) ^ m * inner ℂ (SmoothPeriodicTest.toL2 φ) v := by
          rw [F.inner_map_map]

/-- The all-test weak derivative relation is equivalent to its coefficient
identity at every integer frequency. -/
theorem weakDerivative_fourierCoeff_iff
    {m : ℕ} {u v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)} :
    HasWeakDerivativeL2 T m u v ↔
      ∀ n : ℤ, fourierCoeff v n =
        fourierMultiplier T n ^ m * fourierCoeff u n := by
  constructor
  · intro hweak n
    exact weakDerivative_fourierCoeff hweak n
  · exact weakTest_identity_of_fourier_coefficients

/-- Arbitrary-period weak differentiation of order `m` is equivalent to
square summability of all multiplier-weighted Fourier coefficients. The
zero frequency is included literally; for positive order its multiplier is
zero, while at order zero it is one. -/
theorem weakDerivative_fourier_iff
    (m : ℕ) (u : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    (∃ v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT),
      HasWeakDerivativeL2 T m u v) ↔
      Summable (fun n : ℤ =>
        ‖fourierMultiplier T n ^ m * fourierCoeff u n‖ ^ 2) := by
  constructor
  · rintro ⟨v, hweak⟩
    exact weakDerivative_fourier_summable hweak
  · intro hweighted
    let a : ℤ → ℂ := fun n =>
      fourierMultiplier T n ^ m * fourierCoeff u n
    have hMemℓp : Memℓp a (2 : ℝ≥0∞) := by
      apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
      simpa [a] using hweighted
    let c : lp (fun _ : ℤ => ℂ) 2 := ⟨a, hMemℓp⟩
    let v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT) :=
      (normalizedFourierL2 T).symm c
    have hcoeff (n : ℤ) :
        fourierCoeff v n = fourierMultiplier T n ^ m * fourierCoeff u n := by
      rw [← normalizedFourierL2_apply]
      change (normalizedFourierL2 T ((normalizedFourierL2 T).symm c)) n = _
      rw [(normalizedFourierL2 T).apply_symm_apply]
    exact ⟨v, weakTest_identity_of_fourier_coefficients hcoeff⟩

end WeakFourierIff

end NlsGge.Atomic.LIB002

namespace NlsGge.Atomic.LIB002

/-- Explicit zero-mode form of the coefficient identity: order zero preserves
mass, while every positive derivative order annihilates constants. -/
theorem weakDerivative_zeroMode
    {T : ℝ} [hT : Fact (0 < T)] {m : ℕ}
    {u v : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)}
    (hweak : HasWeakDerivativeL2 T m u v) :
    fourierCoeff v 0 = if m = 0 then fourierCoeff u 0 else 0 := by
  rw [weakDerivative_fourierCoeff hweak 0]
  by_cases hm : m = 0
  · subst m
    simp [fourierMultiplier]
  · simp [fourierMultiplier, hm]

end NlsGge.Atomic.LIB002
