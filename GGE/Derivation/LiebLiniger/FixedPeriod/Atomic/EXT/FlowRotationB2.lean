import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB1

/-! # The actual finite-gap Hamiltonian pairing

The first variation is computed on h¹, transported using the actual h⁰
canonicity through its Sobolev derivative compatibility, and restricted to the
finite tangent plane using conservation of actual Birkhoff support.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38
local notation "B" => NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
local notation "H1" => SobolevCarrier38 ((1 : ℕ) : ℝ)

/-- Reflection of the first symplectic argument is reflection of the second;
the two minus signs of the reflected Fourier convention cancel. -/
theorem stdSymplectic38_reflection38 (x y : H1) :
    stdSymplectic38 (carrierCoe38 _ (reflIso38 _ x)) (carrierCoe38 _ y) =
      stdSymplectic38 (carrierCoe38 _ x) (carrierCoe38 _ (reflIso38 _ y)) := by
  unfold stdSymplectic38
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun n => (starRingEnd ℂ (carrierCoe38 _ x n) *
      carrierCoe38 _ (reflIso38 _ y) n).im)]
  apply tsum_congr
  intro n
  change (starRingEnd ℂ (-carrierCoe38 _ x (-n)) * carrierCoe38 _ y n).im =
    (starRingEnd ℂ (carrierCoe38 _ x (-n)) * -carrierCoe38 _ y (- -n)).im
  simp only [neg_neg, map_neg, neg_mul, mul_neg]

/-- The standard symplectic pairing of two inserted vectors is the literal
finite sum of imaginary coordinate pairings. -/
theorem stdSymplectic38_finitePlane38 (Λ : Finset ℤ) (a b : Λ → ℂ) :
    stdSymplectic38 (extZero38 Λ a) (extZero38 Λ b) =
      ∑ i : Λ, (starRingEnd ℂ (a i) * b i).im := by
  unfold stdSymplectic38
  rw [tsum_eq_sum (s := Λ) (fun n hn => by
    rw [extZero38_apply_of_not_mem _ hn, map_zero, zero_mul, Complex.zero_im])]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i _
  rw [extZero38_apply_of_mem _ i.2, extZero38_apply_of_mem _ i.2]

/-- The NLS first variation is twice the symplectic pairing with the actual
uncut PDE right-hand side. The two component sums are summable on h¹ before
any infinite-sum identity is used. -/
theorem ham_variation_rhs38 (x v : H1) :
    2 * (∑' n : ℤ, ((disp n : ℝ) : ℂ) *
      (starRingEnd ℂ (carrierCoe38 _ x n) * carrierCoe38 _ v n)).re +
    2 * (∑' n : ℤ, starRingEnd ℂ (nonlin (carrierCoe38 _ x) n) *
      carrierCoe38 _ v n).re =
    2 * stdSymplectic38 (rhsSeq (carrierCoe38 _ x)) (carrierCoe38 _ v) := by
  let a := fun n : ℤ => ((disp n : ℝ) : ℂ) *
    (starRingEnd ℂ (carrierCoe38 _ x n) * carrierCoe38 _ v n)
  let b := fun n : ℤ => starRingEnd ℂ (nonlin (carrierCoe38 _ x) n) *
    carrierCoe38 _ v n
  have ha : Summable a := summable_wconj disp_nonneg
    (summable_kin_of_h1 (carrierCoe38_mem _ x))
    (summable_kin_of_h1 (carrierCoe38_mem _ v))
  have hb : Summable b := summable_conj_mul38
    (nonlin_summable_sq38 (carrierCoe38_mem _ x))
    (summable_sq_of_h1 (carrierCoe38_mem _ v))
  have he (n : ℤ) : starRingEnd ℂ (rhsSeq (carrierCoe38 _ x) n) *
      carrierCoe38 _ v n = Complex.I * (a n + b n) := by
    simp only [rhsSeq, map_mul, map_add, map_neg, Complex.conj_I,
      Complex.conj_ofReal, neg_neg, a, b]
    ring
  unfold stdSymplectic38
  simp_rw [he]
  rw [← Complex.im_tsum ((ha.add hb).mul_left Complex.I),
    tsum_mul_left, ha.tsum_add hb]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.add_re]
  dsimp only [a, b]
  ring

/-- The derivative of the actual Birkhoff curve is tangent to its finite
coordinate plane. The premise identifies a strong h¹ curve with the actual
reflected Fourier trajectory; the conclusion differentiates this identity. -/
theorem actualPhi_finitePlane_tangent38 (Λ : Finset ℤ) (w : Λ → ℂ)
    (γ : ℝ → H1) (D : H1) (t : ℝ)
    (hγ : ∀ s, carrierCoe38 _ (γ s) =
      fourierSeq38 (nlsFlowL2 s ((B0).finiteGapField38 Λ w)))
    (hD : HasDerivAt γ D t) :
    fderiv ℝ ((B0).TC 1) (γ t) D = finitePlaneInsert38 Λ (deriv (ZΛ Λ w) t) := by
  have he : (fun s => (B0).TC 1 (γ s)) =
      fun s => finitePlaneInsert38 Λ (ZΛ Λ w s) := by
    funext s
    apply carrierExt38
    rw [BirkhoffTop38.TC_coe, hγ s, finitePlaneInsert38_coe]
    exact actualPhi_eq_extZero_ZΛ38 Λ w s
  have h₁ := (((B).analyticOnNhd_TC 1 (γ t) (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp_hasDerivAt t hD
  have h₂ := (finitePlaneInsert38 Λ).hasFDerivAt.comp_hasDerivAt t
    ((differentiable_ZΛ38 Λ w t).hasDerivAt)
  change HasDerivAt (fun s => (B0).TC 1 (γ s)) _ t at h₁
  rw [he] at h₁
  exact h₁.unique h₂

end LiebLiniger.FixedPeriod.EXT
