import Mathlib
import NlsGge.Atomic.G6.G6042Host

/- G6042SUP PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/Atomic/G6/G6042Sup.lean, namespace
   NlsGge.ThirdConsultation.G6042S. Supporting result for G6-042 (no packet increment): every conclusion of the G6-042
   head after its differentiability clause, for ANY H : h1 → ℝ that is differentiable at z and invariant under
   coefficientwise-modulus-preserving changes (exactly G6-033's second clause). GK §20.3 route:
   rotation of the n-th coordinate preserves all moduli, so DH(z)(i z_n e_n) = 0; at z_n = 0 the even dependence gives
   DH(z) e_n = DH(z)(i e_n) = 0; the bracket with the action and the real-frequency form follow. The h^{-1} membership is
   proved by testing DH(z) on finite vectors Σ_{n∈F} e_n (A_n + i B_n)/w_n (no Riesz map needed):
   Σ_F (A_n²+B_n²)/w_n ≤ ‖DH(z)‖². Uses only the landed carrier API and the G6042Host definitions. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign
noncomputable section
namespace NlsGge.ThirdConsultation.G6042S

theorem coe_dir (n : ℤ) (a : ℂ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (coordinateDirection n a) = Pi.single n a := by
  unfold coordinateDirection
  exact carrierCoe38_mk _ _ _

/-- `a ↦ coordinateDirection n a` as a continuous real-linear map. -/
def dirCLM (n : ℤ) : ℂ →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := coordinateDirection n
      map_add' := fun a b => carrierExt38 (by
        show carrierCoe38 _ (coordinateDirection n (a + b)) =
          carrierCoe38 _ (coordinateDirection n a) + carrierCoe38 _ (coordinateDirection n b)
        rw [coe_dir, coe_dir, coe_dir, Pi.single_add])
      map_smul' := fun c a => carrierExt38 (by
        show carrierCoe38 _ (coordinateDirection n (c • a)) =
          (c : ℝ) • carrierCoe38 _ (coordinateDirection n a)
        rw [coe_dir, coe_dir]
        funext m
        by_cases h : m = n
        · subst h; simp
        · simp [Pi.single_apply, h]) }

theorem dirCLM_apply (n : ℤ) (a : ℂ) : dirCLM n a = coordinateDirection n a := rfl

/-- Evaluation of the `n`-th coordinate as a continuous real-linear map. -/
def evCLM (n : ℤ) : SobolevCarrier38 ((1 : ℕ) : ℝ) →L[ℝ] ℂ where
  toFun w := carrierCoe38 ((1 : ℕ) : ℝ) w n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_carrierCoe_apply38 _ n

theorem evCLM_apply (n : ℤ) (w : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    evCLM n w = carrierCoe38 ((1 : ℕ) : ℝ) w n := rfl

theorem coe_add_dir (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n m : ℤ) (b : ℂ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (z + dirCLM n b) m =
      carrierCoe38 ((1 : ℕ) : ℝ) z m + (Pi.single n b : ℤ → ℂ) m := by
  show carrierCoe38 ((1 : ℕ) : ℝ) z m + carrierCoe38 ((1 : ℕ) : ℝ) (coordinateDirection n b) m = _
  rw [coe_dir]

/-- Real linearity in the complex coordinate direction. -/
theorem L_dir (L : SobolevCarrier38 ((1 : ℕ) : ℝ) →L[ℝ] ℝ) (n : ℤ) (a : ℂ) :
    L (coordinateDirection n a) =
      a.re * L (coordinateDirection n 1) + a.im * L (coordinateDirection n Complex.I) := by
  have e : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  have h : coordinateDirection n a =
      a.re • coordinateDirection n 1 + a.im • coordinateDirection n Complex.I := by
    have h0 := congrArg (dirCLM n) e
    simpa only [map_add, map_smul, dirCLM_apply] using h0
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

section
variable (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ)
  (hinv : ∀ w w' : SobolevCarrier38 ((1 : ℕ) : ℝ),
    (∀ m : ℤ, ‖carrierCoe38 ((1 : ℕ) : ℝ) w m‖ ^ 2 = ‖carrierCoe38 ((1 : ℕ) : ℝ) w' m‖ ^ 2) → H w = H w')
  (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (hd : DifferentiableAt ℝ H z)

include hinv hd in
/-- Rotation of the `n`-th coordinate: `DH(z)(i z_n e_n) = 0`. -/
theorem rot_deriv_zero (n : ℤ) :
    fderiv ℝ H z (coordinateDirection n (Complex.I * carrierCoe38 ((1 : ℕ) : ℝ) z n)) = 0 := by
  set zn := carrierCoe38 ((1 : ℕ) : ℝ) z n with hzn
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I
  have h3 : HasDerivAt (fun θ : ℝ => (Complex.exp ((θ : ℂ) * Complex.I) - 1) * zn)
      (Complex.I * zn) 0 := by
    have := (h1.cexp.sub_const 1).mul_const zn
    simpa using this
  have hγ : HasDerivAt (fun θ : ℝ => z + dirCLM n ((Complex.exp ((θ : ℂ) * Complex.I) - 1) * zn))
      (dirCLM n (Complex.I * zn)) 0 :=
    ((dirCLM n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3).const_add z
  have hγ0 : z = (fun θ : ℝ => z + dirCLM n ((Complex.exp ((θ : ℂ) * Complex.I) - 1) * zn)) 0 := by
    simp
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0
  have hconst : (H ∘ fun θ : ℝ => z + dirCLM n ((Complex.exp ((θ : ℂ) * Complex.I) - 1) * zn)) =
      fun _ => H z := by
    funext θ
    refine hinv _ _ (fun m => ?_)
    rw [coe_add_dir]
    by_cases hm : m = n
    · subst hm
      rw [Pi.single_eq_same, ← hzn]
      have : zn + (Complex.exp ((θ : ℂ) * Complex.I) - 1) * zn = Complex.exp ((θ : ℂ) * Complex.I) * zn := by
        ring
      rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    · rw [Pi.single_eq_of_ne hm, add_zero]
  rw [hconst] at hc
  have := hc.unique (hasDerivAt_const (0 : ℝ) (H z))
  rw [← dirCLM_apply]
  exact this

include hinv hd in
/-- At a zero coordinate both coordinate derivatives vanish (even dependence). -/
theorem zero_coord_deriv (n : ℤ) (hz : carrierCoe38 ((1 : ℕ) : ℝ) z n = 0) (a : ℂ) :
    fderiv ℝ H z (coordinateDirection n a) = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const a
  have hγ : HasDerivAt (fun t : ℝ => z + dirCLM n ((t : ℂ) * a)) (dirCLM n a) 0 :=
    ((dirCLM n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).const_add z
  have hγ0 : z = (fun t : ℝ => z + dirCLM n ((t : ℂ) * a)) 0 := by simp
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0
  set f := H ∘ fun t : ℝ => z + dirCLM n ((t : ℂ) * a) with hf
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    refine hinv _ _ (fun m => ?_)
    rw [coe_add_dir, coe_add_dir]
    by_cases hm : m = n
    · subst hm
      rw [Pi.single_eq_same, Pi.single_eq_same, hz, zero_add, zero_add, norm_mul, norm_mul,
        Complex.ofReal_neg, norm_neg]
    · rw [Pi.single_eq_of_ne hm, Pi.single_eq_of_ne hm]
  have hc' : HasDerivAt (f ∘ Neg.neg) (fderiv ℝ H z (dirCLM n a) * (-1)) 0 := by
    have hn : HasDerivAt (Neg.neg : ℝ → ℝ) (-1) 0 := hasDerivAt_neg 0
    have hc0 : HasDerivAt f (fderiv ℝ H z (dirCLM n a)) (-(0 : ℝ)) := by rw [neg_zero]; exact hc
    exact hc0.comp (0 : ℝ) hn
  have hfe : f ∘ Neg.neg = f := funext fun t => heven t
  rw [hfe] at hc'
  have := hc.unique hc'
  rw [← dirCLM_apply]
  linarith

include hinv hd in
/-- The key relation `x B - y A = 0` with `z_n = x + i y`. -/
theorem key_relation (n : ℤ) :
    (carrierCoe38 ((1 : ℕ) : ℝ) z n).re * fderiv ℝ H z (coordinateDirection n Complex.I) -
      (carrierCoe38 ((1 : ℕ) : ℝ) z n).im * fderiv ℝ H z (coordinateDirection n 1) = 0 := by
  have h := rot_deriv_zero H hinv z hd n
  rw [L_dir] at h
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, zero_add] at h
  linarith

theorem fderiv_coordinateAction (n : ℤ) (v : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    fderiv ℝ (coordinateAction n) z v =
      2 * ((starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ) z n) * carrierCoe38 ((1 : ℕ) : ℝ) v n).re := by
  have hact : HasFDerivAt (fun w => ‖evCLM n w‖ ^ 2)
      (2 • (innerSL ℝ (evCLM n z)).comp (evCLM n)) z := (evCLM n).hasFDerivAt.norm_sq
  have hfun : coordinateAction n = fun w => ‖evCLM n w‖ ^ 2 := rfl
  rw [hfun, hact.fderiv]
  simp [evCLM_apply, Complex.inner]
  ring

include hinv hd in
theorem poisson_zero (n : ℤ) :
    coordinatePoisson n (coordinateAction n) H z = 0 := by
  have hk := key_relation H hinv z hd n
  unfold coordinatePoisson
  rw [fderiv_coordinateAction, fderiv_coordinateAction, coe_dir, coe_dir]
  simp only [Pi.single_eq_same, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, neg_mul, sub_neg_eq_add,
    zero_add]
  linear_combination (2 : ℝ) * hk / 2

theorem field_eq (n : ℤ) :
    coordinateHamiltonianField H z n =
      ((fderiv ℝ H z (coordinateDirection n Complex.I) / 2 : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ H z (coordinateDirection n 1) / 2 : ℝ) : ℂ) := by
  unfold coordinateHamiltonianField
  apply Complex.ext <;> simp <;> ring

/-- `A_n = DH(z) e_n`, `B_n = DH(z) (i e_n)`, `w_n` the h1 weight. -/
abbrev Acoef (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) : ℝ :=
  fderiv ℝ H z (coordinateDirection n 1)

abbrev Bcoef (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) : ℝ :=
  fderiv ℝ H z (coordinateDirection n Complex.I)

abbrev wt (n : ℤ) : ℝ := sobolevModeWeight ((1 : ℕ) : ℝ) n

theorem norm_sq_field (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    ‖coordinateHamiltonianField H z n‖ ^ 2 = (Acoef H z n ^ 2 + Bcoef H z n ^ 2) / 4 := by
  rw [field_eq, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem rpow_neg_one_weight (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * (-1 : ℝ)) = (wt n)⁻¹ := by
  show japaneseBracket n ^ (2 * (-1 : ℝ)) = (japaneseBracket n ^ (2 * ((1 : ℕ) : ℝ)))⁻¹
  rw [Nat.cast_one, show (2 : ℝ) * -1 = -(2 * 1) by norm_num,
    Real.rpow_neg (japaneseBracket_pos n).le]

/-- Test-vector bound: `Σ_F (A_n² + B_n²)/w_n ≤ ‖DH(z)‖²` for every finite `F`. -/
theorem partial_bound (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (F : Finset ℤ) :
    ∑ n ∈ F, (Acoef H z n ^ 2 + Bcoef H z n ^ 2) / wt n ≤ ‖fderiv ℝ H z‖ ^ 2 := by
  set L := fderiv ℝ H z with hL
  have hw : ∀ n, 0 < wt n := fun n => sobolevModeWeight_pos _ n
  let a : ℤ → ℂ := fun n => ((Acoef H z n / wt n : ℝ) : ℂ) + ((Bcoef H z n / wt n : ℝ) : ℂ) * Complex.I
  have hare : ∀ n, (a n).re = Acoef H z n / wt n := fun n => by simp [a]
  have haim : ∀ n, (a n).im = Bcoef H z n / wt n := fun n => by simp [a]
  set v : SobolevCarrier38 ((1 : ℕ) : ℝ) := ∑ n ∈ F, dirCLM n (a n) with hv
  have hLv : L v = ∑ n ∈ F, (Acoef H z n ^ 2 + Bcoef H z n ^ 2) / wt n := by
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [dirCLM_apply, L_dir, hare, haim]
    have := (hw n).ne'
    field_simp
    ring
  have hcoe : ∀ m, carrierCoe38 ((1 : ℕ) : ℝ) v m = if m ∈ F then a m else 0 := by
    intro m
    show evCLM m v = _
    rw [hv, map_sum]
    simp only [evCLM_apply, dirCLM_apply, coe_dir]
    exact Finset.sum_pi_single m a F
  have hnorm : ‖v‖ ^ 2 = ∑ n ∈ F, (Acoef H z n ^ 2 + Bcoef H z n ^ 2) / wt n := by
    have h := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) v
    have hz0 : ∀ m ∉ F, sobolevModeWeight ((1 : ℕ) : ℝ) m * ‖carrierCoe38 ((1 : ℕ) : ℝ) v m‖ ^ 2 = 0 := by
      intro m hm
      rw [hcoe, if_neg hm]
      simp
    have h2 : HasSum (fun m => sobolevModeWeight ((1 : ℕ) : ℝ) m * ‖carrierCoe38 ((1 : ℕ) : ℝ) v m‖ ^ 2)
        (∑ m ∈ F, sobolevModeWeight ((1 : ℕ) : ℝ) m * ‖carrierCoe38 ((1 : ℕ) : ℝ) v m‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero hz0
    rw [h.unique h2]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hcoe, if_pos hn, Complex.sq_norm, Complex.normSq_apply, hare, haim]
    have := (hw n).ne'
    field_simp
  set S := ∑ n ∈ F, (Acoef H z n ^ 2 + Bcoef H z n ^ 2) / wt n with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => div_nonneg (by positivity) (hw n).le
  have hle : L v ≤ ‖L‖ * ‖v‖ := by
    have h1 := L.le_opNorm v
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_abs_self _) h1
  have hvS : ‖v‖ = Real.sqrt S := by rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  rw [hLv, hvS] at hle
  have hs := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  have hL0 := norm_nonneg L
  nlinarith [sq_nonneg (‖L‖ - Real.sqrt S)]

/-- The coordinate Hamiltonian field lies in `h^{-1}` (for every `H`; `fderiv` is a bounded functional). -/
theorem field_mem_neg_one (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    (fun n : ℤ => coordinateHamiltonianField H z n) ∈ seqSobolev38 (-1 : ℝ) := by
  have hw : ∀ n, 0 < wt n := fun n => sobolevModeWeight_pos _ n
  have hf0 : ∀ n, 0 ≤ (Acoef H z n ^ 2 + Bcoef H z n ^ 2) / wt n :=
    fun n => div_nonneg (by positivity) (hw n).le
  have hsum := summable_of_sum_le hf0 (partial_bound H z)
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  refine (hsum.div_const 4).congr (fun n => ?_)
  rw [norm_sq_field, rpow_neg_one_weight]
  ring

include hinv hd in
theorem re_zero (n : ℤ) :
    2 * (star (carrierCoe38 ((1 : ℕ) : ℝ) z n) * coordinateHamiltonianField H z n).re = 0 := by
  have hk := key_relation H hinv z hd n
  rw [field_eq]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  linear_combination hk

include hinv hd in
theorem exists_frequency (n : ℤ) :
    ∃ ω : ℝ, coordinateHamiltonianField H z n =
      -Complex.I * (ω : ℂ) * carrierCoe38 ((1 : ℕ) : ℝ) z n := by
  set x := (carrierCoe38 ((1 : ℕ) : ℝ) z n).re with hx
  set y := (carrierCoe38 ((1 : ℕ) : ℝ) z n).im with hy
  set A := fderiv ℝ H z (coordinateDirection n 1) with hA
  set B := fderiv ℝ H z (coordinateDirection n Complex.I) with hB
  have hk : x * B - y * A = 0 := key_relation H hinv z hd n
  by_cases h0 : carrierCoe38 ((1 : ℕ) : ℝ) z n = 0
  · refine ⟨0, ?_⟩
    have hA0 : A = 0 := zero_coord_deriv H hinv z hd n h0 1
    have hB0 : B = 0 := zero_coord_deriv H hinv z hd n h0 Complex.I
    rw [field_eq, ← hA, ← hB, hA0, hB0, h0]
    simp
  · have hr : x ^ 2 + y ^ 2 ≠ 0 := by
      intro h
      apply h0
      apply Complex.ext
      · simp only [Complex.zero_re]; nlinarith [sq_nonneg x, sq_nonneg y]
      · simp only [Complex.zero_im]; nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨(x * A + y * B) / (2 * (x ^ 2 + y ^ 2)), ?_⟩
    rw [field_eq, ← hA, ← hB]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_im, ← hx, ← hy]
      field_simp
      linear_combination x * hk
    · simp only [Complex.sub_im, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_im, ← hx, ← hy]
      field_simp
      linear_combination y * hk


include hinv hd in
/-- All G6-042 conclusions after differentiability, for any modulus-invariant `H` differentiable at `z`. -/
theorem G6042_of :
    (fun n : ℤ => coordinateHamiltonianField H z n) ∈ seqSobolev38 (-1 : ℝ) ∧
    ∀ n : ℤ,
      coordinatePoisson n (coordinateAction n) H z = 0 ∧
      2 * (star (carrierCoe38 ((1 : ℕ) : ℝ) z n) * coordinateHamiltonianField H z n).re = 0 ∧
      ∃ ω : ℝ, coordinateHamiltonianField H z n = -Complex.I * (ω : ℂ) * carrierCoe38 ((1 : ℕ) : ℝ) z n :=
  ⟨field_mem_neg_one H z, fun n =>
    ⟨poisson_zero H hinv z hd n, re_zero H hinv z hd n, exists_frequency H hinv z hd n⟩⟩

end

end NlsGge.ThirdConsultation.G6042S
