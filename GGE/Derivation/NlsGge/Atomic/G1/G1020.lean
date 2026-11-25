/- G1-020 PRODUCTION02 (proof development batch-8 landing kit). Source: proof development/G1020_PROOF01.lean.txt. #check/#print lines removed; original namespaces kept. No acceptance claimed. -/
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential

/- G1-020 pre-approval proof candidate (proof development, AUTHOR; not reviewed).  Statement = proof development's G1020_COMMAND01.
   Route (GK Thm 2.4, derivative clause): f(w) = M(t,w) - E(t,w) is entire; Cauchy's integral formula on the unit circle
   gives ||f'(c)||^2 <= (2 pi)^{-1} int_0^{2 pi} ||f(c + e^{i theta})||^2 dtheta (Cauchy-Schwarz); for fixed theta the
   sequence xi_n + e^{i theta} satisfies the G1-019 hypothesis with R1 + 1, so (private copy of proof development's G1019_PROOF01) every finite
   sum of squares over the circle points is <= C(R0, R1+1); finite sums commute with the theta-integral. -/

set_option autoImplicit false

/- ===== private copy of proof development G1019_PROOF01 (namespace renamed) ===== -/
section
/- G1-019 pre-approval proof candidate (proof development, AUTHOR; not reviewed).  Statement = proof development's G1019_COMMAND01.
   Route (GK Thm 2.4): G1-016 (private copy of proof development's G1016_PROOF01) bounds the weighted ||M - E|| by the weighted
   ||M_1|| plus c e^c (int ||M_1||^2)^{1/2}; the first Volterra term is off-diagonal with entries I seqOsc(a,-z) and -I seqOsc(b,z);
   the production Bessel estimate for bounded perturbed frequencies (G1-015, perturbed_fourier_bessel_physical) bounds the
   sums of squares over every finite set of indices, uniformly in the time; the finite sums of integrals are
   integrals of finite sums, so no summation/integration interchange of infinite sums is needed. -/

set_option autoImplicit false

/- ===== private copy of proof development G1016_PROOF01 (namespace renamed) ===== -/
section
/- G1-016 pre-approval proof candidate (proof development).  Statement verbatim from proof development's G1016_COMMAND01.
   Route (source Lemma 2.1): with weights e^{-|Im z| t}, N = M - E - M_1 = V(M-E), so
   n(t) <= int_0^t w(s) (a(s) + n(s)) ds with w = sqrt(|phi1|^2+|phi2|^2), a = weighted |M_1|;
   Gronwall (integral form, proved here via absolute continuity) gives n(t) <= b(t) e^{W(t)},
   b = int w a; Cauchy-Schwarz and int_0^1 w^2 = |phi1|^2+|phi2|^2 finish.  Invertibility is not used. -/

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1020S1.K19.K16

noncomputable section


theorem lipschitzOnWith_exp_Iic : LipschitzOnWith 1 Real.exp (Set.Iic (0 : ℝ)) := by
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) (f := Real.exp) (s := Set.Iic (0 : ℝ))
    (fun x _ => Real.differentiableAt_exp) (fun x hx => ?_) (convex_Iic 0)
  rw [Real.deriv_exp]
  have : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 hx
  rw [← NNReal.coe_le_coe]
  simpa using this

/-- Gronwall's inequality in integral form with an integrable weight. -/
theorem gronwall_integral {t : ℝ} (ht : 0 ≤ t) {ω n : ℝ → ℝ}
    (hω0 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ ω s)
    (hω : IntervalIntegrable ω volume 0 t) (hn : ContinuousOn n (Set.Icc (0 : ℝ) t)) (c : ℝ)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) t, n s ≤ c + ∫ r in (0 : ℝ)..s, ω r * n r) :
    n t ≤ c * Real.exp (∫ r in (0 : ℝ)..t, ω r) := by
  have hu : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
  have hωn : IntervalIntegrable (fun r => ω r * n r) volume 0 t :=
    hω.mul_continuousOn (by rw [hu]; exact hn)
  set W : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, ω r with hW
  set Q : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, ω r * n r with hQ
  have hWac : AbsolutelyContinuousOnInterval W 0 t :=
    hω.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hQac : AbsolutelyContinuousOnInterval Q 0 t :=
    hωn.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hW0 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ W s := fun s hs =>
    intervalIntegral.integral_nonneg hs.1 fun r hr => hω0 r ⟨hr.1, hr.2.trans hs.2⟩
  have hnegac : AbsolutelyContinuousOnInterval (fun s => -W s) 0 t := hWac.neg
  have hexpac : AbsolutelyContinuousOnInterval (fun s => Real.exp (-W s)) 0 t := by
    have := lipschitzOnWith_exp_Iic.comp_absolutelyContinuousOnInterval
      (g := fun s => -W s) (a := 0) (b := t)
      (fun s hs => by
        rw [hu] at hs
        exact neg_nonpos.2 (hW0 s hs)) hnegac
    exact this
  have hcac : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 t :=
    (contDiff_const.contDiffOn (s := Set.uIcc (0 : ℝ) t) (n := 1)).absolutelyContinuousOnInterval
  set P : ℝ → ℝ := fun s => Real.exp (-W s) * (Q s + c) with hP
  have hPac : AbsolutelyContinuousOnInterval P 0 t := by
    have := hexpac.fun_mul (hQac.add hcac)
    exact this
  have hint := hPac.intervalIntegrable_deriv
  have hae : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0 : ℝ) t → deriv P s ≤ 0 := by
    filter_upwards [hω.ae_hasDerivAt_integral, hωn.ae_hasDerivAt_integral] with s h1 h2 hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := by rwa [hu] at hs
    have d1 : HasDerivAt W (ω s) s := h1 hs 0 left_mem_uIcc
    have d2 : HasDerivAt Q (ω s * n s) s := h2 hs 0 left_mem_uIcc
    have d3 : HasDerivAt (fun x => Real.exp (-W x)) (Real.exp (-W s) * (-ω s)) s :=
      (d1.neg).exp
    have d4 : HasDerivAt P (Real.exp (-W s) * (-ω s) * (Q s + c) +
        Real.exp (-W s) * (ω s * n s)) s := d3.mul (d2.add_const c)
    rw [d4.deriv]
    have hn' := h s hs'
    have e1 : Real.exp (-W s) * (-ω s) * (Q s + c) + Real.exp (-W s) * (ω s * n s) =
        Real.exp (-W s) * ω s * (n s - (c + Q s)) := by ring
    rw [e1]
    have : n s - (c + Q s) ≤ 0 := by
      have := hn'
      simp only [hQ] at *
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le (hω0 s hs')) this
  have hI : ∫ s in (0 : ℝ)..t, deriv P s ≤ 0 := by
    have := intervalIntegral.integral_mono_ae_restrict (μ := volume) (a := 0) (b := t) ht hint
      (intervalIntegrable_const (c := (0 : ℝ)))
      ((ae_restrict_iff' measurableSet_Icc).2 (hae.mono fun s hs hs1 => hs (by rwa [hu])))
    simpa using this
  rw [hPac.integral_deriv_eq_sub] at hI
  have hP0 : P 0 = c := by simp [hP, hW, hQ]
  have hPt : P t ≤ c := by linarith
  have h1 : Q t + c ≤ c * Real.exp (W t) := by
    have := mul_le_mul_of_nonneg_right hPt (Real.exp_pos (W t)).le
    have e : P t * Real.exp (W t) = Q t + c := by
      simp only [hP, mul_assoc]
      rw [mul_comm (Q t + c), ← mul_assoc, ← Real.exp_add]
      simp
    rw [e] at this
    linarith
  have := h t ⟨ht, le_rfl⟩
  have e2 : (∫ r in (0 : ℝ)..t, ω r * n r) = Q t := rfl
  have e3 : (∫ r in (0 : ℝ)..t, ω r) = W t := rfl
  rw [e3]
  linarith



theorem norm_matrix_integral_le {F : ℝ → PairMat38} {t : ℝ} (ht : 0 ≤ t) {h : ℝ → ℝ}
    (hent : ∀ i j : Fin 2, IntervalIntegrable (fun s => F s i j) volume 0 t)
    (hh : IntervalIntegrable h volume 0 t)
    (hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖F s‖ ≤ h s) :
    ‖(Matrix.of fun i j => ∫ s in (0 : ℝ)..t, F s i j : PairMat38)‖ ≤ ∫ s in (0 : ℝ)..t, h s := by
  have hmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have e : F = fun s => ∑ i : Fin 2, ∑ j : Fin 2, Matrix.single i j (F s i j) := by
      funext s
      exact Matrix.matrix_eq_sum_single (F s)
    rw [e]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    have hc : Continuous (fun c : ℂ => (Matrix.single i j c : PairMat38)) := by
      refine continuous_matrix fun a b => ?_
      by_cases hab : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hab
        have e : (fun c : ℂ => (Matrix.single i j c : PairMat38) i j) = fun c => c := by
          funext c
          simp
        rw [e]
        exact continuous_id
      · have : (fun c : ℂ => (Matrix.single i j c : PairMat38) a b) = fun _ => 0 := by
          funext c
          simp [Matrix.single_apply, hab]
        rw [this]
        exact continuous_const
    exact hc.comp_aestronglyMeasurable (hent i j).1.aestronglyMeasurable
  have hhi : IntegrableOn h (Set.Ioc (0 : ℝ) t) := hh.1
  have hF : IntervalIntegrable F volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    refine Integrable.mono' hhi hmeas ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb)
  have hG : ‖∫ s in (0 : ℝ)..t, F s‖ ≤ ∫ s in (0 : ℝ)..t, h s :=
    intervalIntegral.norm_integral_le_of_norm_le ht
      (Eventually.of_forall fun s hs => hb s hs) hh
  have hEq : (Matrix.of fun i j => ∫ s in (0 : ℝ)..t, F s i j : PairMat38) =
      ∫ s in (0 : ℝ)..t, F s := by
    ext i j
    let L : PairMat38 →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
    have := L.intervalIntegral_comp_comm hF
    exact this
  rw [hEq]
  exact hG


/-! ### Norm bounds for the free solution and the potential coefficient -/

/-- The pointwise `ℓ²` size of the potential. -/
def omegaW (φ : PotPair) (s : ℝ) : ℝ :=
  Real.sqrt (‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2)

theorem omegaW_nonneg (φ : PotPair) (s : ℝ) : 0 ≤ omegaW φ s := Real.sqrt_nonneg _

def otherFin2 (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem even_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
    (hC : 0 ≤ C) (hdiag : ∀ i j : Fin 2, i ≠ j → M i j = 0)
    (hb : ∀ i : Fin 2, ‖M i i‖ ≤ C) : ‖M‖ ≤ C := by
  have hM : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hdiag i j hij
  rw [hM, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 hb

theorem odd_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
    (hC : 0 ≤ C) (hdiag : ∀ i : Fin 2, M i i = 0)
    (hb : ∀ i : Fin 2, ‖M i (otherFin2 i)‖ ≤ C) : ‖M‖ ≤ C := by
  let P : PairMat38 := !![0, 1; 1, 0]
  let D : PairMat38 := Matrix.diagonal (fun i => M i (otherFin2 i))
  have hPmul : Matrix.conjTranspose P * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]
  have hPnorm : ‖P‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self P
    rw [hPmul] at h
    norm_num at h ⊢
    nlinarith [norm_nonneg P]
  have hM : M = D * P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, P, otherFin2, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_two, hdiag]
  calc
    ‖M‖ = ‖D * P‖ := by rw [hM]
    _ ≤ ‖D‖ * ‖P‖ := Matrix.l2_opNorm_mul D P
    _ = ‖D‖ := by rw [hPnorm, mul_one]
    _ ≤ C := by
      rw [Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg hC).2 hb

theorem norm_potCoeff38_le_omega (φ : PotPair) (s : ℝ) : ‖potCoeff38 φ s‖ ≤ omegaW φ s := by
  have h1 : ‖potRepFst38 φ s‖ ≤ omegaW φ s :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖potRepSnd38 φ s‖])
  have h2 : ‖potRepSnd38 φ s‖ ≤ omegaW φ s :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖potRepFst38 φ s‖])
  refine odd_sparse_matrix_opNorm_le _ _ (omegaW_nonneg φ s)
    (fun i => by fin_cases i <;> simp [potCoeff38]) (fun i => ?_)
  fin_cases i <;> simp [potCoeff38, otherFin2, h1, h2]

theorem norm_freeE_le (z : ℂ) {r : ℝ} (hr : 0 ≤ r) : ‖freeE z r‖ ≤ Real.exp (|z.im| * r) := by
  refine even_sparse_matrix_opNorm_le _ _ (Real.exp_pos _).le (fun i j hij => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j <;> simp [freeE] at hij ⊢
  · have := norm_freeE_entry_le z r i i
    rwa [abs_of_nonneg hr] at this

/-! ### The functions on `[0,1]` -/

theorem hT1 : (0 : ℝ) ≤ 1 := zero_le_one

/-- `M(s) = ∑ M_n(s)` as a function on `ℝ` (constant extension of the fundamental solution). -/
def Mfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := ext38T hT1 (fundContT φ z hT1) s

/-- `M_1(s)` as a function on `ℝ`. -/
def M1fun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  ext38T hT1 (volterraPT φ z hT1 (freeFundT 1 z)) s

def Xfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := Mfun φ z s - freeE z s

def Nfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := Xfun φ z s - M1fun φ z s

def kerT (φ : PotPair) (z : ℂ) (t s : ℝ) : PairMat38 :=
  freeE z (t - s) * potCoeff38 φ s * Xfun φ z s

theorem cont_Mfun (φ : PotPair) (z : ℂ) : Continuous (Mfun φ z) := continuous_ext38T hT1 _

theorem cont_M1fun (φ : PotPair) (z : ℂ) : Continuous (M1fun φ z) := continuous_ext38T hT1 _

theorem cont_Xfun (φ : PotPair) (z : ℂ) : Continuous (Xfun φ z) :=
  (cont_Mfun φ z).sub (continuous_freeE z)

theorem cont_Nfun (φ : PotPair) (z : ℂ) : Continuous (Nfun φ z) :=
  (cont_Xfun φ z).sub (cont_M1fun φ z)


theorem fundContT_entry_eq' (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundContT φ z hT1 ⟨t, ht⟩ i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s *
        ext38T hT1 (fundContT φ z hT1) s) i j := by
  have h := congrArg (fun G : PairContT 1 => G ⟨t, ht⟩ i j) (fundContT_eq_add φ z hT1)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at h
  rw [h]
  rfl

theorem tsum_entry (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j = fundContT φ z hT1 ⟨t, ht⟩ i j := by
  have hent : ∀ i j : Fin 2, HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      (fundContT φ z hT1 ⟨t, ht⟩ i j) := by
    intro i j
    have e : (fun n : ℕ => potentialVolterraTerm38 φ z n t i j) =
        fun n : ℕ => ((volterraPT φ z hT1 ^ n) (freeFundT 1 z)) ⟨t, ht⟩ i j :=
      funext fun n => by rw [term_eq_powT φ z hT1 n t ht]
    rw [e]
    exact hasSum_entryT φ z hT1 ⟨t, ht⟩ i j
  have hS : Summable (fun n : ℕ => potentialVolterraTerm38 φ z n t) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => (hent i j).summable
  have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    (continuous_id.matrix_elem i j)
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      ((∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j) :=
    hS.hasSum.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hcont
  exact h1.unique (hent i j)

theorem tsum_eq_Mfun (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) = Mfun φ z t := by
  ext i j
  rw [tsum_entry φ z ht i j, Mfun, ext38T_of_mem hT1 _ ht]

theorem term1_eq (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    potentialVolterraTerm38 φ z 1 t = M1fun φ z t := by
  have h := term_eq_powT φ z hT1 1 t ht
  rw [pow_one] at h
  rw [h, M1fun, ext38T_of_mem hT1 _ ht]

theorem ker_integrable (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    IntervalIntegrable (fun s => kerT φ z t s i j) volume 0 t := by
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have h1 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (cont_Mfun φ z) ht i j
  have h2 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (continuous_freeE z) ht i j
  refine (h1.sub h2).congr ?_
  intro s _
  simp [kerT, Xfun, Matrix.mul_sub, Matrix.sub_apply]

theorem stepB (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nfun φ z t = Matrix.of fun i j => ∫ s in (0 : ℝ)..t, kerT φ z t s i j := by
  ext i j
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have h1 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (cont_Mfun φ z) ht i j
  have h2 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (continuous_freeE z) ht i j
  have hM : Mfun φ z t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Mfun φ z s) i j := by
    rw [Mfun, ext38T_of_mem hT1 _ ht]
    exact fundContT_entry_eq' φ z ht i j
  have hM1 : M1fun φ z t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * freeE z s) i j := by
    rw [M1fun, ext38T_of_mem hT1 _ ht, volterraPT_apply, volterraFunT_apply]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      have := Set.uIcc_subset_Icc (Set.left_mem_Icc.2 hT1) ht hs
      exact this
    rw [ext38T_of_mem hT1 _ hs']
    rfl
  have hker : (∫ s in (0 : ℝ)..t, kerT φ z t s i j) =
      (∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Mfun φ z s) i j) -
        ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * freeE z s) i j := by
    rw [← intervalIntegral.integral_sub h1 h2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [kerT, Xfun, Matrix.mul_sub, Matrix.sub_apply]
  rw [Matrix.of_apply, hker]
  simp only [Nfun, Xfun, Matrix.sub_apply]
  rw [hM, hM1]
  ring

/-! ### The weight `ω` and weighted norms -/

theorem omegaW_sq (φ : PotPair) (s : ℝ) :
    omegaW φ s ^ 2 = ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem intervalIntegrable_omegaW_sq (φ : PotPair) :
    IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 1 := by
  have h := (intervalIntegrable_coverRep38_sq_one φ.1).add (intervalIntegrable_coverRep38_sq_one φ.2)
  refine h.congr ?_
  intro s _
  simp only [omegaW_sq, potRepFst38, potRepSnd38]

theorem integral_omegaW_sq (φ : PotPair) :
    ∫ s in (0 : ℝ)..1, omegaW φ s ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
  have e : ∀ s, omegaW φ s ^ 2 = ‖coverRep38 φ.1 s‖ ^ 2 + ‖coverRep38 φ.2 s‖ ^ 2 := fun s => by
    rw [omegaW_sq]; rfl
  simp_rw [e]
  rw [intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one φ.1)
    (intervalIntegrable_coverRep38_sq_one φ.2), integral_sq_coverRep38_one, integral_sq_coverRep38_one]

theorem omegaW_le_potW (φ : PotPair) (s : ℝ) : omegaW φ s ≤ potW38 φ s := by
  unfold omegaW potW38
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (potRepFst38 φ s), norm_nonneg (potRepSnd38 φ s)]

theorem intervalIntegrable_omegaW (φ : PotPair) : IntervalIntegrable (omegaW φ) volume 0 1 := by
  have hsq : IntervalIntegrable (fun s => ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_coverRep38_sq_one φ.1).add (intervalIntegrable_coverRep38_sq_one φ.2)
  have hm : AEStronglyMeasurable (omegaW φ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hsq.1.aestronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (intervalIntegrable_potW38 φ).1 hm ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s _ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (omegaW_nonneg φ s)]
  exact omegaW_le_potW φ s

/-- The weighted norms. -/
def aW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖M1fun φ z s‖
def nW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖Nfun φ z s‖
def YW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖Xfun φ z s‖

theorem continuous_expW (z : ℂ) : Continuous fun s : ℝ => Real.exp (-|z.im| * s) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem continuous_aW (φ : PotPair) (z : ℂ) : Continuous (aW φ z) :=
  (continuous_expW z).mul (cont_M1fun φ z).norm

theorem continuous_nW (φ : PotPair) (z : ℂ) : Continuous (nW φ z) :=
  (continuous_expW z).mul (cont_Nfun φ z).norm

theorem continuous_YW (φ : PotPair) (z : ℂ) : Continuous (YW φ z) :=
  (continuous_expW z).mul (cont_Xfun φ z).norm

theorem aW_nonneg (φ : PotPair) (z : ℂ) (s : ℝ) : 0 ≤ aW φ z s :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem nW_nonneg (φ : PotPair) (z : ℂ) (s : ℝ) : 0 ≤ nW φ z s :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem YW_le (φ : PotPair) (z : ℂ) (s : ℝ) : YW φ z s ≤ aW φ z s + nW φ z s := by
  have h : ‖Xfun φ z s‖ ≤ ‖M1fun φ z s‖ + ‖Nfun φ z s‖ := by
    have : Xfun φ z s = M1fun φ z s + Nfun φ z s := by simp [Nfun]
    rw [this]
    exact norm_add_le _ _
  unfold YW aW nW
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-! ### The integral inequality -/

theorem n_le_integral (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ ∫ s in (0 : ℝ)..t, YW φ z s * omegaW φ s := by
  have hωt : IntervalIntegrable (omegaW φ) volume 0 t :=
    (intervalIntegrable_omegaW φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hcont : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖ :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (cont_Xfun φ z).norm
  have hh : IntervalIntegrable (fun s => (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) *
      omegaW φ s) volume 0 t := hωt.continuousOn_mul hcont.continuousOn
  have hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖kerT φ z t s‖ ≤
      (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) * omegaW φ s := by
    intro s hs
    have hts : 0 ≤ t - s := sub_nonneg.2 hs.2
    unfold kerT
    calc ‖freeE z (t - s) * potCoeff38 φ s * Xfun φ z s‖
        ≤ ‖freeE z (t - s) * potCoeff38 φ s‖ * ‖Xfun φ z s‖ := norm_mul_le _ _
      _ ≤ (‖freeE z (t - s)‖ * ‖potCoeff38 φ s‖) * ‖Xfun φ z s‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (Real.exp (|z.im| * (t - s)) * omegaW φ s) * ‖Xfun φ z s‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul (norm_freeE_le z hts) (norm_potCoeff38_le_omega φ s)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hN := norm_matrix_integral_le ht.1 (ker_integrable φ z ht) hh hb
  rw [← stepB φ z ht] at hN
  unfold nW
  calc Real.exp (-|z.im| * t) * ‖Nfun φ z t‖
      ≤ Real.exp (-|z.im| * t) * ∫ s in (0 : ℝ)..t,
          (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) * omegaW φ s :=
        mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
    _ = ∫ s in (0 : ℝ)..t, YW φ z s * omegaW φ s := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [YW]
        rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
        have e : -|z.im| * t + |z.im| * (t - s) = -|z.im| * s := by ring
        rw [e]

/-! ### Gronwall step -/

theorem Icc_sub_Icc_one {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩

theorem intervalIntegrable_omegaW_on (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (omegaW φ) volume 0 t :=
  (intervalIntegrable_omegaW φ).mono_set (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl ht.2)

/-- `∫₀ᵗ ω a`. -/
def bW (φ : PotPair) (z : ℂ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, omegaW φ s * aW φ z s

theorem intervalIntegrable_omega_mul {φ : PotPair} {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => omegaW φ s * g s) volume 0 t :=
  (intervalIntegrable_omegaW_on φ ht).mul_continuousOn hg.continuousOn

theorem n_le_b_add_Q (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ bW φ z t + ∫ s in (0 : ℝ)..t, omegaW φ s * nW φ z s := by
  refine (n_le_integral φ z ht).trans ?_
  have hia := intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht
  have hin := intervalIntegrable_omega_mul (φ := φ) (continuous_nW φ z) ht
  unfold bW
  rw [← intervalIntegral.integral_add hia hin]
  have hY : IntervalIntegrable (fun s => YW φ z s * omegaW φ s) volume 0 t :=
    (intervalIntegrable_omegaW_on φ ht).continuousOn_mul (continuous_YW φ z).continuousOn
  refine intervalIntegral.integral_mono_on ht.1 hY (hia.add hin) fun s hs => ?_
  have := YW_le φ z s
  have hω := omegaW_nonneg φ s
  nlinarith

theorem bW_mono (φ : PotPair) (z : ℂ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : bW φ z s ≤ bW φ z t := by
  unfold bW
  refine intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 ?_
    (intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht)
  exact Eventually.of_forall fun r => mul_nonneg (omegaW_nonneg φ r) (aW_nonneg φ z r)

theorem n_le_gronwall (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ bW φ z t * Real.exp (∫ r in (0 : ℝ)..t, omegaW φ r) := by
  refine gronwall_integral ht.1 (ω := omegaW φ) (n := nW φ z)
    (fun s _ => omegaW_nonneg φ s) (intervalIntegrable_omegaW_on φ ht)
    (continuous_nW φ z).continuousOn (bW φ z t) fun s hs => ?_
  have h1 := n_le_b_add_Q φ z (Icc_sub_Icc_one hs ht)
  have h2 := bW_mono φ z hs ht
  linarith

/-! ### Cauchy-Schwarz -/

theorem cs_integral {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun s => f s ^ 2) volume 0 t)
    (hg : IntervalIntegrable (fun s => g s ^ 2) volume 0 t)
    (hfg : IntervalIntegrable (fun s => f s * g s) volume 0 t) :
    (∫ s in (0 : ℝ)..t, f s * g s) ^ 2 ≤
      (∫ s in (0 : ℝ)..t, f s ^ 2) * ∫ s in (0 : ℝ)..t, g s ^ 2 := by
  have key : ∀ x : ℝ, 0 ≤ (∫ s in (0 : ℝ)..t, f s ^ 2) * (x * x) +
      (-2 * ∫ s in (0 : ℝ)..t, f s * g s) * x + ∫ s in (0 : ℝ)..t, g s ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..t, (x * f s - g s) ^ 2 :=
      intervalIntegral.integral_nonneg ht fun s _ => sq_nonneg _
    have e : ∫ s in (0 : ℝ)..t, (x * f s - g s) ^ 2 =
        (∫ s in (0 : ℝ)..t, f s ^ 2) * (x * x) +
          (-2 * ∫ s in (0 : ℝ)..t, f s * g s) * x + ∫ s in (0 : ℝ)..t, g s ^ 2 := by
      have e1 : ∀ s, (x * f s - g s) ^ 2 =
          (x * x) * f s ^ 2 + (-2 * x) * (f s * g s) + g s ^ 2 := fun s => by ring
      simp_rw [e1]
      rw [intervalIntegral.integral_add ((hf.const_mul (x * x)).add (hfg.const_mul (-2 * x))) hg,
        intervalIntegral.integral_add (hf.const_mul (x * x)) (hfg.const_mul (-2 * x)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem W_le (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ r in (0 : ℝ)..t, omegaW φ r ≤ Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) := by
  have hf : IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 t :=
    (intervalIntegrable_omegaW_sq φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hg : IntervalIntegrable (fun s : ℝ => (1 : ℝ) ^ 2) volume 0 t := intervalIntegrable_const
  have hfg : IntervalIntegrable (fun s => omegaW φ s * 1) volume 0 t := by
    simpa using intervalIntegrable_omegaW_on φ ht
  have h := cs_integral ht.1 hf hg hfg
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  have hsq : ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    rw [← integral_omegaW_sq φ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ (intervalIntegrable_omegaW_sq φ)
    exact Eventually.of_forall fun r => sq_nonneg _
  have hP : 0 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by positivity
  have h3 : (∫ r in (0 : ℝ)..t, omegaW φ r) ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    have hI : 0 ≤ ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
    nlinarith [ht.2, ht.1]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

theorem b_le (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    bW φ z t ≤ Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) *
      Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2) := by
  have hf : IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 t :=
    (intervalIntegrable_omegaW_sq φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hg : IntervalIntegrable (fun s => aW φ z s ^ 2) volume 0 t :=
    ((continuous_aW φ z).pow 2).intervalIntegrable 0 t
  have hfg := intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht
  have h := cs_integral ht.1 hf hg hfg
  have hsq : ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    rw [← integral_omegaW_sq φ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ (intervalIntegrable_omegaW_sq φ)
    exact Eventually.of_forall fun r => sq_nonneg _
  have hJ : 0 ≤ ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have hP : 0 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by positivity
  have h3 : (bW φ z t) ^ 2 ≤ (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
    h.trans (mul_le_mul_of_nonneg_right hsq hJ)
  rw [← Real.sqrt_mul hP]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

/-! ### Assembly -/

theorem aW_eq_term (φ : PotPair) (z : ℂ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖ = aW φ z s := by
  rw [term1_eq φ z hs]; rfl

theorem G1016_whole :
    ((∀ (φ : PotPair) (z : ℂ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    IntervalIntegrable
      (fun s : ℝ => (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2)
      MeasureTheory.volume 0 t ∧
    Real.exp (-|z.im| * t) *
        ‖(∑' n : ℕ, potentialVolterraTerm38 φ z n t) - freeZsFundamentalComplex z t‖ ≤
      Real.exp (-|z.im| * t) * ‖potentialVolterraTerm38 φ z 1 t‖ +
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2))) *
          Real.sqrt (∫ s in (0 : ℝ)..t,
            (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2)
  : Prop)) := by
  intro φ z t ht0 ht1
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hcongr : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2 = aW φ z s ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [aW_eq_term φ z (Icc_sub_Icc_one hs ht)]
  refine ⟨?_, ?_⟩
  · refine (((continuous_aW φ z).pow 2).intervalIntegrable 0 t).congr ?_
    intro s hs
    exact (hcongr s (Set.uIoc_subset_uIcc hs)).symm
  · have hI : (∫ s in (0 : ℝ)..t,
        (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2) =
        ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
      intervalIntegral.integral_congr hcongr
    rw [hI, aW_eq_term φ z ht, tsum_eq_Mfun φ z ht, ← freeE_eq]
    have hY : Real.exp (-|z.im| * t) * ‖Mfun φ z t - freeE z t‖ = YW φ z t := rfl
    rw [hY]
    have h1 := YW_le φ z t
    have h2 := n_le_gronwall φ z ht
    have h3 := b_le φ z ht
    have h4 := W_le φ ht
    have hb0 : 0 ≤ bW φ z t := intervalIntegral.integral_nonneg ht0 fun s _ =>
      mul_nonneg (omegaW_nonneg φ s) (aW_nonneg φ z s)
    have h5 : bW φ z t * Real.exp (∫ r in (0 : ℝ)..t, omegaW φ r) ≤
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2)) *
          Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)) :=
      mul_le_mul h3 (Real.exp_le_exp.2 h4) (Real.exp_pos _).le
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h6 : (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2)) *
          Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)) =
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2))) *
          Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2) := by ring
    rw [h6] at h5
    linarith

end

end NlsGge.Atomic.G1020S1.K19.K16

end

open MeasureTheory Filter Topology Set
open NlsGge.GK38
/-! ### The first Volterra term -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1020S1.K19.Aux

noncomputable section

theorem term1_apply (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) (i j : Fin 2) :
    freeKernelVolterraTerm38 a b z 1 t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * rawPotCoeff38 a b s * freeE z s) i j := by
  simp only [freeKernelVolterraTerm38, freeE_eq]

theorem term1_entry01 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 0 1 =
      Complex.I * Complex.exp (-(Complex.I * z * (t : ℂ))) *
        ∫ s in (0 : ℝ)..t, a s * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
  rw [term1_apply,
    ← intervalIntegral.integral_const_mul (Complex.I * Complex.exp (-(Complex.I * z * (t : ℂ))))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (-(Complex.I * z * ((t - s : ℝ) : ℂ))) * Complex.exp (Complex.I * z * (s : ℂ)) =
      Complex.exp (-(Complex.I * z * (t : ℂ))) * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  linear_combination (Complex.I * a s) * e

theorem term1_entry10 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 1 0 =
      -Complex.I * Complex.exp (Complex.I * z * (t : ℂ)) *
        ∫ s in (0 : ℝ)..t, b s * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
  rw [term1_apply,
    ← intervalIntegral.integral_const_mul (-Complex.I * Complex.exp (Complex.I * z * (t : ℂ)))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (Complex.I * z * ((t - s : ℝ) : ℂ)) * Complex.exp (-(Complex.I * z * (s : ℂ))) =
      Complex.exp (Complex.I * z * (t : ℂ)) * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  linear_combination (-(Complex.I * b s)) * e

theorem term1_entry00 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 0 0 = 0 := by
  rw [term1_apply]
  simp [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem term1_entry11 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 1 1 = 0 := by
  rw [term1_apply]
  simp [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_term1_le (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    ‖freeKernelVolterraTerm38 a b z 1 t‖ ≤
      max (‖freeKernelVolterraTerm38 a b z 1 t 0 1‖) (‖freeKernelVolterraTerm38 a b z 1 t 1 0‖) := by
  refine NlsGge.Atomic.G1020S1.K19.K16.odd_sparse_matrix_opNorm_le _ _ (le_max_of_le_left (norm_nonneg _))
    (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact term1_entry00 a b z t
    · exact term1_entry11 a b z t
  · fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _


end

end NlsGge.Atomic.G1020S1.K19.Aux

namespace NlsGge.Atomic.G1020S1.K19.Aux

noncomputable section

theorem entry01_osc (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 0 1 = Complex.I * seqOsc38 a (-z) t := by
  rw [term1_entry01, seqOsc38, mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (Complex.I * (-z) * ((t - 2 * s : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * z * (t : ℂ))) * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [e]
  ring

theorem entry10_osc (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 1 0 = -Complex.I * seqOsc38 b z t := by
  rw [term1_entry10, seqOsc38, mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (Complex.I * z * ((t - 2 * s : ℝ) : ℂ)) =
      Complex.exp (Complex.I * z * (t : ℂ)) * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [e]
  ring

theorem W_sq_le (a b : ℝ → ℂ) (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    (Real.exp (-|z.im| * s) * ‖freeKernelVolterraTerm38 a b z 1 s‖) ^ 2 ≤
      ‖seqOsc38 a (-z) s‖ ^ 2 + ‖seqOsc38 b z s‖ ^ 2 := by
  have hexp : Real.exp (-|z.im| * s) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith [abs_nonneg z.im]
  have hN := norm_term1_le a b z s
  rw [entry01_osc, entry10_osc, norm_mul, norm_mul, Complex.norm_I, one_mul] at hN
  simp only [norm_neg, Complex.norm_I, one_mul] at hN
  set x := ‖freeKernelVolterraTerm38 a b z 1 s‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have h1 : (Real.exp (-|z.im| * s) * x) ^ 2 ≤ x ^ 2 := by
    have : Real.exp (-|z.im| * s) * x ≤ x := by nlinarith
    exact pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hx0) this 2
  have h2 : x ^ 2 ≤ ‖seqOsc38 a (-z) s‖ ^ 2 + ‖seqOsc38 b z s‖ ^ 2 := by
    rcases max_cases ‖seqOsc38 a (-z) s‖ ‖seqOsc38 b z s‖ with ⟨hm, _⟩ | ⟨hm, _⟩
    · have : x ≤ ‖seqOsc38 a (-z) s‖ := hm ▸ hN
      nlinarith [norm_nonneg (seqOsc38 b z s)]
    · have : x ≤ ‖seqOsc38 b z s‖ := hm ▸ hN
      nlinarith [norm_nonneg (seqOsc38 a (-z) s)]
  exact h1.trans h2

end

end NlsGge.Atomic.G1020S1.K19.Aux

namespace NlsGge.Atomic.G1020S1.K19.Aux

noncomputable section

open NlsGge.Pilot

theorem bessel_fin_b (f : PhysicalL2) (ξ : ℤ → ℂ) {R1 : ℝ}
    (hR : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset ℤ) :
    ∑ n ∈ S, ‖seqOsc38 (coverRep38 f) (ξ n) s‖ ^ 2 ≤ Real.exp (2 * R1) * ‖f‖ ^ 2 := by
  have h := NlsGge.Atomic.G1015.perturbed_fourier_bessel_physical f
    (fun n : ℤ => ξ n - (n : ℂ) * (Real.pi : ℂ)) hR hs
  simp only [add_sub_cancel] at h
  exact (Summable.sum_le_tsum S (fun n _ => sq_nonneg _) h.1).trans h.2

theorem bessel_fin_a (f : PhysicalL2) (ξ : ℤ → ℂ) {R1 : ℝ}
    (hR : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset ℤ) :
    ∑ n ∈ S, ‖seqOsc38 (coverRep38 f) (-ξ n) s‖ ^ 2 ≤ Real.exp (2 * R1) * ‖f‖ ^ 2 := by
  have hα : ∀ m : ℤ, ‖(-ξ (-m) - (m : ℂ) * (Real.pi : ℂ))‖ ≤ R1 := by
    intro m
    have := hR (-m)
    have e : -ξ (-m) - (m : ℂ) * (Real.pi : ℂ) = -(ξ (-m) - ((-m : ℤ) : ℂ) * (Real.pi : ℂ)) := by
      push_cast; ring
    rw [e, norm_neg]
    exact this
  have h := NlsGge.Atomic.G1015.perturbed_fourier_bessel_physical f
    (fun m : ℤ => -ξ (-m) - (m : ℂ) * (Real.pi : ℂ)) hα hs
  simp only [add_sub_cancel] at h
  have hle : ∑ m ∈ S.image (fun n : ℤ => -n), ‖seqOsc38 (coverRep38 f) (-ξ (-m)) s‖ ^ 2 ≤
      ∑' m : ℤ, ‖seqOsc38 (coverRep38 f) (-ξ (-m)) s‖ ^ 2 :=
    Summable.sum_le_tsum _ (fun m _ => sq_nonneg _) h.1
  rw [Finset.sum_image (fun x _ y _ hxy => neg_injective hxy)] at hle
  simp only [neg_neg] at hle
  exact hle.trans h.2

end

end NlsGge.Atomic.G1020S1.K19.Aux

namespace NlsGge.Atomic.G1020S1.K19

noncomputable section

open NlsGge.Atomic.G1020S1.K19.Aux
open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

theorem G1019_whole : ((
  ∀ R0 R1 : ℝ, ∃ C : ℝ, ∀ (φ : PotPair) (ξ : ℤ → ℂ),
    Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 →
    (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Summable (fun n : ℤ =>
        ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ ^ 2) ∧
      (∑' n : ℤ,
        ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ ^ 2) ≤ C
  : Prop)) := by
  intro R0 R1
  set R0' : ℝ := max R0 0 with hR0'
  set R1' : ℝ := max R1 0 with hR1'
  have hR1p : 0 ≤ R1' := le_max_right _ _
  have hR0p : 0 ≤ R0' := le_max_right _ _
  refine ⟨2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * R0' ^ 2 +
    R0' ^ 2 * Real.exp (2 * R0') * (Real.exp (2 * R1') * R0' ^ 2)), ?_⟩
  intro φ ξ hφ hξ t ht0 ht1
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  set c : ℝ := Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcR : c ≤ R0' := hφ.trans (le_max_left _ _)
  have hc2 : c ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hξ' : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1' :=
    fun n => (hξ n).trans (le_max_left _ _)
  have himR : ∀ n : ℤ, |(ξ n).im| ≤ R1' := by
    intro n
    refine le_trans ?_ (hξ' n)
    have := Complex.abs_im_le_norm (ξ n - (n : ℂ) * (Real.pi : ℂ))
    simpa using this
  set Wf : ℤ → ℝ → ℝ := fun n s =>
    Real.exp (-|(ξ n).im| * s) * ‖potentialVolterraTerm38 φ (ξ n) 1 s‖ with hWf
  set X : ℤ → ℝ := fun n =>
    ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ with hX
  have hK : ∀ n : ℤ, IntervalIntegrable (fun s => Wf n s ^ 2) MeasureTheory.volume 0 t ∧
      Real.exp (-|(ξ n).im| * t) * X n ≤ Wf n t + (c * Real.exp c) *
        Real.sqrt (∫ s in (0 : ℝ)..t, Wf n s ^ 2) :=
    fun n => K16.G1016_whole φ (ξ n) t ht0 ht1
  set Ib : ℤ → ℝ := fun n => ∫ s in (0 : ℝ)..t, Wf n s ^ 2 with hIb
  have hIb0 : ∀ n, 0 ≤ Ib n := fun n =>
    intervalIntegral.integral_nonneg ht0 fun s _ => sq_nonneg _
  have hWf0 : ∀ n s, 0 ≤ Wf n s := fun n s => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  -- pointwise bound for one index
  have hXn : ∀ n : ℤ, X n ^ 2 ≤ 2 * Real.exp (2 * R1') * (Wf n t ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) := by
    intro n
    have h1 := (hK n).2
    have hexp : Real.exp (|(ξ n).im| * t) ≤ Real.exp R1' := by
      apply Real.exp_le_exp.2
      calc |(ξ n).im| * t ≤ |(ξ n).im| * 1 :=
            mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)
        _ ≤ R1' := by simpa using himR n
    have hXle : X n ≤ Real.exp R1' * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n)) := by
      have hw : Real.exp (|(ξ n).im| * t) * Real.exp (-|(ξ n).im| * t) = 1 := by
        rw [← Real.exp_add]; simp
      have h2 : X n = Real.exp (|(ξ n).im| * t) * (Real.exp (-|(ξ n).im| * t) * X n) := by
        rw [← mul_assoc, hw, one_mul]
      have hnn : 0 ≤ Wf n t + (c * Real.exp c) * Real.sqrt (Ib n) := by
        have := hWf0 n t
        positivity
      calc X n = Real.exp (|(ξ n).im| * t) * (Real.exp (-|(ξ n).im| * t) * X n) := h2
        _ ≤ Real.exp (|(ξ n).im| * t) * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ Real.exp R1' * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n)) :=
            mul_le_mul_of_nonneg_right hexp hnn
    have hX0 : 0 ≤ X n := norm_nonneg _
    have hsq : X n ^ 2 ≤ (Real.exp R1' * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n))) ^ 2 :=
      pow_le_pow_left₀ hX0 hXle 2
    have hsqrt : Real.sqrt (Ib n) ^ 2 = Ib n := Real.sq_sqrt (hIb0 n)
    have he2 : Real.exp R1' ^ 2 = Real.exp (2 * R1') := by rw [← Real.exp_nat_mul]; norm_num
    have he2c : Real.exp c ^ 2 = Real.exp (2 * c) := by rw [← Real.exp_nat_mul]; norm_num
    have hu := hWf0 n t
    set u := Wf n t
    set v := (c * Real.exp c) * Real.sqrt (Ib n) with hv
    have hv2 : v ^ 2 = c ^ 2 * Real.exp (2 * c) * Ib n := by
      rw [hv, mul_pow, mul_pow, hsqrt, he2c]
    calc X n ^ 2 ≤ (Real.exp R1' * (u + v)) ^ 2 := hsq
      _ = Real.exp (2 * R1') * (u + v) ^ 2 := by rw [mul_pow, he2]
      _ ≤ Real.exp (2 * R1') * (2 * (u ^ 2 + v ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          nlinarith [sq_nonneg (u - v)]
      _ = 2 * Real.exp (2 * R1') * (u ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) := by
          rw [hv2]; ring
  -- sums over finite sets
  have hpt : ∀ (S : Finset ℤ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) t →
      ∑ n ∈ S, Wf n s ^ 2 ≤ Real.exp (2 * R1') * c ^ 2 := by
    intro S s hs
    have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht1⟩
    have h1 : ∑ n ∈ S, Wf n s ^ 2 ≤
        ∑ n ∈ S, (‖seqOsc38 (coverRep38 φ.1) (-ξ n) s‖ ^ 2 + ‖seqOsc38 (coverRep38 φ.2) (ξ n) s‖ ^ 2) :=
      Finset.sum_le_sum fun n _ => W_sq_le (potRepFst38 φ) (potRepSnd38 φ) (ξ n) hs.1
    rw [Finset.sum_add_distrib] at h1
    have ha := bessel_fin_a φ.1 ξ hξ' hs1 S
    have hb := bessel_fin_b φ.2 ξ hξ' hs1 S
    rw [hc2]
    nlinarith
  have hint : ∀ S : Finset ℤ, ∑ n ∈ S, Ib n ≤ Real.exp (2 * R1') * c ^ 2 := by
    intro S
    have hI : ∑ n ∈ S, Ib n = ∫ s in (0 : ℝ)..t, ∑ n ∈ S, Wf n s ^ 2 := by
      rw [intervalIntegral.integral_finset_sum]
      intro n _
      exact (hK n).1
    rw [hI]
    have hsumint : IntervalIntegrable (fun s => ∑ n ∈ S, Wf n s ^ 2) MeasureTheory.volume 0 t := by
      have := IntervalIntegrable.sum S fun n _ => (hK n).1
      simpa only [Finset.sum_fn] using this
    have := intervalIntegral.integral_mono_on ht0 hsumint
      (intervalIntegrable_const (c := Real.exp (2 * R1') * c ^ 2)) (fun s hs => hpt S s hs)
    refine this.trans ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hp : 0 ≤ Real.exp (2 * R1') * c ^ 2 := by positivity
    nlinarith
  have hsum : ∀ S : Finset ℤ, ∑ n ∈ S, X n ^ 2 ≤
      2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * R0' ^ 2 +
        R0' ^ 2 * Real.exp (2 * R0') * (Real.exp (2 * R1') * R0' ^ 2)) := by
    intro S
    have h1 : ∑ n ∈ S, X n ^ 2 ≤
        ∑ n ∈ S, 2 * Real.exp (2 * R1') * (Wf n t ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) :=
      Finset.sum_le_sum fun n _ => hXn n
    have h2 : ∑ n ∈ S, 2 * Real.exp (2 * R1') * (Wf n t ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) =
        2 * Real.exp (2 * R1') * (∑ n ∈ S, Wf n t ^ 2 +
          c ^ 2 * Real.exp (2 * c) * ∑ n ∈ S, Ib n) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h3 := hpt S t ⟨ht0, le_rfl⟩
    have h4 := hint S
    have hE : 0 < Real.exp (2 * R1') := Real.exp_pos _
    have hmono : 2 * Real.exp (2 * R1') * (∑ n ∈ S, Wf n t ^ 2 +
          c ^ 2 * Real.exp (2 * c) * ∑ n ∈ S, Ib n) ≤
        2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * c ^ 2 +
          c ^ 2 * Real.exp (2 * c) * (Real.exp (2 * R1') * c ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh : c ^ 2 * Real.exp (2 * c) * ∑ n ∈ S, Ib n ≤
          c ^ 2 * Real.exp (2 * c) * (Real.exp (2 * R1') * c ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    have hcc : 2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * c ^ 2 +
          c ^ 2 * Real.exp (2 * c) * (Real.exp (2 * R1') * c ^ 2)) ≤
        2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * R0' ^ 2 +
          R0' ^ 2 * Real.exp (2 * R0') * (Real.exp (2 * R1') * R0' ^ 2)) := by
      have hc2' : c ^ 2 ≤ R0' ^ 2 := pow_le_pow_left₀ hc0 hcR 2
      have hec : Real.exp (2 * c) ≤ Real.exp (2 * R0') := Real.exp_le_exp.2 (by linarith)
      gcongr
    exact h1.trans (h2 ▸ (hmono.trans hcc))
  have hsumm : Summable (fun n : ℤ => X n ^ 2) :=
    summable_of_sum_le (fun n => sq_nonneg _) hsum
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le hsum⟩

end

end NlsGge.Atomic.G1020S1.K19

end

namespace NlsGge.Atomic.G1020S1

noncomputable section

open MeasureTheory Filter Topology Set
open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

theorem differentiableAt_M (ψ : PotPair) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z := by
  have h := NlsGge.Atomic.G1004GenT.analytic_all t ht (z, ψ) (Set.mem_univ _)
  have hc : AnalyticAt ℂ (fun w : ℂ => (w, ψ)) z :=
    analyticAt_id.prod analyticAt_const
  have h2 := AnalyticAt.comp (g := fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
    (f := fun w : ℂ => (w, ψ)) (x := z) h hc
  exact h2.differentiableAt

theorem differentiable_E (t : ℝ) : Differentiable ℂ (fun w : ℂ => freeZsFundamentalComplex w t) := by
  intro z
  have h : AnalyticAt ℂ (fun w : ℂ => freeE w t) z := by
    refine NlsGge.Atomic.G1004GenT.analyticAt_of_entries fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [freeE] <;> fun_prop
  have e : (fun w : ℂ => freeZsFundamentalComplex w t) = fun w => freeE w t := by
    funext w; exact (freeE_eq w t).symm
  rw [e]
  exact h.differentiableAt

/-- Cauchy's estimate in mean-square form on the unit circle. -/
theorem cauchy_sq_bound {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    ‖deriv f c‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ ^ 2 := by
  have hI := (hf.diffContOnCl (s := Metric.ball c 1)).deriv_eq_smul_circleIntegral (c := c)
    (R := 1) one_pos
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcont : Continuous fun θ : ℝ => ‖f (circleMap c 1 θ)‖ :=
    (hf.continuous.comp (continuous_circleMap c 1)).norm
  have hnorm : ‖(2 * Real.pi * Complex.I) • deriv f c‖ = 2 * Real.pi * ‖deriv f c‖ := by
    rw [norm_smul]
    congr 1
    simp [Complex.norm_mul, abs_of_pos Real.pi_pos]
  have hle : ‖∮ z in C(c, 1), (1 / (z - c) ^ 2) • f z‖ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ := by
    rw [circleIntegral]
    refine (intervalIntegral.norm_integral_le_integral_norm hpi.le).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one]
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp
    have h2 : ‖1 / (circleMap c 1 θ - c) ^ 2‖ = 1 := by
      rw [norm_div, norm_pow, norm_one]
      have : circleMap c 1 θ - c = circleMap 0 1 θ := by simp [circleMap]
      rw [this, h1]; simp
    simp only [h1, h2, one_mul]
  have hB : 2 * Real.pi * ‖deriv f c‖ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ := by
    rw [← hnorm, ← hI]; exact hle
  have hcs := NlsGge.Atomic.G1020S1.K19.K16.cs_integral (t := 2 * Real.pi) hpi.le
    (f := fun θ => ‖f (circleMap c 1 θ)‖) (g := fun _ => (1 : ℝ))
    ((hcont.pow 2).intervalIntegrable 0 _) (by simpa using intervalIntegrable_const)
    (by simpa using hcont.intervalIntegrable 0 (2 * Real.pi))
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hcs
  have hd0 : 0 ≤ 2 * Real.pi * ‖deriv f c‖ := by positivity
  have h3 : (2 * Real.pi * ‖deriv f c‖) ^ 2 ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ ^ 2) * (2 * Real.pi) :=
    (pow_le_pow_left₀ hd0 hB 2).trans hcs
  rw [inv_mul_eq_div, le_div_iff₀ hpi]
  nlinarith [h3]

theorem G1020_whole : ((
  ∀ R0 R1 : ℝ, ∃ C : ℝ, ∀ (φ : PotPair) (ξ : ℤ → ℂ),
    Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 →
    (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ n : ℤ, DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n)) ∧
      Summable (fun n : ℤ =>
        ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
            deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ^ 2) ∧
      (∑' n : ℤ,
        ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
            deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ^ 2) ≤ C
  : Prop)) := by
  intro R0 R1
  obtain ⟨C, hC⟩ := K19.G1019_whole R0 (R1 + 1)
  refine ⟨C, ?_⟩
  intro φ ξ hφ hξ t ht0 ht1
  have hMd : ∀ w : ℂ, DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) w :=
    fun w => differentiableAt_M φ ht0 w
  refine ⟨fun n => hMd (ξ n), ?_⟩
  set f : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w =>
    (∑' m : ℕ, potentialVolterraTerm38 φ w m t) - freeZsFundamentalComplex w t with hf
  have hfd : Differentiable ℂ f := fun w => (hMd w).sub (differentiable_E t w)
  have hderiv : ∀ n : ℤ, deriv f (ξ n) =
      deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
        deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n) := fun n =>
    deriv_sub (hMd (ξ n)) (differentiable_E t (ξ n))
  have hcirc : ∀ θ : ℝ, ∀ S : Finset ℤ,
      ∑ n ∈ S, ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 ≤ C := by
    intro θ S
    have hξθ : ∀ n : ℤ, ‖(fun n => circleMap (ξ n) 1 θ) n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 + 1 := by
      intro n
      have e : circleMap (ξ n) 1 θ - (n : ℂ) * (Real.pi : ℂ) =
          (ξ n - (n : ℂ) * (Real.pi : ℂ)) + circleMap 0 1 θ := by
        simp [circleMap]; ring
      show ‖circleMap (ξ n) 1 θ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 + 1
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp
      linarith [hξ n]
    obtain ⟨hs, hb⟩ := hC φ (fun n => circleMap (ξ n) 1 θ) hφ hξθ t ht0 ht1
    exact (Summable.sum_le_tsum S (fun n _ => sq_nonneg _) hs).trans hb
  have hpi : 0 < 2 * Real.pi := by positivity
  have hgc : ∀ n : ℤ, Continuous fun θ : ℝ => ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 := fun n =>
    ((hfd.continuous.comp (continuous_circleMap (ξ n) 1)).norm).pow 2
  have hsum : ∀ S : Finset ℤ, ∑ n ∈ S, ‖deriv f (ξ n)‖ ^ 2 ≤ C := by
    intro S
    have h1 : ∑ n ∈ S, ‖deriv f (ξ n)‖ ^ 2 ≤
        ∑ n ∈ S, (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 :=
      Finset.sum_le_sum fun n _ => cauchy_sq_bound hfd (ξ n)
    have h2 : ∑ n ∈ S, (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 =
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ n ∈ S, ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 := by
      rw [← Finset.mul_sum, intervalIntegral.integral_finset_sum]
      intro n _
      exact (hgc n).intervalIntegrable 0 _
    have hint : ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ n ∈ S, ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi), C := by
      refine intervalIntegral.integral_mono_on hpi.le ?_ intervalIntegrable_const fun θ _ => hcirc θ S
      exact (continuous_finset_sum _ fun n _ => hgc n).intervalIntegrable 0 _
    have h3 : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), C = C := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      field_simp
    calc ∑ n ∈ S, ‖deriv f (ξ n)‖ ^ 2 ≤ _ := h1
      _ = _ := h2
      _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), C :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = C := h3
  have hsumm : Summable (fun n : ℤ => ‖deriv f (ξ n)‖ ^ 2) :=
    summable_of_sum_le (fun n => sq_nonneg _) hsum
  have hrw : (fun n : ℤ => ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ^ 2) =
      fun n : ℤ => ‖deriv f (ξ n)‖ ^ 2 := by
    funext n; rw [hderiv n]
  rw [hrw]
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le hsum⟩

end

end NlsGge.Atomic.G1020S1
