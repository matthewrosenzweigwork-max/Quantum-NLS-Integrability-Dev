/- G1-021 PRODUCTION02 (proof development batch-8 landing kit). Source: proof development/G1021_PROOF_T3.lean.txt. #check/#print lines removed; original namespaces kept. No acceptance claimed. -/
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential

/- G1-018 pre-approval proof candidate (proof development, AUTHOR; not reviewed).  Statement = proof development's G1018_COMMAND04.
   Route (GK Thm 2.3): (a,b) are continuous 1-periodic, hence the cover representatives of an element phi of PotPair
   (private lift); the Volterra terms agree; G1-016 (private copy of proof development's G1016_PROOF01) bounds
   the weighted ||M-E|| by ||F|| + c e^c (int ||F||^2)^{1/2} with F = M_1; integration by parts bounds F by 3||phi||_{H1}/|z|. -/

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

namespace NlsGge.Atomic.G1021S2.K18.K16

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

end NlsGge.Atomic.G1021S2.K18.K16

end

/-! ### Complex absolutely continuous functions: fundamental theorem of calculus -/

open MeasureTheory Filter Topology Set

namespace NlsGge.Atomic.G1021S2.K18.Aux

noncomputable section

theorem ac_re {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x).re) a b :=
  (Complex.reCLM.lipschitz).comp_absolutelyContinuousOnInterval hf

theorem ac_im {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x).im) a b :=
  (Complex.imCLM.lipschitz).comp_absolutelyContinuousOnInterval hf

theorem ac_ae_differentiableAt {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x : ℝ, x ∈ uIcc a b → DifferentiableAt ℝ f x := by
  filter_upwards [(ac_re hf).ae_differentiableAt, (ac_im hf).ae_differentiableAt] with x h1 h2 hx
  have hre := h1 hx
  have him := h2 hx
  have h : DifferentiableAt ℝ (fun x => ((f x).re : ℂ) + ((f x).im : ℂ) * Complex.I) x :=
    (Complex.ofRealCLM.differentiableAt.comp x hre).add
      ((Complex.ofRealCLM.differentiableAt.comp x him).mul_const _)
  have e : (fun x => ((f x).re : ℂ) + ((f x).im : ℂ) * Complex.I) = f := by
    funext y; exact Complex.re_add_im (f y)
  rwa [e] at h

theorem deriv_re {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    deriv (fun y => (f y).re) x = (deriv f x).re :=
  ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt)).deriv

theorem deriv_im {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    deriv (fun y => (f y).im) x = (deriv f x).im :=
  ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt)).deriv

theorem ac_complex_ftc {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b ∧ ∫ x in a..b, deriv f x = f b - f a := by
  have hre := ac_re hf
  have him := ac_im hf
  have ae := ac_ae_differentiableAt hf
  have hae' : ∀ᵐ x ∂(volume.restrict (uIoc a b)), DifferentiableAt ℝ f x :=
    (ae_restrict_iff' measurableSet_uIoc).2
      (ae.mono fun x hx hxI => hx (uIoc_subset_uIcc hxI))
  have e_re : (deriv fun y => (f y).re) =ᵐ[volume.restrict (uIoc a b)] fun x => (deriv f x).re :=
    hae'.mono fun x hx => deriv_re hx
  have e_im : (deriv fun y => (f y).im) =ᵐ[volume.restrict (uIoc a b)] fun x => (deriv f x).im :=
    hae'.mono fun x hx => deriv_im hx
  have hi_re : IntervalIntegrable (fun x => (deriv f x).re) volume a b :=
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hre.intervalIntegrable_deriv).congr e_re)
  have hi_im : IntervalIntegrable (fun x => (deriv f x).im) volume a b :=
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 him.intervalIntegrable_deriv).congr e_im)
  have hd : deriv f = fun x => ((deriv f x).re : ℂ) + ((deriv f x).im : ℂ) * Complex.I := by
    funext x; exact (Complex.re_add_im _).symm
  have hI : IntervalIntegrable (deriv f) volume a b := by
    rw [hd]
    have h1 : IntervalIntegrable (fun x => (((deriv f x).re : ℝ) : ℂ)) volume a b :=
      intervalIntegrable_iff.2 (intervalIntegrable_iff.1 hi_re).ofReal
    have h2 : IntervalIntegrable (fun x => (((deriv f x).im : ℝ) : ℂ)) volume a b :=
      intervalIntegrable_iff.2 (intervalIntegrable_iff.1 hi_im).ofReal
    exact h1.add (h2.mul_const _)
  refine ⟨hI, ?_⟩
  have ir : ∫ x in a..b, (deriv f x).re = (f b).re - (f a).re := by
    rw [← hre.integral_deriv_eq_sub]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_uIoc).1 e_re] with x hx hxI
    exact (hx hxI).symm
  have ii : ∫ x in a..b, (deriv f x).im = (f b).im - (f a).im := by
    rw [← him.integral_deriv_eq_sub]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_uIoc).1 e_im] with x hx hxI
    exact (hx hxI).symm
  have h1 : IntervalIntegrable (fun x => (((deriv f x).re : ℝ) : ℂ)) volume a b :=
    intervalIntegrable_iff.2 (intervalIntegrable_iff.1 hi_re).ofReal
  have h2 : IntervalIntegrable (fun x => (((deriv f x).im : ℝ) : ℂ)) volume a b :=
    intervalIntegrable_iff.2 (intervalIntegrable_iff.1 hi_im).ofReal
  rw [hd, intervalIntegral.integral_add h1 (h2.mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, ir, ii]
  apply Complex.ext <;> simp

end

end NlsGge.Atomic.G1021S2.K18.Aux

/-! ### Sobolev sup bound on `[0,1]` -/

namespace NlsGge.Atomic.G1021S2.K18.Aux

noncomputable section

theorem sqrt_integral_bound {g : ℝ → ℝ} (hg0 : ∀ s, 0 ≤ g s)
    (hg : IntervalIntegrable g volume 0 1)
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume 0 1) :
    ∫ s in (0 : ℝ)..1, g s ≤ Real.sqrt (∫ s in (0 : ℝ)..1, g s ^ 2) := by
  have h := NlsGge.Atomic.G1021S2.K18.K16.cs_integral (t := 1) zero_le_one (f := g) (g := fun _ => (1 : ℝ))
    hg2 (by simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1))
    (by simpa using hg)
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

theorem sup_bound {a : ℝ → ℂ} (ha : AbsolutelyContinuousOnInterval a 0 1)
    (hd : IntervalIntegrable (fun s => ‖deriv a s‖ ^ 2) volume 0 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖a t‖ ≤ Real.sqrt (∫ s in (0 : ℝ)..1, ‖a s‖ ^ 2) +
      Real.sqrt (∫ s in (0 : ℝ)..1, ‖deriv a s‖ ^ 2) := by
  have hu : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hder : IntervalIntegrable (deriv a) volume 0 1 := (ac_complex_ftc ha).1
  have hder_n : IntervalIntegrable (fun s => ‖deriv a s‖) volume 0 1 := hder.norm
  have hac : ContinuousOn a (Set.Icc 0 1) := by
    have := ha.continuousOn
    rwa [hu] at this
  have han : IntervalIntegrable (fun s => ‖a s‖) volume 0 1 :=
    (hac.norm).intervalIntegrable_of_Icc zero_le_one
  have han2 : IntervalIntegrable (fun s => ‖a s‖ ^ 2) volume 0 1 :=
    ((hac.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  set Ida : ℝ := ∫ s in (0 : ℝ)..1, ‖deriv a s‖ with hIda
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖a t‖ ≤ ‖a s‖ + Ida := by
    intro s hs
    have hsub : Set.uIcc s t ⊆ Set.uIcc 0 1 := by
      rw [hu]
      exact Set.uIcc_subset_Icc hs ht
    have hftc := (ac_complex_ftc (ha.mono hsub)).2
    have hn : ‖a t - a s‖ ≤ Ida := by
      rw [← hftc]
      refine intervalIntegral.norm_integral_le_abs_integral_norm.trans ?_
      have h0 : ∀ r ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ‖deriv a r‖ := fun r _ => norm_nonneg _
      have hts : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∫ r in (0 : ℝ)..u, ‖deriv a r‖ ≤ Ida := by
        intro u hu1
        refine intervalIntegral.integral_mono_interval le_rfl hu1.1 hu1.2 ?_ hder_n
        exact Eventually.of_forall fun r => norm_nonneg _
      have hnn : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ∫ r in (0 : ℝ)..u, ‖deriv a r‖ := fun u hu1 =>
        intervalIntegral.integral_nonneg hu1.1 fun r _ => norm_nonneg _
      have hsubu : ∀ u ∈ Set.Icc (0 : ℝ) 1, Set.uIcc 0 u ⊆ Set.uIcc 0 1 := fun u hu1 =>
        Set.uIcc_subset_uIcc left_mem_uIcc (by rw [hu]; exact hu1)
      have hdiff : ∫ r in s..t, ‖deriv a r‖ =
          (∫ r in (0 : ℝ)..t, ‖deriv a r‖) - ∫ r in (0 : ℝ)..s, ‖deriv a r‖ := by
        rw [intervalIntegral.integral_interval_sub_left (hder_n.mono_set (hsubu t ht))
          (hder_n.mono_set (hsubu s hs))]
      rw [hdiff, abs_le]
      have h1 := hts t ht
      have h2 := hts s hs
      have h3 := hnn t ht
      have h4 := hnn s hs
      constructor <;> linarith
    have := norm_sub_norm_le (a t) (a s)
    linarith
  have hint : ‖a t‖ ≤ (∫ s in (0 : ℝ)..1, ‖a s‖) + Ida := by
    calc ‖a t‖ = ∫ s in (0 : ℝ)..1, ‖a t‖ := by simp
      _ ≤ ∫ s in (0 : ℝ)..1, (‖a s‖ + Ida) :=
          intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
            (han.add intervalIntegrable_const) hpt
      _ = (∫ s in (0 : ℝ)..1, ‖a s‖) + Ida := by
          rw [intervalIntegral.integral_add han intervalIntegrable_const]
          simp
  have b1 := sqrt_integral_bound (g := fun s => ‖a s‖) (fun s => norm_nonneg _) han han2
  have b2 := sqrt_integral_bound (g := fun s => ‖deriv a s‖) (fun s => norm_nonneg _) hder_n hd
  linarith

end

end NlsGge.Atomic.G1021S2.K18.Aux

/-! ### Integration by parts for `∫ a e^{2izs}` -/

namespace NlsGge.Atomic.G1021S2.K18.Aux

noncomputable section

theorem exp_phase_hasDerivAt (c : ℂ) (x : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ))) (c * Complex.exp (c * (x : ℂ))) x := by
  have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul c
  simpa [mul_comm] using h1.cexp

theorem norm_exp_phase (z : ℂ) (s : ℝ) : ‖Complex.exp (2 * Complex.I * z * (s : ℂ))‖ =
    Real.exp (-2 * z.im * s) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem ibp_identity {a : ℝ → ℂ} (ha : AbsolutelyContinuousOnInterval a 0 1)
    (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Complex.I * z) * ∫ s in (0 : ℝ)..t, a s * Complex.exp (2 * Complex.I * z * (s : ℂ)) =
      a t * Complex.exp (2 * Complex.I * z * (t : ℂ)) - a 0 -
        ∫ s in (0 : ℝ)..t, deriv a s * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
  set c : ℂ := 2 * Complex.I * z with hc
  set g : ℝ → ℂ := fun s => Complex.exp (c * (s : ℂ)) with hg
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 1 :=
    Set.uIcc_subset_uIcc left_mem_uIcc (by rw [hu1]; exact ht)
  have hgd : ∀ x, HasDerivAt g (c * g x) x := fun x => exp_phase_hasDerivAt c x
  have hgc : Continuous g := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hgac : AbsolutelyContinuousOnInterval g 0 1 := by
    refine ContDiff.contDiffOn ?_ |>.absolutelyContinuousOnInterval
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hhac : AbsolutelyContinuousOnInterval (fun s => a s * g s) 0 1 := by
    have := ha.fun_smul hgac
    simpa [smul_eq_mul] using this
  have hftc := (ac_complex_ftc (hhac.mono hsub)).2
  have hder : IntervalIntegrable (deriv a) volume 0 t :=
    (ac_complex_ftc (ha.mono hsub)).1
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc 0 t →
      deriv (fun s => a s * g s) x = deriv a x * g x + a x * (c * g x) := by
    filter_upwards [ac_ae_differentiableAt (ha.mono hsub)] with x hx hxI
    have hda := (hx (Set.uIoc_subset_uIcc hxI)).hasDerivAt
    exact (hda.mul (hgd x)).deriv
  have hac_c : ContinuousOn a (Set.Icc 0 t) := by
    have := (ha.mono hsub).continuousOn
    rwa [Set.uIcc_of_le ht.1] at this
  have i1 : IntervalIntegrable (fun s => deriv a s * g s) volume 0 t :=
    hder.mul_continuousOn hgc.continuousOn
  have i2 : IntervalIntegrable (fun s => c * (a s * g s)) volume 0 t := by
    have : ContinuousOn (fun s => c * (a s * g s)) (Set.uIcc 0 t) := by
      rw [Set.uIcc_of_le ht.1]
      exact continuousOn_const.mul (hac_c.mul hgc.continuousOn)
    exact this.intervalIntegrable
  have h3 : ∫ s in (0 : ℝ)..t, deriv (fun s => a s * g s) s =
      (∫ s in (0 : ℝ)..t, deriv a s * g s) + c * ∫ s in (0 : ℝ)..t, a s * g s := by
    rw [intervalIntegral.integral_congr_ae (g := fun s => deriv a s * g s + c * (a s * g s))
      (by filter_upwards [hae] with x hx hxI; rw [hx hxI]; ring)]
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul]
  have h4 : (fun s => a s * g s) t - (fun s => a s * g s) 0 =
      (∫ s in (0 : ℝ)..t, deriv a s * g s) + c * ∫ s in (0 : ℝ)..t, a s * g s := by
    rw [← h3, hftc]
  simp only [hg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h4
  have : c * ∫ s in (0 : ℝ)..t, a s * g s =
      a t * g t - a 0 - ∫ s in (0 : ℝ)..t, deriv a s * g s := by
    linear_combination -h4
  exact this

end

end NlsGge.Atomic.G1021S2.K18.Aux

/-! ### The weighted integration-by-parts bound -/

namespace NlsGge.Atomic.G1021S2.K18.Aux

noncomputable section

theorem weight_le_one (y t : ℝ) (ht : 0 ≤ t) {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-|y| * t) * (Real.exp (y * t) * Real.exp (-2 * y * s)) ≤ 1 := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_one_iff.2
  have h1 : y * (t - 2 * s) ≤ |y| * t := by
    calc y * (t - 2 * s) ≤ |y * (t - 2 * s)| := le_abs_self _
      _ = |y| * |t - 2 * s| := abs_mul _ _
      _ ≤ |y| * t := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
        rw [abs_le]; constructor <;> linarith
  nlinarith

theorem weight_le_one' (y t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-|y| * t) * Real.exp (y * t) ≤ 1 := by
  rw [← Real.exp_add]
  apply Real.exp_le_one_iff.2
  have := le_abs_self y
  nlinarith

theorem ibp_bound {a : ℝ → ℂ} (ha : AbsolutelyContinuousOnInterval a 0 1) (z : ℂ) (hz : z ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-|z.im| * t) * (Real.exp (z.im * t) *
        ‖∫ s in (0 : ℝ)..t, a s * Complex.exp (2 * Complex.I * z * (s : ℂ))‖) ≤
      (‖a t‖ + ‖a 0‖ + ∫ s in (0 : ℝ)..t, ‖deriv a s‖) / (2 * ‖z‖) := by
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 1 :=
    Set.uIcc_subset_uIcc left_mem_uIcc (by rw [hu1]; exact ht)
  have hder : IntervalIntegrable (deriv a) volume 0 t := (ac_complex_ftc (ha.mono hsub)).1
  have hgc : Continuous fun s : ℝ => Complex.exp (2 * Complex.I * z * (s : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hid := ibp_identity ha z ht
  set A := ∫ s in (0 : ℝ)..t, a s * Complex.exp (2 * Complex.I * z * (s : ℂ)) with hA
  set W : ℝ := Real.exp (-|z.im| * t) * Real.exp (z.im * t) with hW
  have hz2 : 0 < 2 * ‖z‖ := by positivity
  have hnorm : (2 * ‖z‖) * ‖A‖ ≤ ‖a t‖ * Real.exp (-2 * z.im * t) + ‖a 0‖ +
      ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * Real.exp (-2 * z.im * s) := by
    have h1 : ‖(2 * Complex.I * z) * A‖ = (2 * ‖z‖) * ‖A‖ := by
      rw [norm_mul]; congr 1; simp [norm_mul]
    rw [← h1, hid]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
    · refine add_le_add ?_ le_rfl
      rw [norm_mul, norm_exp_phase]
    · refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      refine le_of_eq (intervalIntegral.integral_congr fun s _ => ?_)
      simp only [norm_mul, norm_exp_phase]
  have hIw : ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * (W * Real.exp (-2 * z.im * s)) ≤
      ∫ s in (0 : ℝ)..t, ‖deriv a s‖ := by
    have hi1 : IntervalIntegrable (fun s => ‖deriv a s‖) volume 0 t := hder.norm
    have hi2 : IntervalIntegrable (fun s => ‖deriv a s‖ * (W * Real.exp (-2 * z.im * s))) volume 0 t := by
      have : ContinuousOn (fun s : ℝ => W * Real.exp (-2 * z.im * s)) (Set.uIcc 0 t) :=
        (continuousOn_const.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).continuousOn)
      exact hi1.mul_continuousOn this
    refine intervalIntegral.integral_mono_on ht.1 hi2 hi1 fun s hs => ?_
    have : W * Real.exp (-2 * z.im * s) ≤ 1 := by
      simpa [hW, mul_assoc] using weight_le_one z.im t ht.1 hs.1 hs.2
    have hn := norm_nonneg (deriv a s)
    calc ‖deriv a s‖ * (W * Real.exp (-2 * z.im * s)) ≤ ‖deriv a s‖ * 1 :=
          mul_le_mul_of_nonneg_left this hn
      _ = _ := mul_one _
  have hIeq : ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * (W * Real.exp (-2 * z.im * s)) =
      W * ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * Real.exp (-2 * z.im * s) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring
  have hW0 : 0 ≤ W := by positivity
  have hWt : W * Real.exp (-2 * z.im * t) ≤ 1 := by
    simpa [hW, mul_assoc] using weight_le_one z.im t ht.1 ht.1 le_rfl
  have hW1 : W ≤ 1 := weight_le_one' z.im t ht.1
  have hmul := mul_le_mul_of_nonneg_left hnorm hW0
  have e1 : W * (‖a t‖ * Real.exp (-2 * z.im * t)) ≤ ‖a t‖ := by
    have := mul_le_mul_of_nonneg_left hWt (norm_nonneg (a t))
    nlinarith
  have e2 : W * ‖a 0‖ ≤ ‖a 0‖ := by nlinarith [norm_nonneg (a 0)]
  have e3 : W * ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * Real.exp (-2 * z.im * s) ≤
      ∫ s in (0 : ℝ)..t, ‖deriv a s‖ := hIeq ▸ hIw
  rw [le_div_iff₀ hz2]
  calc Real.exp (-|z.im| * t) * (Real.exp (z.im * t) * ‖A‖) * (2 * ‖z‖)
      = W * (2 * ‖z‖ * ‖A‖) := by rw [hW]; ring
    _ ≤ W * (‖a t‖ * Real.exp (-2 * z.im * t) + ‖a 0‖ +
        ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * Real.exp (-2 * z.im * s)) := hmul
    _ = W * (‖a t‖ * Real.exp (-2 * z.im * t)) + W * ‖a 0‖ +
        W * ∫ s in (0 : ℝ)..t, ‖deriv a s‖ * Real.exp (-2 * z.im * s) := by ring
    _ ≤ ‖a t‖ + ‖a 0‖ + ∫ s in (0 : ℝ)..t, ‖deriv a s‖ := by linarith

end

end NlsGge.Atomic.G1021S2.K18.Aux

/-! ### The first Volterra term -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1021S2.K18.Aux

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
  refine NlsGge.Atomic.G1021S2.K18.K16.odd_sparse_matrix_opNorm_le _ _ (le_max_of_le_left (norm_nonneg _))
    (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact term1_entry00 a b z t
    · exact term1_entry11 a b z t
  · fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem norm_exp_neg_phase (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(Complex.I * z * (t : ℂ)))‖ = Real.exp (z.im * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_exp_pos_phase (z : ℂ) (t : ℝ) :
    ‖Complex.exp (Complex.I * z * (t : ℂ))‖ = Real.exp (-z.im * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem M1_weighted_bound {a b : ℝ → ℂ} (ha : AbsolutelyContinuousOnInterval a 0 1)
    (hb : AbsolutelyContinuousOnInterval b 0 1) (z : ℂ) (hz : z ≠ 0) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {S : ℝ}
    (hSa : ‖a t‖ + ‖a 0‖ + ∫ s in (0 : ℝ)..t, ‖deriv a s‖ ≤ 5 * S)
    (hSb : ‖b t‖ + ‖b 0‖ + ∫ s in (0 : ℝ)..t, ‖deriv b s‖ ≤ 5 * S) :
    Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t‖ ≤ 5 * S / (2 * ‖z‖) := by
  have hz2 : 0 < 2 * ‖z‖ := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    positivity
  have h01 : Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t 0 1‖ ≤
      5 * S / (2 * ‖z‖) := by
    rw [term1_entry01, norm_mul, norm_mul, norm_exp_neg_phase]
    simp only [Complex.norm_I, one_mul]
    refine (ibp_bound ha z hz ht).trans ?_
    exact div_le_div_of_nonneg_right hSa hz2.le
  have h10 : Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t 1 0‖ ≤
      5 * S / (2 * ‖z‖) := by
    rw [term1_entry10, norm_mul, norm_mul, norm_exp_pos_phase]
    simp only [norm_neg, Complex.norm_I, one_mul]
    have := ibp_bound hb (-z) (neg_ne_zero.2 hz) ht
    simp only [Complex.neg_im, abs_neg, norm_neg] at this
    refine this.trans ?_
    exact div_le_div_of_nonneg_right hSb hz2.le
  calc Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t‖
      ≤ Real.exp (-|z.im| * t) * max (‖freeKernelVolterraTerm38 a b z 1 t 0 1‖)
          (‖freeKernelVolterraTerm38 a b z 1 t 1 0‖) :=
        mul_le_mul_of_nonneg_left (norm_term1_le a b z t) (Real.exp_pos _).le
    _ ≤ _ := by
        rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
        exact max_le h01 h10

end

end NlsGge.Atomic.G1021S2.K18.Aux

/-! ### The potential pair of a continuous period-one pair -/

open NlsGge.Pilot

namespace NlsGge.Atomic.G1021S2.K18.Aux

noncomputable section

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

/-- The continuous function on the circle of a continuous period-one function. -/
def liftMap (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) :
    C(PhysicalCircle, ℂ) :=
  ⟨AddCircle.liftIoc 1 0 u,
    AddCircle.liftIoc_continuous (by simpa using (hper 0).symm) (by simpa using hu)⟩

/-- Its physical `L²` class. -/
def liftPD (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) : PhysicalL2 :=
  ContinuousMap.toLp 2 spatialMeasure ℂ (liftMap u hu hper)

theorem liftPD_cover_ae (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) :
    ∀ᵐ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 → coverRep38 (liftPD u hu hper) s = u s := by
  set F := liftMap u hu hper with hF
  have h1 := coverRep38_ae_phys (liftPD u hu hper)
  have h2 : (⇑(liftPD u hu hper) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (F : PhysicalCircle → ℂ) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure F
  have hv : (⇑(liftPD u hu hper) : PhysicalCircle → ℂ) =ᵐ[(volume : Measure PhysicalCircle)]
      (F : PhysicalCircle → ℂ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h2 _
  have hr := (AddCircle.measurePreserving_mk (1 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp hv
  have h01 : (0 : ℝ) + 1 = 1 := by norm_num
  rw [h01] at hr
  have hr' := (ae_restrict_iff' measurableSet_Ioc).1 hr
  filter_upwards [h1, hr'] with s hs1 hs2 hmem
  rw [hs1]
  refine (hs2 hmem).trans ?_
  show AddCircle.liftIoc 1 0 u (s : PhysicalCircle) = u s
  exact AddCircle.liftIoc_coe_apply (by simpa using hmem)

theorem term_eq (a b : ℝ → ℂ) (ha : ContinuousOn a (Set.Icc 0 1)) (hb : ContinuousOn b (Set.Icc 0 1))
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (z : ℂ) (n : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, freeKernelVolterraTerm38 a b z n t =
      potentialVolterraTerm38 (liftPD a ha hpa, liftPD b hb hpb) z n t := by
  have hA := liftPD_cover_ae a ha hpa
  have hB := liftPD_cover_ae b hb hpb
  induction n with
  | zero =>
    intro t _
    rfl
  | succ n ih =>
    intro t ht
    funext i j
    simp only [potentialVolterraTerm38, freeKernelVolterraTerm38]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hA, hB] with s hsA hsB hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have ihs := ih s ⟨hs'.1.le, hs'.2⟩
    have e1 : potRepFst38 (liftPD a ha hpa, liftPD b hb hpb) s = a s := hsA hs'
    have e2 : potRepSnd38 (liftPD a ha hpa, liftPD b hb hpb) s = b s := hsB hs'
    simp only [potentialVolterraTerm38] at ihs
    have hraw : rawPotCoeff38 (potRepFst38 (liftPD a ha hpa, liftPD b hb hpb))
        (potRepSnd38 (liftPD a ha hpa, liftPD b hb hpb)) s = rawPotCoeff38 a b s := by
      simp only [rawPotCoeff38, e1, e2]
    rw [hraw, ← ihs]

theorem L2_eq (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) :
    ‖liftPD u hu hper‖ ^ 2 = ∫ s in (0 : ℝ)..1, ‖u s‖ ^ 2 := by
  rw [← integral_sq_coverRep38_one]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [liftPD_cover_ae u hu hper] with s hs hmem
  rw [Set.uIoc_of_le zero_le_one] at hmem
  rw [hs hmem]

end

end NlsGge.Atomic.G1021S2.K18.Aux

/-! ### Assembly -/

namespace NlsGge.Atomic.G1021S2.K18

noncomputable section

open Aux

theorem sq_deriv_integrable {a b : ℝ → ℂ}
    (hd : IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hd ⊢
  refine Integrable.mono' hd ?_ ?_
  · exact ((measurable_deriv a).norm.pow_const 2).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg ‖deriv b s‖]

theorem sq_deriv_integrable' {a b : ℝ → ℂ}
    (hd : IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun s : ℝ => ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1 :=
  sq_deriv_integrable (a := b) (b := a) (by
    refine hd.congr ?_
    intro s _
    ring)

/-- The numerator bound used for each component. -/
theorem numerator_bound {a : ℝ → ℂ} (ha : AbsolutelyContinuousOnInterval a 0 1)
    (hda : IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2) MeasureTheory.volume 0 1)
    {S : ℝ} (hHa : Real.sqrt (∫ s in (0 : ℝ)..1, ‖a s‖ ^ 2) ≤ S)
    (hDa : Real.sqrt (∫ s in (0 : ℝ)..1, ‖deriv a s‖ ^ 2) ≤ S) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖a t‖ + ‖a 0‖ + ∫ s in (0 : ℝ)..t, ‖deriv a s‖ ≤ 5 * S := by
  have h1 := sup_bound ha hda ht
  have h2 := sup_bound ha hda (t := 0) ⟨le_rfl, zero_le_one⟩
  have hder_n : IntervalIntegrable (fun s => ‖deriv a s‖) MeasureTheory.volume 0 1 :=
    (ac_complex_ftc ha).1.norm
  have h3 : ∫ s in (0 : ℝ)..t, ‖deriv a s‖ ≤ ∫ s in (0 : ℝ)..1, ‖deriv a s‖ := by
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ hder_n
    exact Eventually.of_forall fun r => norm_nonneg _
  have h4 := sqrt_integral_bound (g := fun s => ‖deriv a s‖) (fun s => norm_nonneg _) hder_n hda
  linarith

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator

theorem G1018_whole : ((
  ∀ (a b : ℝ → ℂ),
  (∀ s : ℝ, a (s + 1) = a s) ∧ (∀ s : ℝ, b (s + 1) = b s) ∧
  AbsolutelyContinuousOnInterval a 0 1 ∧ AbsolutelyContinuousOnInterval b 0 1 ∧
  IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1 →
  let L2sq : ℝ := ∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)
  let H1sq : ℝ := ∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)
  ∀ z : ℂ, 1 ≤ ‖z‖ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    Real.exp (-|z.im| * t) *
        ‖(∑' n : ℕ, freeKernelVolterraTerm38 a b z n t) - freeZsFundamentalComplex z t‖ ≤
      3 * (1 + Real.sqrt L2sq * Real.exp (Real.sqrt L2sq)) * Real.sqrt H1sq / ‖z‖
  : Prop)) := by
  intro a b hyp L2sq H1sq z hz t ht0 ht1
  obtain ⟨hpa, hpb, hAa, hAb, hd⟩ := hyp
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hca : ContinuousOn a (Set.Icc 0 1) := by
    have := hAa.continuousOn
    rwa [hu1] at this
  have hcb : ContinuousOn b (Set.Icc 0 1) := by
    have := hAb.continuousOn
    rwa [hu1] at this
  have hda := sq_deriv_integrable hd
  have hdb := sq_deriv_integrable' hd
  have hia2 : IntervalIntegrable (fun s => ‖a s‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hca.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hib2 : IntervalIntegrable (fun s => ‖b s‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hcb.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  set Ha : ℝ := ∫ s in (0 : ℝ)..1, ‖a s‖ ^ 2 with hHa
  set Hb : ℝ := ∫ s in (0 : ℝ)..1, ‖b s‖ ^ 2 with hHb
  set Da : ℝ := ∫ s in (0 : ℝ)..1, ‖deriv a s‖ ^ 2 with hDa
  set Db : ℝ := ∫ s in (0 : ℝ)..1, ‖deriv b s‖ ^ 2 with hDb
  have hHa0 : 0 ≤ Ha := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hHb0 : 0 ≤ Hb := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hDa0 : 0 ≤ Da := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hDb0 : 0 ≤ Db := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hL2 : L2sq = Ha + Hb := by
    show (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) = _
    rw [intervalIntegral.integral_add hia2 hib2]
  have hH1 : H1sq = Ha + Da + Hb + Db := by
    show (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) = _
    rw [intervalIntegral.integral_add ((hia2.add hda).add hib2) hdb,
      intervalIntegral.integral_add (hia2.add hda) hib2, intervalIntegral.integral_add hia2 hda]
  set S : ℝ := Real.sqrt H1sq with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hsa : Real.sqrt Ha ≤ S := Real.sqrt_le_sqrt (by rw [hH1]; linarith)
  have hsb : Real.sqrt Hb ≤ S := Real.sqrt_le_sqrt (by rw [hH1]; linarith)
  have hsda : Real.sqrt Da ≤ S := Real.sqrt_le_sqrt (by rw [hH1]; linarith)
  have hsdb : Real.sqrt Db ≤ S := Real.sqrt_le_sqrt (by rw [hH1]; linarith)
  have hz1 : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz1
  set φ : PotPair := (liftPD a hca hpa, liftPD b hcb hpb) with hφ
  obtain ⟨hint, hineq⟩ := K16.G1016_whole φ z t ht0 ht1
  set K : ℝ := 5 * S / (2 * ‖z‖) with hK
  have hK0 : 0 ≤ K := by positivity
  have hM1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖ ≤ K := by
    intro s hs
    rw [← term_eq a b hca hcb hpa hpb z 1 s hs]
    exact M1_weighted_bound hAa hAb z hz0 hs
      (numerator_bound hAa hda hsa hsda hs) (numerator_bound hAb hdb hsb hsdb hs)
  have hphi : ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 = L2sq := by
    rw [hL2]
    exact congrArg₂ (· + ·) (L2_eq a hca hpa) (L2_eq b hcb hpb)
  rw [hphi] at hineq
  have htsum : (∑' n : ℕ, freeKernelVolterraTerm38 a b z n t) =
      ∑' n : ℕ, potentialVolterraTerm38 φ z n t :=
    tsum_congr fun n => term_eq a b hca hcb hpa hpb z n t ht
  rw [htsum]
  have hP2 : Real.sqrt (∫ s in (0 : ℝ)..t,
      (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2) ≤ K := by
    have h1 : ∫ s in (0 : ℝ)..t, (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2 ≤
        ∫ s in (0 : ℝ)..t, K ^ 2 :=
      intervalIntegral.integral_mono_on ht0 hint intervalIntegrable_const fun s hs =>
        pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
          (hM1 s ⟨hs.1, hs.2.trans ht1⟩) 2
    have h2 : ∫ s in (0 : ℝ)..t, K ^ 2 ≤ K ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      nlinarith [sq_nonneg K]
    exact Real.sqrt_le_iff.2 ⟨hK0, h1.trans h2⟩
  have hcc : 0 ≤ Real.sqrt L2sq * Real.exp (Real.sqrt L2sq) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hKK : K ≤ 3 * S / ‖z‖ := by
    rw [hK, div_le_div_iff₀ (by positivity) hz1]
    nlinarith [mul_nonneg hS0 hz1.le]
  calc _ ≤ _ := hineq
    _ ≤ K + (Real.sqrt L2sq * Real.exp (Real.sqrt L2sq)) * K :=
        add_le_add (hM1 t ht) (mul_le_mul_of_nonneg_left hP2 hcc)
    _ ≤ 3 * S / ‖z‖ + (Real.sqrt L2sq * Real.exp (Real.sqrt L2sq)) * (3 * S / ‖z‖) :=
        add_le_add hKK (mul_le_mul_of_nonneg_left hKK hcc)
    _ = 3 * (1 + Real.sqrt L2sq * Real.exp (Real.sqrt L2sq)) * Real.sqrt H1sq / ‖z‖ := by
        rw [hS]; ring

end

end NlsGge.Atomic.G1021S2.K18

/-! ============================================================================
G1-021 COMMAND03 pre-approval proof (proof development, AUTHOR; not self-reviewed).
The text above is a private copy of proof development/G1018_PROOF01.lean.txt (lines 1-1302, reviewed PASS by proof development; namespace
renamed `NlsGge.Atomic.G1018S1` -> `NlsGge.Atomic.G1021S2.K18`, the `#check`/`#print` tail removed); it contains the verbatim
G1-016 kit as `K18.K16`.  Route (GK Theorem 2.5): (i) a crude all-`z` weighted bound (no `|z|` restriction) from `K16.G1016_whole`
and `‖M_1‖_weighted <= ∫‖a‖`; (ii) G1-018 for `|z| >= 1`; (iii) a dichotomy in `n` (large `|n|`: use `1/|z|`; small: crude bound)
gives `‖F_t(w)‖ <= C/max(|n|,1)` for `w` within `Y` of `nπ`; (iv) Cauchy estimates on unit circles for derivatives; (v) the shift
`ξ_n -> nπ` by the mean value inequality for the entire function `E` and its derivative (Cauchy estimates again); (vi) the
`ℓ²` majorants `S n = Kc/max(|n|,1) + Ec ‖ξ n - nπ‖`.
============================================================================ -/

namespace NlsGge.Atomic.G1021S2

open MeasureTheory Filter Topology Set Metric NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The hypotheses on a pair of representatives. -/
abbrev HypG (a b : ℝ → ℂ) : Prop :=
  (∀ s : ℝ, a (s + 1) = a s) ∧ (∀ s : ℝ, b (s + 1) = b s) ∧
  AbsolutelyContinuousOnInterval a 0 1 ∧ AbsolutelyContinuousOnInterval b 0 1 ∧
  IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1

def K0f (R0 : ℝ) : ℝ := (1 + R0 * Real.exp R0) * R0

theorem weighted_int_le {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 1)) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-|z.im| * t) * (Real.exp (z.im * t) *
        ‖∫ s in (0 : ℝ)..t, f s * Complex.exp (2 * Complex.I * z * (s : ℂ))‖) ≤
      ∫ s in (0 : ℝ)..1, ‖f s‖ := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl ht.2
  have hfn : IntervalIntegrable (fun s => ‖f s‖) volume 0 1 :=
    (hf.norm).intervalIntegrable_of_Icc zero_le_one
  have hfn_t : IntervalIntegrable (fun s => ‖f s‖) volume 0 t :=
    ((hf.mono hsub).norm).intervalIntegrable_of_Icc ht.1
  set A := ∫ s in (0 : ℝ)..t, f s * Complex.exp (2 * Complex.I * z * (s : ℂ)) with hA
  set W : ℝ := Real.exp (-|z.im| * t) * Real.exp (z.im * t) with hW
  have hW0 : 0 ≤ W := by positivity
  have hnorm : ‖A‖ ≤ ∫ s in (0 : ℝ)..t, ‖f s‖ * Real.exp (-2 * z.im * s) := by
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [norm_mul, K18.Aux.norm_exp_phase]
  have hi2 : IntervalIntegrable (fun s => ‖f s‖ * (W * Real.exp (-2 * z.im * s))) volume 0 t := by
    have : ContinuousOn (fun s : ℝ => W * Real.exp (-2 * z.im * s)) (Set.uIcc 0 t) :=
      (continuousOn_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousOn)
    exact hfn_t.mul_continuousOn this
  have hIw : ∫ s in (0 : ℝ)..t, ‖f s‖ * (W * Real.exp (-2 * z.im * s)) ≤
      ∫ s in (0 : ℝ)..t, ‖f s‖ := by
    refine intervalIntegral.integral_mono_on ht.1 hi2 hfn_t fun s hs => ?_
    have : W * Real.exp (-2 * z.im * s) ≤ 1 := by
      simpa [hW, mul_assoc] using K18.Aux.weight_le_one z.im t ht.1 hs.1 hs.2
    calc ‖f s‖ * (W * Real.exp (-2 * z.im * s)) ≤ ‖f s‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_one _
  have hIeq : ∫ s in (0 : ℝ)..t, ‖f s‖ * (W * Real.exp (-2 * z.im * s)) =
      W * ∫ s in (0 : ℝ)..t, ‖f s‖ * Real.exp (-2 * z.im * s) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring
  have hmono : ∫ s in (0 : ℝ)..t, ‖f s‖ ≤ ∫ s in (0 : ℝ)..1, ‖f s‖ := by
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ hfn
    exact Eventually.of_forall fun r => norm_nonneg _
  calc Real.exp (-|z.im| * t) * (Real.exp (z.im * t) * ‖A‖) = W * ‖A‖ := by rw [hW]; ring
    _ ≤ W * ∫ s in (0 : ℝ)..t, ‖f s‖ * Real.exp (-2 * z.im * s) :=
        mul_le_mul_of_nonneg_left hnorm hW0
    _ = ∫ s in (0 : ℝ)..t, ‖f s‖ * (W * Real.exp (-2 * z.im * s)) := hIeq.symm
    _ ≤ _ := hIw.trans hmono

theorem M1_weighted_all {a b : ℝ → ℂ} (ha : ContinuousOn a (Set.Icc 0 1))
    (hb : ContinuousOn b (Set.Icc 0 1)) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {S : ℝ}
    (hSa : ∫ s in (0 : ℝ)..1, ‖a s‖ ≤ S) (hSb : ∫ s in (0 : ℝ)..1, ‖b s‖ ≤ S) :
    Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t‖ ≤ S := by
  have h01 : Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t 0 1‖ ≤ S := by
    rw [K18.Aux.term1_entry01, norm_mul, norm_mul, K18.Aux.norm_exp_neg_phase]
    simp only [Complex.norm_I, one_mul]
    exact (weighted_int_le ha z ht).trans hSa
  have h10 : Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t 1 0‖ ≤ S := by
    rw [K18.Aux.term1_entry10, norm_mul, norm_mul, K18.Aux.norm_exp_pos_phase]
    simp only [norm_neg, Complex.norm_I, one_mul]
    have := weighted_int_le hb (-z) ht
    simp only [Complex.neg_im, abs_neg, norm_neg] at this
    exact this.trans hSb
  calc Real.exp (-|z.im| * t) * ‖freeKernelVolterraTerm38 a b z 1 t‖
      ≤ Real.exp (-|z.im| * t) * max (‖freeKernelVolterraTerm38 a b z 1 t 0 1‖)
          (‖freeKernelVolterraTerm38 a b z 1 t 1 0‖) :=
        mul_le_mul_of_nonneg_left (K18.Aux.norm_term1_le a b z t) (Real.exp_pos _).le
    _ ≤ _ := by
        rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
        exact max_le h01 h10

theorem sqrtL2_le (a b : ℝ → ℂ) (hyp : HypG a b) :
    Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) ≤
      Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) := by
  obtain ⟨hpa, hpb, hAa, hAb, hd⟩ := hyp
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hca : ContinuousOn a (Set.Icc 0 1) := by
    have := hAa.continuousOn
    rwa [hu1] at this
  have hcb : ContinuousOn b (Set.Icc 0 1) := by
    have := hAb.continuousOn
    rwa [hu1] at this
  have hda := K18.sq_deriv_integrable hd
  have hdb := K18.sq_deriv_integrable' hd
  have hia2 : IntervalIntegrable (fun s => ‖a s‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hca.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hib2 : IntervalIntegrable (fun s => ‖b s‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hcb.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hDa0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖deriv a s‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hDb0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖deriv b s‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  refine Real.sqrt_le_sqrt ?_
  rw [intervalIntegral.integral_add hia2 hib2,
    intervalIntegral.integral_add ((hia2.add hda).add hib2) hdb,
    intervalIntegral.integral_add (hia2.add hda) hib2, intervalIntegral.integral_add hia2 hda]
  linarith

theorem weighted_all (a b : ℝ → ℂ) (hyp : HypG a b) (z : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-|z.im| * t) *
        ‖(∑' n : ℕ, freeKernelVolterraTerm38 a b z n t) - freeZsFundamentalComplex z t‖ ≤
      (1 + Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) *
          Real.exp (Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)))) *
        Real.sqrt (∫ s in (0 : ℝ)..1,
          (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) := by
  obtain ⟨hpa, hpb, hAa, hAb, hd⟩ := hyp
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hca : ContinuousOn a (Set.Icc 0 1) := by
    have := hAa.continuousOn
    rwa [hu1] at this
  have hcb : ContinuousOn b (Set.Icc 0 1) := by
    have := hAb.continuousOn
    rwa [hu1] at this
  have hda := K18.sq_deriv_integrable hd
  have hdb := K18.sq_deriv_integrable' hd
  have hia2 : IntervalIntegrable (fun s => ‖a s‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hca.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hib2 : IntervalIntegrable (fun s => ‖b s‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hcb.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hia : IntervalIntegrable (fun s => ‖a s‖) MeasureTheory.volume 0 1 :=
    (hca.norm).intervalIntegrable_of_Icc zero_le_one
  have hib : IntervalIntegrable (fun s => ‖b s‖) MeasureTheory.volume 0 1 :=
    (hcb.norm).intervalIntegrable_of_Icc zero_le_one
  set L2sq : ℝ := ∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2) with hL2def
  set H1sq : ℝ := ∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)
    with hH1def
  set Ha : ℝ := ∫ s in (0 : ℝ)..1, ‖a s‖ ^ 2 with hHa
  set Hb : ℝ := ∫ s in (0 : ℝ)..1, ‖b s‖ ^ 2 with hHb
  set Da : ℝ := ∫ s in (0 : ℝ)..1, ‖deriv a s‖ ^ 2 with hDa
  set Db : ℝ := ∫ s in (0 : ℝ)..1, ‖deriv b s‖ ^ 2 with hDb
  have hHa0 : 0 ≤ Ha := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hHb0 : 0 ≤ Hb := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hDa0 : 0 ≤ Da := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hDb0 : 0 ≤ Db := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hL2 : L2sq = Ha + Hb := by
    rw [hL2def, intervalIntegral.integral_add hia2 hib2]
  have hH1 : H1sq = Ha + Da + Hb + Db := by
    rw [hH1def, intervalIntegral.integral_add ((hia2.add hda).add hib2) hdb,
      intervalIntegral.integral_add (hia2.add hda) hib2, intervalIntegral.integral_add hia2 hda]
  set S : ℝ := Real.sqrt H1sq with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hsa : Real.sqrt Ha ≤ S := Real.sqrt_le_sqrt (by rw [hH1]; linarith)
  have hsb : Real.sqrt Hb ≤ S := Real.sqrt_le_sqrt (by rw [hH1]; linarith)
  have hSa : ∫ s in (0 : ℝ)..1, ‖a s‖ ≤ S :=
    (K18.Aux.sqrt_integral_bound (g := fun s => ‖a s‖) (fun s => norm_nonneg _) hia hia2).trans hsa
  have hSb : ∫ s in (0 : ℝ)..1, ‖b s‖ ≤ S :=
    (K18.Aux.sqrt_integral_bound (g := fun s => ‖b s‖) (fun s => norm_nonneg _) hib hib2).trans hsb
  set φ : PotPair := (K18.Aux.liftPD a hca hpa, K18.Aux.liftPD b hcb hpb) with hφ
  obtain ⟨hint, hineq⟩ := K18.K16.G1016_whole φ z t ht0 ht1
  have hM1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖ ≤ S := by
    intro s hs
    rw [← K18.Aux.term_eq a b hca hcb hpa hpb z 1 s hs]
    exact M1_weighted_all hca hcb z hs hSa hSb
  have hphi : ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 = L2sq := by
    rw [hL2]
    exact congrArg₂ (· + ·) (K18.Aux.L2_eq a hca hpa) (K18.Aux.L2_eq b hcb hpb)
  rw [hphi] at hineq
  have htsum : (∑' n : ℕ, freeKernelVolterraTerm38 a b z n t) =
      ∑' n : ℕ, potentialVolterraTerm38 φ z n t :=
    tsum_congr fun n => K18.Aux.term_eq a b hca hcb hpa hpb z n t ht
  rw [htsum]
  have hP2 : Real.sqrt (∫ s in (0 : ℝ)..t,
      (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2) ≤ S := by
    have h1 : ∫ s in (0 : ℝ)..t, (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2 ≤
        ∫ s in (0 : ℝ)..t, S ^ 2 :=
      intervalIntegral.integral_mono_on ht0 hint intervalIntegrable_const fun s hs =>
        pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
          (hM1 s ⟨hs.1, hs.2.trans ht1⟩) 2
    have h2 : ∫ s in (0 : ℝ)..t, S ^ 2 ≤ S ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      nlinarith [sq_nonneg S]
    exact Real.sqrt_le_iff.2 ⟨hS0, h1.trans h2⟩
  have hcc : 0 ≤ Real.sqrt L2sq * Real.exp (Real.sqrt L2sq) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  calc _ ≤ _ := hineq
    _ ≤ S + (Real.sqrt L2sq * Real.exp (Real.sqrt L2sq)) * S :=
        add_le_add (hM1 t ht) (mul_le_mul_of_nonneg_left hP2 hcc)
    _ = (1 + Real.sqrt L2sq * Real.exp (Real.sqrt L2sq)) * S := by ring

/-- Entire dependence of the series on the spectral parameter. -/
theorem differentiableAt_M (ψ : PotPair) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z := by
  have h := NlsGge.Atomic.G1004GenT.analytic_all t ht (z, ψ) (Set.mem_univ _)
  have hc : AnalyticAt ℂ (fun w : ℂ => (w, ψ)) z :=
    analyticAt_id.prod analyticAt_const
  have h2 := AnalyticAt.comp (g := fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
    (f := fun w : ℂ => (w, ψ)) (x := z) h hc
  exact h2.differentiableAt

theorem diffAt_series (a b : ℝ → ℂ) (hyp : HypG a b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) z := by
  obtain ⟨hpa, hpb, hAa, hAb, hd⟩ := hyp
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hca : ContinuousOn a (Set.Icc 0 1) := by
    have := hAa.continuousOn
    rwa [hu1] at this
  have hcb : ContinuousOn b (Set.Icc 0 1) := by
    have := hAb.continuousOn
    rwa [hu1] at this
  have e : (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) =
      fun w => ∑' m : ℕ,
        potentialVolterraTerm38 (K18.Aux.liftPD a hca hpa, K18.Aux.liftPD b hcb hpb) w m t := by
    funext w
    exact tsum_congr fun m => K18.Aux.term_eq a b hca hcb hpa hpb w m t ⟨ht0, ht1⟩
  rw [e]
  exact differentiableAt_M _ ht0 z

theorem analyticE (t : ℝ) (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => freeZsFundamentalComplex w t) z := by
  have h : AnalyticAt ℂ (fun w : ℂ => freeE w t) z := by
    refine NlsGge.Atomic.G1004GenT.analyticAt_of_entries fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [freeE] <;> fun_prop
  have e : (fun w : ℂ => freeZsFundamentalComplex w t) = fun w => freeE w t := by
    funext w; exact (freeE_eq w t).symm
  rw [e]
  exact h

theorem differentiable_E (t : ℝ) : Differentiable ℂ (fun w : ℂ => freeZsFundamentalComplex w t) :=
  fun z => (analyticE t z).differentiableAt

theorem norm_E_le (w : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖freeZsFundamentalComplex w t‖ ≤ Real.exp |w.im| := by
  rw [← freeE_eq]
  refine (K18.K16.norm_freeE_le w ht0).trans (Real.exp_le_exp.2 ?_)
  exact mul_le_of_le_one_right (abs_nonneg _) ht1

theorem cauchy_mat {f : ℂ → PairMat38} (hf : Differentiable ℂ f) {z : ℂ} {B : ℝ}
    (hB : ∀ w : ℂ, ‖w - z‖ = 1 → ‖f w‖ ≤ B) : ‖deriv f z‖ ≤ B := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hf.diffContOnCl
    (fun w hw => hB w (by simpa [dist_eq_norm] using hw))
  simpa using h

theorem norm_sub_le_of_dist {u v c : ℂ} {Y : ℝ} (hu : ‖u - v‖ = 1) (hv : ‖v - c‖ ≤ Y) :
    ‖u - c‖ ≤ Y + 1 := by
  calc ‖u - c‖ = ‖(u - v) + (v - c)‖ := by ring_nf
    _ ≤ ‖u - v‖ + ‖v - c‖ := norm_add_le _ _
    _ ≤ Y + 1 := by rw [hu]; linarith

theorem abs_im_le_of_real {u c : ℂ} (hc : c.im = 0) {Y : ℝ} (hu : ‖u - c‖ ≤ Y) : |u.im| ≤ Y := by
  have h := Complex.abs_im_le_norm (u - c)
  rw [Complex.sub_im, hc, sub_zero] at h
  linarith

theorem E_deriv_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : ℂ) (hc : c.im = 0) {Y : ℝ} {v : ℂ}
    (hv : ‖v - c‖ ≤ Y) :
    ‖deriv (fun w : ℂ => freeZsFundamentalComplex w t) v‖ ≤ Real.exp (Y + 1) := by
  refine cauchy_mat (differentiable_E t) fun u hu => ?_
  have hu' := norm_sub_le_of_dist hu hv
  exact (norm_E_le u ht0 ht1).trans (Real.exp_le_exp.2 (abs_im_le_of_real hc hu'))

theorem E_shift (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : ℂ) (hc : c.im = 0) {Y : ℝ} (hY : 0 ≤ Y)
    {w : ℂ} (hw : ‖w - c‖ ≤ Y) :
    ‖freeZsFundamentalComplex w t - freeZsFundamentalComplex c t‖ ≤ Real.exp (Y + 1) * ‖w - c‖ ∧
    ‖deriv (fun v : ℂ => freeZsFundamentalComplex v t) w -
        deriv (fun v : ℂ => freeZsFundamentalComplex v t) c‖ ≤ Real.exp (Y + 2) * ‖w - c‖ := by
  have hconv : Convex ℝ (Metric.closedBall c Y) := convex_closedBall c Y
  have hwm : w ∈ Metric.closedBall c Y := by simpa [dist_eq_norm] using hw
  have hcm : c ∈ Metric.closedBall c Y := Metric.mem_closedBall_self hY
  have hd' : ∀ v : ℂ, DifferentiableAt ℂ (deriv (fun v : ℂ => freeZsFundamentalComplex v t)) v :=
    fun v => (analyticE t v).deriv.differentiableAt
  constructor
  · have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun v : ℂ => freeZsFundamentalComplex v t) (C := Real.exp (Y + 1))
      (s := Metric.closedBall c Y) (fun v _ => differentiable_E t v)
      (fun v hv => E_deriv_bound t ht0 ht1 c hc (by simpa [dist_eq_norm] using hv)) hconv hcm hwm
    simpa using h
  · have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := deriv (fun v : ℂ => freeZsFundamentalComplex v t)) (C := Real.exp (Y + 2))
      (s := Metric.closedBall c Y) (fun v _ => hd' v)
      (fun v hv => ?_) hconv hcm hwm
    · simpa using h
    · have hv' : ‖v - c‖ ≤ Y := by simpa [dist_eq_norm] using hv
      refine cauchy_mat (fun u => hd' u) fun u hu => ?_
      have hu' := norm_sub_le_of_dist hu hv'
      have := E_deriv_bound t ht0 ht1 c hc hu'
      calc _ ≤ Real.exp (Y + 1 + 1) := this
        _ = Real.exp (Y + 2) := by ring_nf

theorem unweightT {a t X A : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (h : Real.exp (-a * t) * X ≤ A) : X ≤ Real.exp a * A := by
  have e : X = Real.exp (a * t) * (Real.exp (-a * t) * X) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [e]
  calc Real.exp (a * t) * (Real.exp (-a * t) * X) ≤ Real.exp (a * t) * A :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ ≤ Real.exp a * A :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_of_le_one_right ha ht1)) hA

theorem Fbound (a b : ℝ → ℂ) (hyp : HypG a b) {R0 : ℝ}
    (hR0 : Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0)
    (z : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(∑' m : ℕ, freeKernelVolterraTerm38 a b z m t) - freeZsFundamentalComplex z t‖ ≤
        Real.exp |z.im| * K0f R0 ∧
    (1 ≤ ‖z‖ → ‖(∑' m : ℕ, freeKernelVolterraTerm38 a b z m t) - freeZsFundamentalComplex z t‖ ≤
        Real.exp |z.im| * (3 * K0f R0 / ‖z‖)) := by
  have hc := sqrtL2_le a b hyp
  have hS0 : 0 ≤ Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) := Real.sqrt_nonneg _
  have hR00 : 0 ≤ R0 := hS0.trans hR0
  have hcR : Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) ≤ R0 := hc.trans hR0
  have hc0 : 0 ≤ Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) := Real.sqrt_nonneg _
  have hfac : (1 + Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) *
          Real.exp (Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)))) *
        Real.sqrt (∫ s in (0 : ℝ)..1,
          (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ K0f R0 := by
    unfold K0f
    refine mul_le_mul ?_ hR0 hS0 (by positivity)
    have := mul_le_mul hcR (Real.exp_le_exp.2 hcR) (Real.exp_pos _).le hR00
    linarith
  have hK0 : 0 ≤ K0f R0 := by unfold K0f; positivity
  constructor
  · exact unweightT ht0 ht1 (abs_nonneg _) hK0 ((weighted_all a b hyp z ht0 ht1).trans hfac)
  · intro hz
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
    have h18 : Real.exp (-|z.im| * t) *
        ‖(∑' n : ℕ, freeKernelVolterraTerm38 a b z n t) - freeZsFundamentalComplex z t‖ ≤
      3 * (1 + Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)) *
          Real.exp (Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖b s‖ ^ 2)))) *
        Real.sqrt (∫ s in (0 : ℝ)..1,
          (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) / ‖z‖ :=
      K18.G1018_whole a b hyp z hz t ht0 ht1
    refine unweightT ht0 ht1 (abs_nonneg _) (by positivity) (h18.trans ?_)
    refine div_le_div_of_nonneg_right ?_ hz0.le
    linarith

theorem Fcomb (a b : ℝ → ℂ) (hyp : HypG a b) {R0 : ℝ}
    (hR0 : Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0)
    (n : ℤ) {Y : ℝ} (hY : 0 ≤ Y) {w : ℂ} (hw : ‖w - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) - freeZsFundamentalComplex w t‖ ≤
      Real.exp Y * ((Y + 3) * K0f R0) / max |(n : ℝ)| 1 := by
  have hS0 : 0 ≤ Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K0f R0 := by
    have : 0 ≤ R0 := hS0.trans hR0
    unfold K0f; positivity
  have hcim : ((n : ℂ) * (Real.pi : ℂ)).im = 0 := by simp
  have him : |w.im| ≤ Y := abs_im_le_of_real hcim hw
  obtain ⟨hF1, hF2⟩ := Fbound a b hyp hR0 w ht0 ht1
  have hexp : Real.exp |w.im| ≤ Real.exp Y := Real.exp_le_exp.2 him
  by_cases hcase : Y + 1 ≤ |(n : ℝ)|
  · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by linarith
    have hmax : max |(n : ℝ)| 1 = |(n : ℝ)| := max_eq_left hn1
    have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = |(n : ℝ)| * Real.pi := by
      rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hwn : |(n : ℝ)| ≤ ‖w‖ := by
      have h1 : ‖(n : ℂ) * (Real.pi : ℂ)‖ ≤ ‖w‖ + ‖w - (n : ℂ) * (Real.pi : ℂ)‖ := by
        calc ‖(n : ℂ) * (Real.pi : ℂ)‖ = ‖w - (w - (n : ℂ) * (Real.pi : ℂ))‖ := by ring_nf
          _ ≤ ‖w‖ + ‖w - (n : ℂ) * (Real.pi : ℂ)‖ := norm_sub_le _ _
      rw [hnpi] at h1
      nlinarith [Real.pi_gt_three]
    have hw1 : 1 ≤ ‖w‖ := hn1.trans hwn
    have hb := hF2 hw1
    rw [hmax]
    have hpos : 0 < |(n : ℝ)| := lt_of_lt_of_le one_pos hn1
    calc _ ≤ Real.exp |w.im| * (3 * K0f R0 / ‖w‖) := hb
      _ ≤ Real.exp Y * (3 * K0f R0 / |(n : ℝ)|) := by
          refine mul_le_mul hexp ?_ (by positivity) (Real.exp_pos _).le
          exact div_le_div_of_nonneg_left (by positivity) hpos hwn
      _ ≤ Real.exp Y * ((Y + 3) * K0f R0) / |(n : ℝ)| := by
          rw [← mul_div_assoc]
          refine div_le_div_of_nonneg_right ?_ hpos.le
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          nlinarith
  · push_neg at hcase
    have hmax : max |(n : ℝ)| 1 ≤ Y + 1 := max_le hcase.le (by linarith)
    have hm1 : 1 ≤ max |(n : ℝ)| 1 := le_max_right _ _
    have hmpos : 0 < max |(n : ℝ)| 1 := lt_of_lt_of_le one_pos hm1
    calc _ ≤ Real.exp |w.im| * K0f R0 := hF1
      _ ≤ Real.exp Y * K0f R0 := mul_le_mul_of_nonneg_right hexp hK0
      _ ≤ Real.exp Y * ((Y + 3) * K0f R0) / max |(n : ℝ)| 1 := by
          rw [le_div_iff₀ hmpos]
          have h1 : Real.exp Y * K0f R0 * max |(n : ℝ)| 1 ≤ Real.exp Y * K0f R0 * (Y + 3) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          nlinarith

theorem deriv_F_bound (a b : ℝ → ℂ) (hyp : HypG a b) {R0 : ℝ}
    (hR0 : Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0)
    (n : ℤ) {Y : ℝ} (hY : 0 ≤ Y) {z : ℂ} (hz : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖deriv (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) z -
        deriv (fun w : ℂ => freeZsFundamentalComplex w t) z‖ ≤
      Real.exp (Y + 1) * ((Y + 1 + 3) * K0f R0) / max |(n : ℝ)| 1 := by
  have hdM : ∀ w : ℂ, DifferentiableAt ℂ
      (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) w :=
    fun w => diffAt_series a b hyp ht0 ht1 w
  have hdE := differentiable_E t
  set G : ℂ → PairMat38 := fun w => (∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) -
      freeZsFundamentalComplex w t with hG
  have hGd : Differentiable ℂ G := fun w => (hdM w).sub (hdE w)
  have hderiv : deriv (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) z -
      deriv (fun w : ℂ => freeZsFundamentalComplex w t) z = deriv G z :=
    (deriv_sub (hdM z) (hdE z)).symm
  rw [hderiv]
  refine cauchy_mat hGd fun w hw => ?_
  have hw' := norm_sub_le_of_dist hw hz
  exact Fcomb a b hyp hR0 n (Y := Y + 1) (by linarith) hw' ht0 ht1


theorem G1021_whole :
    ((
  (∀ R0 R1 : ℝ, ∃ C : ℝ,
    ∀ (a b : ℝ → ℂ),
      (∀ s : ℝ, a (s + 1) = a s) → (∀ s : ℝ, b (s + 1) = b s) →
      AbsolutelyContinuousOnInterval a 0 1 → AbsolutelyContinuousOnInterval b 0 1 →
      IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1 →
      Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0 →
      ∀ ξ : ℤ → ℂ, (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
      ∀ n : ℤ, 1 ≤ |n| → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖(∑' m : ℕ, freeKernelVolterraTerm38 a b (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ ≤ C / |(n : ℝ)| ∧
        DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) (ξ n) ∧
        ‖deriv (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) (ξ n) -
            deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ≤ C / |(n : ℝ)|)
  ∧
  (∀ R0 R2 : ℝ, ∃ C : ℝ,
    ∀ (a b : ℝ → ℂ),
      (∀ s : ℝ, a (s + 1) = a s) → (∀ s : ℝ, b (s + 1) = b s) →
      AbsolutelyContinuousOnInterval a 0 1 → AbsolutelyContinuousOnInterval b 0 1 →
      IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) MeasureTheory.volume 0 1 →
      Real.sqrt (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0 →
      ∀ ξ : ℤ → ℂ,
        (Summable (fun n : ℤ => ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
          Real.sqrt (∑' n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ R2) →
        (∃ S : ℤ → ℝ, Summable (fun n : ℤ => S n ^ 2) ∧ (∑' n : ℤ, S n ^ 2) ≤ C ∧
          ∀ n : ℤ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            ‖(∑' m : ℕ, freeKernelVolterraTerm38 a b (ξ n) m t) - freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t‖ ≤ S n) ∧
        (∃ S' : ℤ → ℝ, Summable (fun n : ℤ => S' n ^ 2) ∧ (∑' n : ℤ, S' n ^ 2) ≤ C ∧
          ∀ n : ℤ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            ‖deriv (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) (ξ n) -
                deriv (fun w : ℂ => freeZsFundamentalComplex w t) ((n : ℂ) * (Real.pi : ℂ))‖ ≤ S' n))
  : Prop)) := by
  constructor
  · intro R0 R1
    refine ⟨Real.exp (|R1| + 1) * ((|R1| + 1 + 3) * K0f R0), ?_⟩
    intro a b hpa hpb hAa hAb hd hR0 ξ hξ n hn t ht0 ht1
    have hyp : HypG a b := ⟨hpa, hpb, hAa, hAb, hd⟩
    have hK0 : 0 ≤ K0f R0 := by
      have : 0 ≤ R0 := (Real.sqrt_nonneg _).trans hR0
      unfold K0f; positivity
    have hY : 0 ≤ |R1| := abs_nonneg _
    have hξn : ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ |R1| := (hξ n).trans (le_abs_self _)
    have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hn
    have hmax : max |(n : ℝ)| 1 = |(n : ℝ)| := max_eq_left hn'
    have hpos : 0 < |(n : ℝ)| := lt_of_lt_of_le one_pos hn'
    refine ⟨?_, diffAt_series a b hyp ht0 ht1 (ξ n), ?_⟩
    · have h := Fcomb a b hyp hR0 n hY hξn ht0 ht1
      rw [hmax] at h
      refine h.trans (div_le_div_of_nonneg_right ?_ hpos.le)
      have h1 : Real.exp |R1| ≤ Real.exp (|R1| + 1) := Real.exp_le_exp.2 (by linarith)
      have h2 : (|R1| + 3) * K0f R0 ≤ (|R1| + 1 + 3) * K0f R0 :=
        mul_le_mul_of_nonneg_right (by linarith) hK0
      exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    · have h := deriv_F_bound a b hyp hR0 n hY hξn ht0 ht1
      rw [hmax] at h
      exact h
  · intro R0 R2
    set Y : ℝ := |R2| with hYdef
    set Kc : ℝ := Real.exp (Y + 2) * ((Y + 4) * K0f R0) with hKc
    set Ec : ℝ := Real.exp (Y + 2) with hEc
    set Zc : ℝ := ∑' n : ℤ, 1 / (max |(n : ℝ)| 1) ^ 2 with hZc
    refine ⟨2 * Kc ^ 2 * Zc + 2 * Ec ^ 2 * R2 ^ 2, ?_⟩
    intro a b hpa hpb hAa hAb hd hR0 ξ hξ
    obtain ⟨hsum, hR2⟩ := hξ
    have hyp : HypG a b := ⟨hpa, hpb, hAa, hAb, hd⟩
    have hK0 : 0 ≤ K0f R0 := by
      have : 0 ≤ R0 := (Real.sqrt_nonneg _).trans hR0
      unfold K0f; positivity
    have hY : 0 ≤ Y := abs_nonneg _
    have hEc0 : 0 ≤ Ec := (Real.exp_pos _).le
    have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
    -- the perturbations are small
    have hwY : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Y := by
      intro n
      have h2 : ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤
          ∑' k : ℤ, ‖ξ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2 :=
        hsum.le_tsum n (fun j _ => sq_nonneg _)
      have h3 := Real.abs_le_sqrt h2
      have h4 : ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R2 :=
        (le_abs_self _).trans (h3.trans hR2)
      exact h4.trans (le_abs_self _)
    have hsq : (∑' k : ℤ, ‖ξ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ R2 ^ 2 := by
      calc (∑' k : ℤ, ‖ξ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2)
          = (Real.sqrt (∑' k : ℤ, ‖ξ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ^ 2 :=
            (Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)).symm
        _ ≤ R2 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hR2 2
    have hm1 : ∀ n : ℤ, 1 ≤ max |(n : ℝ)| 1 := fun n => le_max_right _ _
    have hmpos : ∀ n : ℤ, 0 < max |(n : ℝ)| 1 := fun n => lt_of_lt_of_le one_pos (hm1 n)
    have hg : Summable (fun n : ℤ => 1 / (max |(n : ℝ)| 1) ^ 2) := by
      refine Summable.of_nonneg_of_le (fun n => by have := hmpos n; positivity) (fun n => ?_)
        ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num) |>.add
          (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable)
      by_cases hn : n = 0
      · subst hn; simp
      · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
        rw [max_eq_left h1, sq_abs]
        simp [hn]
    set S : ℤ → ℝ := fun n => Kc / max |(n : ℝ)| 1 + Ec * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ with hS
    have hle : ∀ n : ℤ, S n ^ 2 ≤ 2 * Kc ^ 2 * (1 / (max |(n : ℝ)| 1) ^ 2) +
        2 * Ec ^ 2 * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by
      intro n
      have hx : (Kc / max |(n : ℝ)| 1) ^ 2 = Kc ^ 2 * (1 / (max |(n : ℝ)| 1) ^ 2) := by
        rw [div_pow]; ring
      have := sq_nonneg (Kc / max |(n : ℝ)| 1 - Ec * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖)
      simp only [hS]
      nlinarith [hx, this]
    have hsb : Summable (fun n : ℤ => 2 * Kc ^ 2 * (1 / (max |(n : ℝ)| 1) ^ 2) +
        2 * Ec ^ 2 * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
      (hg.mul_left _).add (hsum.mul_left _)
    have hSsum : Summable (fun n : ℤ => S n ^ 2) :=
      Summable.of_nonneg_of_le (fun n => sq_nonneg _) hle hsb
    have hStsum : (∑' n : ℤ, S n ^ 2) ≤ 2 * Kc ^ 2 * Zc + 2 * Ec ^ 2 * R2 ^ 2 := by
      refine (hSsum.tsum_le_tsum hle hsb).trans ?_
      rw [(hg.mul_left _).tsum_add (hsum.mul_left _), tsum_mul_left, tsum_mul_left]
      have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * Ec ^ 2)
      linarith
    have hcim : ∀ n : ℤ, ((n : ℂ) * (Real.pi : ℂ)).im = 0 := fun n => by simp
    have hKc_le : ∀ n : ℤ, Real.exp Y * ((Y + 3) * K0f R0) / max |(n : ℝ)| 1 ≤
        Kc / max |(n : ℝ)| 1 := by
      intro n
      refine div_le_div_of_nonneg_right ?_ (hmpos n).le
      rw [hKc]
      exact mul_le_mul (Real.exp_le_exp.2 (by linarith))
        (mul_le_mul_of_nonneg_right (by linarith) hK0) (by positivity) (Real.exp_pos _).le
    have hKc_le' : ∀ n : ℤ, Real.exp (Y + 1) * ((Y + 1 + 3) * K0f R0) / max |(n : ℝ)| 1 ≤
        Kc / max |(n : ℝ)| 1 := by
      intro n
      refine div_le_div_of_nonneg_right ?_ (hmpos n).le
      rw [hKc]
      have : Y + 1 + 3 = Y + 4 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith))
        (by positivity)
    refine ⟨⟨S, hSsum, hStsum, ?_⟩, ⟨S, hSsum, hStsum, ?_⟩⟩
    · intro n t ht0 ht1
      have hF := (Fcomb a b hyp hR0 n hY (hwY n) ht0 ht1).trans (hKc_le n)
      have hE := (E_shift t ht0 ht1 ((n : ℂ) * (Real.pi : ℂ)) (hcim n) hY (hwY n)).1
      have hE' : ‖freeZsFundamentalComplex (ξ n) t -
          freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t‖ ≤
          Ec * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ :=
        hE.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (norm_nonneg _))
      calc _ ≤ ‖(∑' m : ℕ, freeKernelVolterraTerm38 a b (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ +
            ‖freeZsFundamentalComplex (ξ n) t -
              freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ S n := add_le_add hF hE'
    · intro n t ht0 ht1
      have hF := (deriv_F_bound a b hyp hR0 n hY (hwY n) ht0 ht1).trans (hKc_le' n)
      have hE := (E_shift t ht0 ht1 ((n : ℂ) * (Real.pi : ℂ)) (hcim n) hY (hwY n)).2
      calc _ ≤ ‖deriv (fun w : ℂ => ∑' m : ℕ, freeKernelVolterraTerm38 a b w m t) (ξ n) -
              deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ +
            ‖deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n) -
              deriv (fun w : ℂ => freeZsFundamentalComplex w t) ((n : ℂ) * (Real.pi : ℂ))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ S n := add_le_add hF hE

end

end NlsGge.Atomic.G1021S2
