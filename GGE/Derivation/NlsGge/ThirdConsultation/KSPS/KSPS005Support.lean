import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS005Host
import NlsGge.ThirdConsultation.KSPS.KSPS004Support2

/- KSPS-005 SUPPORT01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS005Support.lean.
   Summing the Picard tail (n >= 3): the density `dens` of the potential pair, the primitive-power integral
   (PrimOn calculus of KSPS003Support1), the entrywise factorial bound for term (n+3) from an entrywise bound on
   term 3 (alternating phases are absorbed by |E(x-t)||E(t)| <= e^{|Im lam| x}), summability/tsum bound,
   entry-wise decomposition of `fundamentalRemainder`, and the final assembly from arbitrary KSPS-003/004 constants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS003Support NlsGge.ThirdConsultation.KSPS004Support2
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS005Support

/-! ### the density of a potential pair -/

def dens (p : PotPair) (t : ℝ) : ℝ :=
  Real.sqrt (‖coverRep38 p.1 t‖ ^ 2 + ‖coverRep38 p.2 t‖ ^ 2)

theorem dens_nonneg (p : PotPair) (t : ℝ) : 0 ≤ dens p t := Real.sqrt_nonneg _

theorem dens_sq (p : PotPair) (t : ℝ) :
    dens p t ^ 2 = ‖coverRep38 p.1 t‖ ^ 2 + ‖coverRep38 p.2 t‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem fst_le_dens (p : PotPair) (t : ℝ) : ‖potRepFst38 p t‖ ≤ dens p t := by
  unfold dens potRepFst38
  calc ‖coverRep38 p.1 t‖ = Real.sqrt (‖coverRep38 p.1 t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖coverRep38 p.2 t‖])

theorem snd_le_dens (p : PotPair) (t : ℝ) : ‖potRepSnd38 p t‖ ≤ dens p t := by
  unfold dens potRepSnd38
  calc ‖coverRep38 p.2 t‖ = Real.sqrt (‖coverRep38 p.2 t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖coverRep38 p.1 t‖])

theorem dens_le_sum (p : PotPair) (t : ℝ) : dens p t ≤ ‖coverRep38 p.1 t‖ + ‖coverRep38 p.2 t‖ := by
  unfold dens
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (coverRep38 p.1 t), norm_nonneg (coverRep38 p.2 t)]

theorem dens_aesm (p : PotPair) : AEStronglyMeasurable (dens p) volume := by
  have h1 : Measurable (fun t => ‖coverRep38 p.1 t‖) :=
    (stronglyMeasurable_coverRep38 p.1).measurable.norm
  have h2 : Measurable (fun t => ‖coverRep38 p.2 t‖) :=
    (stronglyMeasurable_coverRep38 p.2).measurable.norm
  exact (Real.continuous_sqrt.measurable.comp
    ((h1.pow_const 2).add (h2.pow_const 2))).aestronglyMeasurable

theorem dens_ii (p : PotPair) : IntervalIntegrable (dens p) volume 0 1 := by
  have h := (intervalIntegrable_coverRep38_one p.1).norm.add
    (intervalIntegrable_coverRep38_one p.2).norm
  refine h.mono_fun' (dens_aesm p).restrict ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  show ‖dens p t‖ ≤ ‖coverRep38 p.1 t‖ + ‖coverRep38 p.2 t‖
  rw [Real.norm_eq_abs, abs_of_nonneg (dens_nonneg p t)]
  exact dens_le_sum p t

theorem integral_dens_le (p : PotPair) :
    ∫ t in (0 : ℝ)..1, dens p t ≤ Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) := by
  have hnorm : ∀ t, ‖(dens p t : ℂ)‖ = dens p t := fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dens_nonneg p t)]
  have hint : IntervalIntegrable (fun t => ‖(dens p t : ℂ)‖ ^ 2) volume 0 1 := by
    simp only [hnorm, dens_sq]
    exact (intervalIntegrable_coverRep38_sq_one p.1).add (intervalIntegrable_coverRep38_sq_one p.2)
  have hm : AEStronglyMeasurable (fun t => (dens p t : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (dens_aesm p)
  have h := integral_norm_le_sqrt_mul (g := fun t => (dens p t : ℂ)) (a := 0) (b := 1)
    zero_le_one hm hint
  simp only [hnorm, dens_sq] at h
  rw [intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one p.1)
    (intervalIntegrable_coverRep38_sq_one p.2), integral_sq_coverRep38_one,
    integral_sq_coverRep38_one] at h
  simpa using h

theorem S_nonneg (p : PotPair) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ ∫ s in (0 : ℝ)..x, dens p s :=
  intervalIntegral.integral_nonneg hx (fun s _ => dens_nonneg p s)

theorem S_le (p : PotPair) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..x, dens p s ≤ Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) := by
  refine le_trans ?_ (integral_dens_le p)
  exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (Filter.Eventually.of_forall (fun s => dens_nonneg p s)) (dens_ii p)

theorem S_continuousOn (p : PotPair) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, dens p s) (Set.Icc (0 : ℝ) 1) := by
  have hfU : IntegrableOn (dens p) (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (dens_ii p)
  simpa [Set.uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval hfU

/-! ### the integral of a * S^j -/

theorem primOn_congr {f f' g g' : ℝ → ℂ} (h : PrimOn f g) (hf : ∀ t, f t = f' t)
    (hg : ∀ t, g t = g' t) : PrimOn f' g' := by
  have e1 : f = f' := funext hf
  have e2 : g = g' := funext hg
  subst e1; subst e2; exact h

theorem primOn_pow {a : ℝ → ℝ} (ha : IntervalIntegrable a volume 0 1) :
    ∀ j : ℕ, PrimOn (fun t : ℝ => ((∫ s in (0 : ℝ)..t, a s : ℝ) : ℂ) ^ (j + 1))
      (fun t => ((j + 1 : ℕ) : ℂ) * (a t : ℂ) * ((∫ s in (0 : ℝ)..t, a s : ℝ) : ℂ) ^ j) := by
  have haC : IntervalIntegrable (fun t => (a t : ℂ)) volume 0 1 :=
    ⟨ha.1.ofReal, ha.2.ofReal⟩
  have hS : PrimOn (fun t : ℝ => ((∫ s in (0 : ℝ)..t, a s : ℝ) : ℂ)) (fun t => (a t : ℂ)) := by
    refine primOn_congr (primOn_integral haC) (fun t => ?_) (fun t => rfl)
    exact intervalIntegral.integral_ofReal
  intro j
  induction j with
  | zero =>
      refine primOn_congr hS (fun t => ?_) (fun t => ?_) <;> simp
  | succ j ih =>
      refine primOn_congr (primOn_mul hS ih) (fun t => ?_) (fun t => ?_)
      · ring
      · push_cast; ring

theorem pow_integral {a : ℝ → ℝ} (ha : IntervalIntegrable a volume 0 1) (j : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..x, a t * (∫ s in (0 : ℝ)..t, a s) ^ j =
      (∫ s in (0 : ℝ)..x, a s) ^ (j + 1) / ((j : ℝ) + 1) := by
  have h := (primOn_pow ha j).2 x hx
  simp only [intervalIntegral.integral_same, Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero j),
    zero_add] at h
  apply Complex.ofReal_injective
  have hc : (((j : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ((j : ℝ) + 1) ≠ 0)
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  rw [eq_div_iff (by exact_mod_cast hc)]
  have h2 : ∫ t in (0 : ℝ)..x, ((j + 1 : ℕ) : ℂ) * (a t : ℂ) * ((∫ s in (0 : ℝ)..t, a s : ℝ) : ℂ) ^ j =
      ((j : ℂ) + 1) * ∫ t in (0 : ℝ)..x, (a t : ℂ) * ((∫ s in (0 : ℝ)..t, a s : ℝ) : ℂ) ^ j := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    push_cast; ring
  rw [h2] at h
  push_cast at h
  linear_combination -h

/-! ### entry bounds -/

theorem prod_aux {u c r n : ℂ} {X d b : ℝ} (hu : ‖u‖ ≤ X) (hc : ‖c‖ = 1) (hr : ‖r‖ ≤ d)
    (hn : ‖n‖ ≤ b) (hd : 0 ≤ d) (hX : 0 ≤ X) : ‖u * c * r * n‖ ≤ X * d * b := by
  rw [norm_mul, norm_mul, norm_mul, hc, mul_one]
  exact mul_le_mul (mul_le_mul hu hr (norm_nonneg _) hX) hn (norm_nonneg _) (mul_nonneg hX hd)

theorem phase_pos_le (lam : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (Complex.I * lam * (s : ℂ))‖ ≤ Real.exp (|lam.im| * s) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (Complex.I * lam * (s : ℂ)).re = (-lam.im) * s := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  exact mul_le_mul_of_nonneg_right (neg_le_abs lam.im) hs

theorem integrand_entry_le (lam : ℂ) (p : PotPair) {x t : ℝ} (htx : t ≤ x)
    (N : Matrix (Fin 2) (Fin 2) ℂ) {b : ℝ} (hN : ∀ k l, ‖N k l‖ ≤ b) (i j : Fin 2) :
    ‖(KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * N) i j‖ ≤
      Real.exp (|lam.im| * (x - t)) * dens p t * b := by
  have hs : 0 ≤ x - t := sub_nonneg.mpr htx
  have hb : 0 ≤ b := (norm_nonneg _).trans (hN 0 0)
  have hX : 0 ≤ Real.exp (|lam.im| * (x - t)) := (Real.exp_pos _).le
  have hD : 0 ≤ dens p t := dens_nonneg p t
  have hE1 := phase0_le lam hs
  have hE2 := phase_pos_le lam hs
  have h00 : ‖(KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * N) 0 0‖ ≤
      Real.exp (|lam.im| * (x - t)) * dens p t * b := by
    rw [KSPS003Support2.integrand_00]
    exact prod_aux hE1 Complex.norm_I (fst_le_dens p t) (hN 1 0) hD hX
  have h01 : ‖(KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * N) 0 1‖ ≤
      Real.exp (|lam.im| * (x - t)) * dens p t * b := by
    rw [KSPS003Support2.integrand_01]
    exact prod_aux hE1 Complex.norm_I (fst_le_dens p t) (hN 1 1) hD hX
  have h10 : ‖(KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * N) 1 0‖ ≤
      Real.exp (|lam.im| * (x - t)) * dens p t * b := by
    rw [KSPS003Support2.integrand_10]
    exact prod_aux hE2 (by simp) (snd_le_dens p t) (hN 0 0) hD hX
  have h11 : ‖(KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * N) 1 1‖ ≤
      Real.exp (|lam.im| * (x - t)) * dens p t * b := by
    rw [KSPS003Support2.integrand_11]
    exact prod_aux hE2 (by simp) (snd_le_dens p t) (hN 0 1) hD hX
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

/-! ### the iteration -/

theorem tail_entry_le (p : PotPair) (lam : ℂ) {K : ℝ}
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k l,
      ‖KSPSVolterra.term 3 t lam p k l‖ ≤ K * Real.exp (|lam.im| * t)) :
    ∀ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖KSPSVolterra.term (n + 3) x lam p i j‖ ≤
        K * Real.exp (|lam.im| * x) *
          ((∫ s in (0 : ℝ)..x, dens p s) ^ n / (n.factorial : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro x hx i j
      simpa using h3 x hx i j
  | succ n ih =>
      intro x hx i j
      have hx0 : 0 ≤ x := hx.1
      have e : (n + 1) + 3 = (n + 3) + 1 := by omega
      rw [e]
      have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hSc : ContinuousOn (fun t => (∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ))
          (Set.uIcc (0 : ℝ) x) := by
        have := ((S_continuousOn p).pow n).div_const (n.factorial : ℝ)
        exact this.mono (by rw [Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc le_rfl hx.2)
      have hdx : IntervalIntegrable (dens p) volume 0 x :=
        (dens_ii p).mono_set (by
          rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le zero_le_one]
          exact Set.Icc_subset_Icc le_rfl hx.2)
      have hII : IntervalIntegrable
          (fun t => dens p t * ((∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ)))
          volume 0 x := hdx.mul_continuousOn hSc
      have hg : IntervalIntegrable (fun t => K * Real.exp (|lam.im| * x) *
          (dens p t * ((∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ)))) volume 0 x :=
        hII.const_mul _
      have hle : ‖∫ t in (0 : ℝ)..x, (KSPSVolterra.E lam (x - t) * KSPSVolterra.R *
            KSPSVolterra.phi p t * KSPSVolterra.term (n + 3) t lam p) i j‖ ≤
          ∫ t in (0 : ℝ)..x, K * Real.exp (|lam.im| * x) *
            (dens p t * ((∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ))) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hx0 ?_ hg
        refine Filter.Eventually.of_forall (fun t ht => ?_)
        have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.trans hx.2⟩
        have hk := integrand_entry_le lam p ht.2 (KSPSVolterra.term (n + 3) t lam p)
          (fun k l => ih t ht1 k l) i j
        have hexp : Real.exp (|lam.im| * (x - t)) * Real.exp (|lam.im| * t) =
            Real.exp (|lam.im| * x) := by
          rw [← Real.exp_add]; congr 1; ring
        calc _ ≤ _ := hk
          _ = (Real.exp (|lam.im| * (x - t)) * Real.exp (|lam.im| * t)) *
                (K * (dens p t * ((∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ)))) := by ring
          _ = _ := by rw [hexp]; ring
      have hval : ∫ t in (0 : ℝ)..x, K * Real.exp (|lam.im| * x) *
            (dens p t * ((∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ))) =
          K * Real.exp (|lam.im| * x) *
            ((∫ s in (0 : ℝ)..x, dens p s) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have e1 : ∀ t : ℝ, dens p t * ((∫ s in (0 : ℝ)..t, dens p s) ^ n / (n.factorial : ℝ)) =
            (dens p t * (∫ s in (0 : ℝ)..t, dens p s) ^ n) / (n.factorial : ℝ) := fun t => by ring
        simp only [e1]
        rw [intervalIntegral.integral_div, pow_integral (dens_ii p) n hx, Nat.factorial_succ]
        push_cast
        field_simp
      exact hle.trans hval.le

theorem tail_summable_bound (p : PotPair) (lam : ℂ) {K : ℝ}
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k l,
      ‖KSPSVolterra.term 3 t lam p k l‖ ≤ K * Real.exp (|lam.im| * t))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    Summable (fun n : ℕ => KSPSVolterra.term (n + 3) x lam p i j) ∧
      ‖∑' n : ℕ, KSPSVolterra.term (n + 3) x lam p i j‖ ≤
        K * Real.exp (|lam.im| * x) * Real.exp (Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)) := by
  have hK : 0 ≤ K := by
    have := h3 0 ⟨le_rfl, zero_le_one⟩ 0 0
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set S : ℝ := ∫ s in (0 : ℝ)..x, dens p s with hSdef
  have hexp : HasSum (fun n : ℕ => S ^ n / (n.factorial : ℝ)) (Real.exp S) := by
    have := NormedSpace.expSeries_div_hasSum_exp S
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hb : HasSum (fun n : ℕ => K * Real.exp (|lam.im| * x) * (S ^ n / (n.factorial : ℝ)))
      (K * Real.exp (|lam.im| * x) * Real.exp S) := hexp.mul_left _
  have hbound : ∀ n : ℕ, ‖KSPSVolterra.term (n + 3) x lam p i j‖ ≤
      K * Real.exp (|lam.im| * x) * (S ^ n / (n.factorial : ℝ)) :=
    fun n => tail_entry_le p lam h3 n x hx i j
  refine ⟨Summable.of_norm_bounded hb.summable hbound, ?_⟩
  refine (tsum_of_norm_bounded hb hbound).trans ?_
  have h1 : Real.exp S ≤ Real.exp (Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)) :=
    Real.exp_le_exp.mpr (S_le p hx)
  exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (Real.exp_pos _).le)

/-! ### operator norms of 2x2 matrices -/

theorem m3_entry_le (φ : SobolevC 1) (x : ℝ) (lam : ℂ) (i j : Fin 2) :
    ‖volterraTerm 3 x lam φ i j‖ ≤ ‖volterraTerm 3 x lam φ‖ := by
  set M := volterraTerm 3 x lam φ with hM
  have h00 : M 0 0 = 0 := volterra3_00 φ x lam
  have h11 : M 1 1 = 0 := volterra3_11 φ x lam
  have e : (Matrix.diagonal ![M 0 1, M 1 0] : Matrix (Fin 2) (Fin 2) ℂ) = M * !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11]
  have hn : ‖(![M 0 1, M 1 0] : Fin 2 → ℂ)‖ ≤ ‖M‖ := by
    rw [← Matrix.l2_opNorm_diagonal, e]
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    have := swap_norm_le
    nlinarith [norm_nonneg M]
  have hpi : ∀ a, ‖(![M 0 1, M 1 0] : Fin 2 → ℂ) a‖ ≤ ‖M‖ :=
    fun a => (norm_le_pi_norm _ a).trans hn
  fin_cases i <;> fin_cases j
  · simp [h00]
  · simpa using hpi 0
  · simpa using hpi 1
  · simp [h11]

theorem opNorm_le_two (A : Matrix (Fin 2) (Fin 2) ℂ) {B : ℝ} (h : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A‖ ≤ 2 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0 0)
  have e : A = Matrix.diagonal ![A 0 0, A 1 1] + !![0, A 0 1; A 1 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h1 : ‖(Matrix.diagonal ![A 0 0, A 1 1] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ B := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hB).2
      (Fin.forall_fin_two.2 ⟨by simpa using h 0 0, by simpa using h 1 1⟩)
  have h2 := antidiag_norm_le (h 0 1) (h 1 0)
  calc ‖A‖ = ‖Matrix.diagonal ![A 0 0, A 1 1] + !![0, A 0 1; A 1 0, 0]‖ := by rw [← e]
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * B := by linarith

/-! ### the entrywise decomposition and the assembled bound -/

theorem fundamentalRemainder_entry (φ : SobolevC 1) (x : ℝ) (lam : ℂ)
    (hs : ∀ i j, Summable (fun n : ℕ => KSPSVolterra.term (n + 3) x lam (KSPSVolterra.toPair φ) i j))
    (i j : Fin 2) :
    fundamentalRemainder φ x lam i j = secondVolterraRemainder φ x lam i j +
      ∑' n : ℕ, KSPSVolterra.term (n + 3) x lam (KSPSVolterra.toPair φ) i j := by
  have hsumm : Summable (fun k : ℕ => KSPSVolterra.term k x lam (KSPSVolterra.toPair φ) i j) :=
    (summable_nat_add_iff 3).mp (hs i j)
  have hsplit := hsumm.sum_add_tsum_nat_add 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  have hF : KSPSVolterra.fundamental φ x lam i j =
      ∑' k : ℕ, KSPSVolterra.term k x lam (KSPSVolterra.toPair φ) i j := rfl
  have h0 : freePropagator x lam i j = KSPSVolterra.term 0 x lam (KSPSVolterra.toPair φ) i j := rfl
  have h1 : volterraTerm 1 x lam φ i j = KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) i j := rfl
  have h2 : volterraTerm 2 x lam φ i j = KSPSVolterra.term 2 x lam (KSPSVolterra.toPair φ) i j := rfl
  unfold fundamentalRemainder secondVolterraRemainder
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hF, h0, h1, h2, ← hsplit]
  ring

theorem assembled_bound (φ : SobolevC 1) {C3 C4 : ℝ} (hC3 : 0 < C3) (hC4 : 0 < C4)
    (h3 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ lam : ℂ, lam ≠ 0 →
      ‖secondVolterraRemainder φ x lam‖ ≤
        C3 * Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2)
    (h4 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ lam : ℂ, lam ≠ 0 →
      ‖volterraTerm 3 x lam φ‖ ≤
        C4 * Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ} (hlam : lam ≠ 0) :
    ‖fundamentalRemainder φ x lam‖ ≤
      (C3 + 2 * C4) * Real.exp (|lam.im| * x + l2Norm φ) * sobolevNorm 1 φ ^ 2 *
        (1 + sobolevNorm 1 φ) / ‖lam‖ ^ 2 := by
  set A : ℝ := sobolevNorm 1 φ with hA
  set L : ℝ := ‖lam‖ with hL
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hLpos : 0 < L := norm_pos_iff.mpr hlam
  set K : ℝ := C4 * A ^ 3 / L ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hk3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k l,
      ‖KSPSVolterra.term 3 t lam (KSPSVolterra.toPair φ) k l‖ ≤ K * Real.exp (|lam.im| * t) := by
    intro t ht k l
    refine (m3_entry_le φ t lam k l).trans ((h4 t ht lam hlam).trans (le_of_eq ?_))
    rw [hK]; ring
  have hts := fun i j => tail_summable_bound (KSPSVolterra.toPair φ) lam hk3 hx i j
  have hsum := fun i j => (hts i j).1
  set T : Matrix (Fin 2) (Fin 2) ℂ :=
    fun i j => ∑' n : ℕ, KSPSVolterra.term (n + 3) x lam (KSPSVolterra.toPair φ) i j with hT
  have hdecomp : fundamentalRemainder φ x lam = secondVolterraRemainder φ x lam + T := by
    ext i j
    rw [Matrix.add_apply]
    exact fundamentalRemainder_entry φ x lam hsum i j
  have hl2 : Real.sqrt (‖(KSPSVolterra.toPair φ).1‖ ^ 2 + ‖(KSPSVolterra.toPair φ).2‖ ^ 2) = l2Norm φ := rfl
  have hTn : ‖T‖ ≤ 2 * (K * Real.exp (|lam.im| * x) * Real.exp (l2Norm φ)) := by
    refine opNorm_le_two T (fun i j => ?_)
    have := (hts i j).2
    rwa [hl2] at this
  have h3x := h3 x hx lam hlam
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have hE1 : 0 < Real.exp (|lam.im| * x) := Real.exp_pos _
  have hE2 : 1 ≤ Real.exp (l2Norm φ) := Real.one_le_exp (Real.sqrt_nonneg _)
  have hexp : Real.exp (|lam.im| * x + l2Norm φ) =
      Real.exp (|lam.im| * x) * Real.exp (l2Norm φ) := Real.exp_add _ _
  have hfin : C3 * Real.exp (|lam.im| * x) * A ^ 2 / L ^ 2 +
      2 * (K * Real.exp (|lam.im| * x) * Real.exp (l2Norm φ)) ≤
      (C3 + 2 * C4) * Real.exp (|lam.im| * x + l2Norm φ) * A ^ 2 * (1 + A) / L ^ 2 := by
    rw [hexp, hK]
    have hnum : C3 * Real.exp (|lam.im| * x) * A ^ 2 +
        2 * C4 * A ^ 3 * Real.exp (|lam.im| * x) * Real.exp (l2Norm φ) ≤
        (C3 + 2 * C4) * (Real.exp (|lam.im| * x) * Real.exp (l2Norm φ)) * A ^ 2 * (1 + A) := by
      have hP : 0 ≤ Real.exp (|lam.im| * x) * A ^ 2 := by positivity
      have hE20 : 0 ≤ Real.exp (l2Norm φ) := (zero_le_one.trans hE2)
      nlinarith [mul_nonneg (mul_nonneg hC3.le hP) (sub_nonneg.2 hE2),
        mul_nonneg (mul_nonneg hC3.le hP) (mul_nonneg hE20 hA0),
        mul_nonneg (mul_nonneg hC4.le hP) hE20]
    have e1 : C3 * Real.exp (|lam.im| * x) * A ^ 2 / L ^ 2 +
        2 * (C4 * A ^ 3 / L ^ 2 * Real.exp (|lam.im| * x) * Real.exp (l2Norm φ)) =
        (C3 * Real.exp (|lam.im| * x) * A ^ 2 +
          2 * C4 * A ^ 3 * Real.exp (|lam.im| * x) * Real.exp (l2Norm φ)) / L ^ 2 := by ring
    rw [e1]
    gcongr
  exact (add_le_add h3x hTn).trans hfin

end NlsGge.ThirdConsultation.KSPS005Support
end
