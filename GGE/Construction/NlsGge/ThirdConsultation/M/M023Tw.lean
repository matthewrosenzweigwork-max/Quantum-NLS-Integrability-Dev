import Mathlib
import NlsGge.ThirdConsultation.M.M023Host
import NlsGge.ThirdConsultation.M.M023Bridge
import NlsGge.ThirdConsultation.M.M023Kernel1
import NlsGge.ThirdConsultation.M.M023Kernel2
import NlsGge.ThirdConsultation.M.M023Kernel3
import NlsGge.Atomic.M.M021
import NlsGge.Atomic.M.M022
import NlsGge.Atomic.KST.KST004

   
                                                                                                

                                                                                                                     
                                                                                                                               
                                                                                                                      
                                                                                                
  

set_option autoImplicit false

open scoped ENNReal BigOperators BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

open NlsGge.ThirdConsultation.MTwoMode

theorem w_submul_of_oneDerivative (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) :
    NlsGge.Atomic.DM046.SubmultiplicativeWeight w := by
  obtain ⟨v, hv1, _, hsub, hwv⟩ := hw
  intro k l
  rw [hwv, hwv, hwv]
  have h1 := NlsGge.ThirdConsultation.M.M022.indexWeight_add_le k l
  have h2 : v (k + l) ≤ v k * v l := hsub k l
  have hi : 0 ≤ NlsGge.Atomic.M.M054.indexWeight (k + l) := by
    unfold NlsGge.Atomic.M.M054.indexWeight; positivity
  have hv0 : 0 ≤ v (k + l) := le_trans zero_le_one (hv1 _)
  have hik : 0 ≤ NlsGge.Atomic.M.M054.indexWeight k := by
    unfold NlsGge.Atomic.M.M054.indexWeight; positivity
  have hil : 0 ≤ NlsGge.Atomic.M.M054.indexWeight l := by
    unfold NlsGge.Atomic.M.M054.indexWeight; positivity
  calc NlsGge.Atomic.M.M054.indexWeight (k + l) * v (k + l)
      ≤ (NlsGge.Atomic.M.M054.indexWeight k * NlsGge.Atomic.M.M054.indexWeight l) * (v k * v l) :=
        mul_le_mul h1 h2 hv0 (mul_nonneg hik hil)
    _ = (NlsGge.Atomic.M.M054.indexWeight k * v k) * (NlsGge.Atomic.M.M054.indexWeight l * v l) := by ring

/-! ### The multiplier sequence -/

/-- `|l-n| · c_lam(l)`, the bounded multiplier whose product with `1/|l-n|` is the complementary resolvent coefficient. -/
def gFun (n : ℤ) (lam : ℂ) (l : ℤ) : ℂ :=
  (((l - n).natAbs : ℝ) : ℂ) * NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l

theorem gFun_bound (n : ℤ) (lam : ℂ) (h : |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 + 1) (l : ℤ) :
    ‖gFun n lam l‖ ≤ 2 := by
  by_cases hl : l = n
  · subst hl
    simp [gFun, NlsGge.Atomic.KST004.complementaryResolventCoeff]
  · have hd : (1 : ℝ) ≤ ((l - n).natAbs : ℝ) := by
      have : 0 < (l - n).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hl)
      exact_mod_cast this
    have hpi := Real.pi_gt_three
    set d : ℝ := ((l - n).natAbs : ℝ) with hdd
    have hdist : |(l : ℝ) * Real.pi - (n : ℝ) * Real.pi| = d * Real.pi := by
      dsimp [d]
      rw [← sub_mul, ← Int.cast_sub, Nat.cast_natAbs, Int.cast_abs,
        Int.cast_sub, abs_mul, abs_of_pos Real.pi_pos]
    have htri : |(l : ℝ) * Real.pi - (n : ℝ) * Real.pi| ≤
        |(l : ℝ) * Real.pi - lam.re| + |lam.re - (n : ℝ) * Real.pi| := by
      have heq : (l : ℝ) * Real.pi - (n : ℝ) * Real.pi =
          ((l : ℝ) * Real.pi - lam.re) + (lam.re - (n : ℝ) * Real.pi) := by ring
      rw [heq]
      exact abs_add_le _ _
    rw [hdist, abs_sub_comm ((l : ℝ) * Real.pi) lam.re] at htri
    have hre : d / 2 ≤ |lam.re - (l : ℝ) * Real.pi| := by
      nlinarith [hpi, hd]
    have hcn := Complex.abs_re_le_norm (lam - (l : ℂ) * (Real.pi : ℂ))
    have hre2 : (lam - (l : ℂ) * (Real.pi : ℂ)).re = lam.re - (l : ℝ) * Real.pi := by
      simp [Complex.mul_re]
    rw [hre2] at hcn
    have hden : d / 2 ≤ ‖lam - (l : ℂ) * (Real.pi : ℂ)‖ := le_trans hre hcn
    have hdpos : 0 < d / 2 := by linarith
    have hnorm : ‖gFun n lam l‖ = d * ‖lam - (l : ℂ) * (Real.pi : ℂ)‖⁻¹ := by
      simp only [gFun, NlsGge.Atomic.KST004.complementaryResolventCoeff, if_neg hl, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, norm_inv]
      rw [abs_of_nonneg (by positivity)]
    rw [hnorm, ← div_eq_mul_inv, div_le_iff₀ (lt_of_lt_of_le hdpos hden)]
    linarith

/-- The bounded multiplier: the formula on the region `|Re lam - n pi| <= pi/2 + 1`, `0` elsewhere (a chosen extension). -/
def gC (n : ℤ) (lam : ℂ) : ℤ →ᵇ ℂ :=
  if h : |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 + 1 then
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (gFun n lam) 2 (gFun_bound n lam h)
  else 0

theorem gC_apply (n : ℤ) (lam : ℂ) (h : |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 + 1) (l : ℤ) :
    gC n lam l = gFun n lam l := by
  unfold gC
  rw [dif_pos h]
  rfl

theorem strip_mem_region (n : ℤ) (lam : ℂ) (h : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 + 1 := by
  have h1 : |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 := h
  linarith

theorem eSeq_mul_gFun (n : ℤ) (lam : ℂ) (l : ℤ) :
    (eSeq n l : ℂ) * gFun n lam l = NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l := by
  by_cases hl : l = n
  · subst hl
    simp [eSeq, gFun, NlsGge.Atomic.KST004.complementaryResolventCoeff]
  · have hd : ((l - n).natAbs : ℝ) ≠ 0 := by
      have : 0 < (l - n).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hl)
      exact_mod_cast this.ne'
    simp only [eSeq, gFun, if_neg hl]
    rw [← mul_assoc]
    have : ((1 / ((l - n).natAbs : ℝ) : ℝ) : ℂ) * (((l - n).natAbs : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      rw [one_div, inv_mul_cancel₀ hd]
      simp
    rw [this, one_mul]

theorem Dm_gC (n : ℤ) (lam : ℂ) (h : |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 + 1)
    (b : Bool) (l : ℤ) :
    Dm n (gC n lam) b l =
      NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (if b then l else -l) := by
  cases b
  · simp only [Dm, Bool.false_eq_true, ite_false]
    rw [gC_apply n lam h, eSeq_mul_gFun]
  · simp only [Dm, ite_true]
    rw [gC_apply n lam h, eSeq_mul_gFun]

/-! ### The transported operator -/

variable (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (n : ℤ)

def Tw (p : ℂ × PotentialCode w) : SourceCode w n →L[ℂ] SourceCode w n :=
  Bop w hw (w_submul_of_oneDerivative w hw) n p.2 (gC n p.1)

theorem Tw_kernel (p : ℂ × PotentialCode w) (hp : p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (x : SourceCode w n) (j : Bool × ℤ) :
    Tw w hw n p x j = kernel w n p.1 p.2 x j := by
  have hreg := strip_mem_region n p.1 hp
  unfold Tw kernel
  rw [Bop_apply]
  unfold kernFun
  congr 1
  refine tsum_congr fun l => ?_
  rw [Dm_gC n p.1 hreg]

theorem raw_eq_pc (hw1 : ∀ k : ℤ, 1 ≤ w k) (a : PotentialCode w) (φ : NlsGge.GK38.PotPair)
    (hp : RepresentsPotential w a φ) (b : Bool) (m : ℤ) :
    potentialRaw w a b m = potentialCoefficientPair φ b m := by
  by_cases he : Even m
  · obtain ⟨r, hr⟩ := he
    have hm : m = 2 * r := by omega
    subst hm
    rw [potentialRaw_two_mul, hp b r]
    have : (w (2 * r) : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le one_pos (hw1 _)).ne'
    field_simp
  · rw [potentialRaw_odd w a b m he]
    symm
    apply pc_odd
    intro h0
    exact he (Int.even_iff.mpr h0)

theorem Tw_represents (p : ℂ × PotentialCode w) (φ : NlsGge.GK38.PotPair)
    (f : NlsGge.Atomic.KST003.KSTPairL2) (x : SourceCode w n)
    (hlam : p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hφ : RepresentsPotential w p.2 φ) (hx : RepresentsSource w n x f) :
    RepresentsSource w n (Tw w hw n p x) (NlsGge.ThirdConsultation.MTwoMode.T φ n p.1 hlam f) := by
  have hw1 := w_ge_one_of_oneDerivative w hw
  intro b k
  rw [Tw_kernel w hw n p hlam x (b, k)]
  have hTc : coefficientPair (NlsGge.ThirdConsultation.MTwoMode.T φ n p.1 hlam f) b k =
      Tcoeff φ n p.1 hlam f b k := rfl
  rw [hTc, Tcoeff_eq_kernel φ n p.1 hlam f b k]
  unfold kernel
  simp only
  congr 1
  refine tsum_congr fun l => ?_
  rw [raw_eq_pc w hw1 p.2 φ hφ b (k - l)]
  congr 2
  have hW : (shiftWeight w n (!b) l : ℂ) ≠ 0 := by
    have : 1 ≤ shiftWeight w n (!b) l := by
      unfold shiftWeight
      split_ifs <;> exact hw1 _
    exact_mod_cast (lt_of_lt_of_le one_pos this).ne'
  rw [hx (!b) l, mul_div_cancel_left₀ _ hW]

theorem Tw_sq_bound (p : ℂ × PotentialCode w) (hlam : p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hth : 8 * ‖p.2‖ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    ‖Tw w hw n p * Tw w hw n p‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨_, b2, b3, _, b5, b6⟩ := weighted_code_bridges w hw n
  obtain ⟨φ, hφ, _⟩ := b2 p.2
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  obtain ⟨f, hf, _⟩ := b5 x
  have hr1 := Tw_represents w hw n p φ f x hlam hφ hf
  have hr2 := Tw_represents w hw n p φ _ (Tw w hw n p x) hlam hφ hr1
  obtain ⟨hEφ, hNφ⟩ := b3 p.2 φ hφ
  obtain ⟨hEf, hNf⟩ := b6 x f hf
  obtain ⟨_, hNN⟩ := b6 (Tw w hw n p (Tw w hw n p x)) _ hr2
  have hsq := NlsGge.ThirdConsultation.M.T_squared_bound w hw φ
    (by rw [hEφ]; exact ENNReal.ofReal_ne_top) n p.1 hlam f
    (by rw [hEf]; exact ENNReal.ofReal_ne_top)
  rw [hNN, hNφ, hNf] at hsq
  have hρ : 0 < NlsGge.Atomic.M.M054.indexWeight n := by
    unfold NlsGge.Atomic.M.M054.indexWeight; positivity
  have hc : 4 * ‖p.2‖ ^ 2 / NlsGge.Atomic.M.M054.indexWeight n ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]; linarith
  calc ‖(Tw w hw n p * Tw w hw n p) x‖ = ‖Tw w hw n p (Tw w hw n p x)‖ := rfl
    _ ≤ (4 * ‖p.2‖ ^ 2 / NlsGge.Atomic.M.M054.indexWeight n) * ‖x‖ := hsq.2
    _ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-! ### Neumann algebra on the carrier -/

theorem neumann_of_small (T : SourceCode w n →L[ℂ] SourceCode w n) (hsmall : ‖T * T‖ ≤ (1 / 2 : ℝ)) :
    HasSum (fun j : ℕ => (T * T) ^ j) (evenNeumann T) ∧ ‖evenNeumann T‖ ≤ 2 ∧
      (1 - T) * fullNeumann T = 1 ∧ fullNeumann T * (1 - T) = 1 := by
  have hS1 : ‖T * T‖ < 1 := lt_of_le_of_lt hsmall (by norm_num)
  have hsum : Summable fun j : ℕ => (T * T) ^ j := summable_geometric_of_norm_lt_one hS1
  have hR : (1 - T * T) * (∑' j : ℕ, (T * T) ^ j) = 1 := mul_neg_geom_series (T * T) hS1
  have hcomm : Commute (∑' j : ℕ, (T * T) ^ j) T :=
    Commute.tsum_left T fun j => ((Commute.refl T).mul_left (Commute.refl T)).pow_left j
  have hEc : (∑' j : ℕ, (T * T) ^ j) * (1 - T) = (1 - T) * (∑' j : ℕ, (T * T) ^ j) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcomm.eq]
  have hTT : (1 - T) * (1 + T) = 1 - T * T := by
    rw [sub_mul, one_mul, mul_add, mul_one]; abel
  have hTT' : (1 + T) * (1 - T) = 1 - T * T := by
    rw [add_mul, one_mul, mul_sub, mul_one]; abel
  refine ⟨hsum.hasSum, ?_, ?_, ?_⟩
  · have hnorm : ∀ j : ℕ, ‖(T * T) ^ j‖ ≤ ((1 : ℝ) / 2) ^ j := by
      intro j
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        rw [pow_zero, pow_zero]
        exact ContinuousLinearMap.norm_id_le
      · exact (norm_pow_le' (T * T) hpos).trans (pow_le_pow_left₀ (norm_nonneg _) hsmall j)
    exact tsum_of_norm_bounded hasSum_geometric_two hnorm
  · unfold fullNeumann evenNeumann
    rw [← mul_assoc, hTT, hR]
  · unfold fullNeumann evenNeumann
    rw [mul_assoc, hEc, ← mul_assoc, hTT', hR]

theorem Tw_neumann (p : ℂ × PotentialCode w) (hlam : p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hth : 8 * ‖p.2‖ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    ‖Tw w hw n p * Tw w hw n p‖ ≤ (1 / 2 : ℝ) ∧
      HasSum (fun j : ℕ => (Tw w hw n p * Tw w hw n p) ^ j) (evenNeumann (Tw w hw n p)) ∧
      ‖evenNeumann (Tw w hw n p)‖ ≤ 2 ∧
      (1 - Tw w hw n p) * fullNeumann (Tw w hw n p) = 1 ∧
      fullNeumann (Tw w hw n p) * (1 - Tw w hw n p) = 1 := by
  have h := Tw_sq_bound w hw n p hlam hth
  obtain ⟨h1, h2, h3, h4⟩ := neumann_of_small w n (Tw w hw n p) h
  exact ⟨h, h1, h2, h3, h4⟩

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
