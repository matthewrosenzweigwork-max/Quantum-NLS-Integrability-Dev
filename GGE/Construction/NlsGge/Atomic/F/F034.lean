                                                                                                                                                                                                                                                   
                                       
import Mathlib

                                                     
                                                             
                                                                               
                                                                              
                                                                            
                                                                    

set_option autoImplicit false

open Filter Set
open scoped Topology ContDiff

namespace NlsGge.ThirdConsultation.F
noncomputable section

def IsCuspCutoff (η : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧
  Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4) ∧
  ∀ x : ℝ, |x| ≤ (1 : ℝ) / 8 → η x = 1

def cutoffCusp (η : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  ∑' k : ℤ, η (x - (k : ℝ)) *
    ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)

def cutoffCuspDensity (η : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  14 * (cutoffCusp η ε x) ^ 2 * (iteratedDeriv 2 (cutoffCusp η ε) x) ^ 2 -
    7 * (deriv (cutoffCusp η ε) x) ^ 4

theorem cusp_term_contDiff (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (ε : ℝ) (hε : 0 < ε) (k : ℤ) :
    ContDiff ℝ ∞ (fun x : ℝ => η (x - (k : ℝ)) * ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => x - (k : ℝ)) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => η (x - (k : ℝ))) := hη.comp h1
  have h3 : ContDiff ℝ ∞ (fun x : ℝ => (x - (k : ℝ)) ^ 2 + ε ^ 2) :=
    (h1.pow 2).add contDiff_const
  have h4 : ContDiff ℝ ∞ (fun x : ℝ => ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) :=
    h3.rpow_const_of_ne (fun x => (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)).ne')
  exact h2.mul h4

/-- A term vanishes when `x - k` lies outside `(-1/4, 1/4)`, in particular for `k` far from
the window around `x0`. -/
theorem far_zero (η : ℝ → ℝ) (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4))
    (x x0 : ℝ) (hx : |x - x0| < 1) (M : ℕ) (hM : |x0| + 2 ≤ (M : ℝ)) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(M : ℤ)) M) : η (x - (k : ℝ)) = 0 := by
  have hyout : x - (k : ℝ) ≤ -1 / 4 ∨ 1 / 4 ≤ x - (k : ℝ) := by
    rw [Finset.mem_Icc] at hk
    have hx' := abs_lt.1 hx
    have hx0 := le_abs_self x0
    have hx0' := neg_abs_le x0
    rcases (show k < -(M : ℤ) ∨ (M : ℤ) < k by omega) with h | h
    · right
      have hk' : (k : ℝ) ≤ -(M : ℝ) - 1 := by
        have : k ≤ -(M : ℤ) - 1 := by omega
        exact_mod_cast this
      linarith [hx'.1, hx'.2, hx0', hM]
    · left
      have hk' : (M : ℝ) + 1 ≤ (k : ℝ) := by
        have : (M : ℤ) + 1 ≤ k := by omega
        exact_mod_cast this
      linarith [hx'.1, hx'.2, hx0, hM]
  by_contra hne
  have hmem : x - (k : ℝ) ∈ Function.support η := hne
  have hI := hsupp hmem
  rcases hyout with h | h <;> linarith [hI.1, hI.2]

theorem cutoffCusp_eq_finite (η : ℝ → ℝ)
    (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4))
    (ε x0 : ℝ) (M : ℕ) (hM : |x0| + 2 ≤ (M : ℝ)) (x : ℝ) (hx : |x - x0| < 1) :
    cutoffCusp η ε x = ∑ k ∈ Finset.Icc (-(M : ℤ)) M,
      η (x - (k : ℝ)) * ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) := by
  unfold cutoffCusp
  apply tsum_eq_sum
  intro k hk
  rw [far_zero η hsupp x x0 hx M hM k hk, zero_mul]

theorem cutoffCusp_contDiff (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4)) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (cutoffCusp η ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x0
  obtain ⟨M, hM⟩ := exists_nat_ge (|x0| + 2)
  have hfin : ContDiff ℝ ∞ (fun x : ℝ => ∑ k ∈ Finset.Icc (-(M : ℤ)) M,
      η (x - (k : ℝ)) * ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) :=
    ContDiff.sum (fun k _ => cusp_term_contDiff η hη ε hε k)
  refine ContDiffAt.congr_of_eventuallyEq hfin.contDiffAt ?_
  filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  exact cutoffCusp_eq_finite η hsupp ε x0 M hM x hx

theorem cutoffCusp_periodic (η : ℝ → ℝ) (ε : ℝ) : Function.Periodic (cutoffCusp η ε) 1 := by
  intro x
  unfold cutoffCusp
  refine Eq.trans ?_ ((Equiv.addRight (-1 : ℤ)).tsum_eq _)
  apply tsum_congr
  intro k
  have e : x + 1 - (k : ℝ) = x - ((k + -1 : ℤ) : ℝ) := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [e]

theorem cutoffCusp_summable (η : ℝ → ℝ)
    (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4)) (ε x : ℝ) :
    Summable (fun k : ℤ => η (x - (k : ℝ)) * ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (|x| + 2)
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(M : ℤ)) M) (fun k hk => ?_)
  rw [far_zero η hsupp x x (by simp) M hM k hk, zero_mul]


theorem eta_zero_of_far (η : ℝ → ℝ) (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4))
    (y : ℝ) (hy : 1 / 4 ≤ |y|) : η y = 0 := by
  by_contra hne
  have hI := hsupp (Function.mem_support.2 hne)
  have hlt : |y| < 1 / 4 := abs_lt.2 ⟨by linarith [hI.1], by linarith [hI.2]⟩
  linarith

theorem cusp_closed (η : ℝ → ℝ)
    (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4))
    (hone : ∀ x : ℝ, |x| ≤ (1 : ℝ) / 8 → η x = 1) (ε x : ℝ) (hx : |x| < 1 / 8) :
    cutoffCusp η ε x = (x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) := by
  unfold cutoffCusp
  rw [tsum_eq_single 0]
  · simp [hone x hx.le]
  · intro k hk
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have := Int.one_le_abs hk
      exact_mod_cast this
    have h1 := abs_sub_abs_le_abs_sub (k : ℝ) x
    rw [abs_sub_comm] at h1
    have hfar : 1 / 4 ≤ |x - (k : ℝ)| := by linarith
    rw [eta_zero_of_far η hsupp _ hfar, zero_mul]

theorem hasDerivAt_closed (ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (fun z : ℝ => (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8))
      ((3 : ℝ) / 4 * y * (y ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) y := by
  have hs : (0 : ℝ) < y ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg y) (pow_pos hε 2)
  have hf : HasDerivAt (fun z : ℝ => z ^ 2 + ε ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (ε ^ 2)
  have h := hf.rpow_const (p := (3 : ℝ) / 8) (Or.inl hs.ne')
  have e : (3 : ℝ) / 8 - 1 = -(5 : ℝ) / 8 := by norm_num
  exact h.congr_deriv (by rw [e]; ring)

theorem deriv_closed (ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    deriv (fun z : ℝ => (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) y =
      (3 : ℝ) / 4 * y * (y ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8) :=
  (hasDerivAt_closed ε hε y).deriv

theorem hasDerivAt_second (ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (fun z : ℝ => (3 : ℝ) / 4 * z * (z ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8))
      ((3 : ℝ) / 16 * (4 * ε ^ 2 - y ^ 2) * (y ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) y := by
  have hs : (0 : ℝ) < y ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg y) (pow_pos hε 2)
  have hf : HasDerivAt (fun z : ℝ => z ^ 2 + ε ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (ε ^ 2)
  have hA := hf.rpow_const (p := -(5 : ℝ) / 8) (Or.inl hs.ne')
  have hL : HasDerivAt (fun z : ℝ => (3 : ℝ) / 4 * z) ((3 : ℝ) / 4) y := by
    simpa using (hasDerivAt_id y).const_mul ((3 : ℝ) / 4)
  have hP := hL.mul hA
  have e : -(5 : ℝ) / 8 - 1 = -(13 : ℝ) / 8 := by norm_num
  have hsplit : (y ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8) =
      (y ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8) * (y ^ 2 + ε ^ 2) := by
    rw [← Real.rpow_add_one hs.ne']
    norm_num
  refine hP.congr_deriv ?_
  rw [e, hsplit]
  ring

theorem cusp_deriv_closed_values (η : ℝ → ℝ)
    (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4))
    (hone : ∀ x : ℝ, |x| ≤ (1 : ℝ) / 8 → η x = 1) (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : |x| < 1 / 8) :
    cutoffCusp η ε x = (x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) ∧
    deriv (cutoffCusp η ε) x = (3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8) ∧
    iteratedDeriv 2 (cutoffCusp η ε) x =
      (3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8) := by
  have hopen : {y : ℝ | |y| < 1 / 8} ∈ 𝓝 x :=
    IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hx
  have hev : cutoffCusp η ε =ᶠ[𝓝 x] fun z : ℝ => (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) := by
    filter_upwards [hopen] with z hz
    exact cusp_closed η hsupp hone ε z hz
  have hd : deriv (cutoffCusp η ε) =ᶠ[𝓝 x] deriv (fun z : ℝ => (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) :=
    hev.deriv
  refine ⟨?_, ?_, ?_⟩
  · exact hev.self_of_nhds
  · rw [hev.deriv_eq, deriv_closed ε hε x]
  · rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [hd.deriv_eq]
    have hdd : deriv (fun z : ℝ => (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) =
        fun z : ℝ => (3 : ℝ) / 4 * z * (z ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8) :=
      funext fun z => deriv_closed ε hε z
    rw [hdd]
    exact (hasDerivAt_second ε hε x).deriv


theorem pow_neg3_eq (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ (-(3 : ℝ)) = 1 / (1 + t) ^ 3 := by
  rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
    Real.rpow_natCast, one_div]

theorem q_lower (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - 3 * t ≤ (1 + t) ^ (-(5 : ℝ) / 2) := by
  have hp : (0 : ℝ) < (1 + t) ^ 3 := by positivity
  have h1 : 1 - 3 * t ≤ 1 / (1 + t) ^ 3 := by
    rw [le_div_iff₀ hp]
    nlinarith [sq_nonneg t, mul_nonneg ht0 (sq_nonneg t), mul_nonneg (mul_nonneg ht0 ht0) (sq_nonneg t)]
  have h2 : (1 + t) ^ (-(3 : ℝ)) ≤ (1 + t) ^ (-(5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [pow_neg3_eq t ht0] at h2
  linarith

theorem q_le_one (t : ℝ) (ht0 : 0 ≤ t) : (1 + t) ^ (-(5 : ℝ) / 2) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)

theorem q_nonneg (t : ℝ) (ht0 : 0 ≤ t) : 0 ≤ (1 + t) ^ (-(5 : ℝ) / 2) :=
  Real.rpow_nonneg (by linarith) _

theorem q_abs_sub_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(1 + t) ^ (-(5 : ℝ) / 2) - 1| ≤ 3 * t := by
  have h1 := q_lower t ht0 ht1
  have h2 := q_le_one t ht0
  rw [abs_le]
  constructor <;> linarith

theorem q_weighted_sub_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) - 1| ≤ 11 * t := by
  set q := (1 + t) ^ (-(5 : ℝ) / 2) with hq
  have h1 := q_lower t ht0 ht1
  have h2 := q_le_one t ht0
  have h3 := q_nonneg t ht0
  have e : (4 * t - 1) ^ 2 * q - 1 = (16 * t ^ 2 - 8 * t) * q + (q - 1) := by ring
  rw [e, abs_le]
  constructor
  · nlinarith [mul_nonneg ht0 h3, mul_nonneg (mul_nonneg ht0 ht0) h3, mul_nonneg ht0 (sub_nonneg.2 h2)]
  · nlinarith [mul_nonneg ht0 h3, mul_nonneg (mul_nonneg ht0 ht0) h3, mul_nonneg ht0 (sub_nonneg.2 h2),
      mul_nonneg (sub_nonneg.2 ht1) ht0]

theorem rp_sq_mul (a u p : ℝ) (ha : 0 < a) (hu : 0 < u) :
    (a ^ 2 * u) ^ p = a ^ (2 * p) * u ^ p := by
  rw [Real.mul_rpow (sq_nonneg a) hu.le, ← Real.rpow_natCast, ← Real.rpow_mul ha.le] <;> norm_num

theorem rp_ident_a2 (a : ℝ) (ha : 0 < a) : (a ^ (-(5 : ℝ) / 2)) ^ 2 * a ^ 4 = a⁻¹ := by
  rw [← Real.rpow_natCast (a ^ (-(5 : ℝ) / 2)) 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a 4,
    ← Real.rpow_add ha, ← Real.rpow_neg_one]
  norm_num

theorem rp_ident_a4 (a : ℝ) (ha : 0 < a) : (a ^ (2 * (-(5 : ℝ) / 8))) ^ 4 * a ^ 4 = a⁻¹ := by
  rw [← Real.rpow_natCast (a ^ (2 * (-(5 : ℝ) / 8))) 4, ← Real.rpow_mul ha.le,
    ← Real.rpow_natCast a 4, ← Real.rpow_add ha, ← Real.rpow_neg_one]
  norm_num

theorem rp_ident_u2 (u : ℝ) (hu : 0 < u) : (u ^ (-(5 : ℝ) / 4)) ^ 2 = u ^ (-(5 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le] <;> norm_num

theorem rp_ident_u4 (u : ℝ) (hu : 0 < u) : (u ^ (-(5 : ℝ) / 8)) ^ 4 = u ^ (-(5 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le] <;> norm_num

theorem alg_I1 (a t A1 A2 U1 U2 γ δ q : ℝ) (h1 : A1 * A2 = γ) (h2 : γ ^ 2 * a ^ 4 = a⁻¹)
    (hu1 : U1 * U2 = δ) (hu2 : δ ^ 2 = q) :
    (A1 * U1) ^ 2 * ((3 / 16 : ℝ) * (a ^ 2 * (4 * t - 1)) * (A2 * U2)) ^ 2 =
      (9 / 256 : ℝ) * (4 * t - 1) ^ 2 * q / a := by
  have key : (A1 * U1) ^ 2 * ((3 / 16 : ℝ) * (a ^ 2 * (4 * t - 1)) * (A2 * U2)) ^ 2 =
      (9 / 256 : ℝ) * (4 * t - 1) ^ 2 * ((A1 * A2) ^ 2 * a ^ 4) * (U1 * U2) ^ 2 := by ring
  rw [key, h1, h2, hu1, hu2]
  ring

theorem alg_I2 (a x t A U q : ℝ) (hx : x ^ 2 = a ^ 2) (h3 : A ^ 4 * a ^ 4 = a⁻¹)
    (hu : U ^ 4 = q) :
    ((3 / 4 : ℝ) * x * (A * U)) ^ 4 = (81 / 256 : ℝ) * q / a := by
  have key : ((3 / 4 : ℝ) * x * (A * U)) ^ 4 = (81 / 256 : ℝ) * (A ^ 4 * a ^ 4) * U ^ 4 := by
    have e1 : ((3 / 4 : ℝ) * x * (A * U)) ^ 4 = (81 / 256 : ℝ) * (x ^ 2) ^ 2 * A ^ 4 * U ^ 4 := by
      ring
    rw [e1, hx]
    ring
  rw [key, h3, hu]
  ring

theorem I1_ident (x ε t : ℝ) (hx : 0 < |x|) (hεt : ε ^ 2 = t * x ^ 2) (hu : 0 < 1 + t) :
    ((x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) ^ 2 *
        ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) ^ 2 =
      (9 / 256 : ℝ) * (4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) / |x| := by
  have hS : x ^ 2 + ε ^ 2 = |x| ^ 2 * (1 + t) := by
    rw [sq_abs, hεt]; ring
  have h4 : 4 * ε ^ 2 - x ^ 2 = |x| ^ 2 * (4 * t - 1) := by
    rw [sq_abs, hεt]; ring
  have h1 : |x| ^ (2 * ((3 : ℝ) / 8)) * |x| ^ (2 * (-(13 : ℝ) / 8)) = |x| ^ (-(5 : ℝ) / 2) := by
    rw [← Real.rpow_add hx]; norm_num
  have hu1 : (1 + t) ^ ((3 : ℝ) / 8) * (1 + t) ^ (-(13 : ℝ) / 8) = (1 + t) ^ (-(5 : ℝ) / 4) := by
    rw [← Real.rpow_add hu]; norm_num
  rw [h4, hS, rp_sq_mul |x| (1 + t) ((3 : ℝ) / 8) hx hu,
    rp_sq_mul |x| (1 + t) (-(13 : ℝ) / 8) hx hu]
  exact alg_I1 |x| t _ _ _ _ _ _ _ h1 (rp_ident_a2 |x| hx) hu1 (rp_ident_u2 (1 + t) hu)

theorem I2_ident (x ε t : ℝ) (hx : 0 < |x|) (hεt : ε ^ 2 = t * x ^ 2) (hu : 0 < 1 + t) :
    ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) ^ 4 =
      (81 / 256 : ℝ) * (1 + t) ^ (-(5 : ℝ) / 2) / |x| := by
  have hS : x ^ 2 + ε ^ 2 = |x| ^ 2 * (1 + t) := by
    rw [sq_abs, hεt]; ring
  rw [hS, rp_sq_mul |x| (1 + t) (-(5 : ℝ) / 8) hx hu]
  exact alg_I2 |x| x t _ _ _ (sq_abs x).symm (rp_ident_a4 |x| hx) (rp_ident_u4 (1 + t) hu)

theorem tparam (x ε : ℝ) (hε : 0 < ε) (hεx : ε < |x|) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ε ^ 2 = t * x ^ 2 ∧ t = ε ^ 2 / |x| ^ 2 := by
  have hx0 : 0 < |x| := lt_trans hε hεx
  have hx2 : x ^ 2 ≠ 0 := by
    rw [← sq_abs x]; exact (pow_pos hx0 2).ne'
  refine ⟨ε ^ 2 / |x| ^ 2, by positivity, ?_, ?_, rfl⟩
  · rw [div_le_one (pow_pos hx0 2)]
    nlinarith [mul_pos (sub_pos.2 hεx) (add_pos hx0 hε)]
  · rw [sq_abs, div_mul_eq_mul_div, eq_div_iff hx2]

theorem bound1 (x ε : ℝ) (hε : 0 < ε) (hεx : ε < |x|) :
    |((x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) ^ 2 *
        ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) ^ 2
        - (9 / 256 : ℝ) / (|x|)| ≤ (99 / 256 : ℝ) * (ε ^ 2 / |x| ^ 3) := by
  have hx0 : 0 < |x| := lt_trans hε hεx
  obtain ⟨t, ht0, ht1, hεt, hteq⟩ := tparam x ε hε hεx
  have hu : 0 < 1 + t := by linarith
  rw [I1_ident x ε t hx0 hεt hu]
  have e : (9 / 256 : ℝ) * (4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) / |x| - (9 / 256 : ℝ) / |x|
      = (9 / 256 : ℝ) / |x| * ((4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) - 1) := by ring
  rw [e, abs_mul, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 9 / 256) hx0)]
  have hA := q_weighted_sub_one t ht0 ht1
  have hfin : (9 / 256 : ℝ) / |x| * (11 * t) = (99 / 256 : ℝ) * (ε ^ 2 / |x| ^ 3) := by
    rw [hteq]; ring
  exact le_trans (mul_le_mul_of_nonneg_left hA (div_pos (by norm_num : (0 : ℝ) < 9 / 256) hx0).le)
    (le_of_eq hfin)

theorem bound2 (x ε : ℝ) (hε : 0 < ε) (hεx : ε < |x|) :
    |((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) ^ 4 - (81 / 256 : ℝ) / (|x|)|
      ≤ (243 / 256 : ℝ) * (ε ^ 2 / |x| ^ 3) := by
  have hx0 : 0 < |x| := lt_trans hε hεx
  obtain ⟨t, ht0, ht1, hεt, hteq⟩ := tparam x ε hε hεx
  have hu : 0 < 1 + t := by linarith
  rw [I2_ident x ε t hx0 hεt hu]
  have e : (81 / 256 : ℝ) * (1 + t) ^ (-(5 : ℝ) / 2) / |x| - (81 / 256 : ℝ) / |x|
      = (81 / 256 : ℝ) / |x| * ((1 + t) ^ (-(5 : ℝ) / 2) - 1) := by ring
  rw [e, abs_mul, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 81 / 256) hx0)]
  have hB := q_abs_sub_one t ht0 ht1
  have hfin : (81 / 256 : ℝ) / |x| * (3 * t) = (243 / 256 : ℝ) * (ε ^ 2 / |x| ^ 3) := by
    rw [hteq]; ring
  exact le_trans (mul_le_mul_of_nonneg_left hB (div_pos (by norm_num : (0 : ℝ) < 81 / 256) hx0).le)
    (le_of_eq hfin)

theorem bound3 (x ε : ℝ) (hε : 0 < ε) (hεx : ε < |x|) :
    |14 * ((x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) ^ 2 *
        ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) ^ 2
        - 7 * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) ^ 4
        + (441 / 256 : ℝ) / (|x|)|
      ≤ (3087 / 256 : ℝ) * (ε ^ 2 / |x| ^ 3) := by
  have hx0 : 0 < |x| := lt_trans hε hεx
  obtain ⟨t, ht0, ht1, hεt, hteq⟩ := tparam x ε hε hεx
  have hu : 0 < 1 + t := by linarith
  have e : 14 * ((x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) ^ 2 *
        ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) ^ 2
        - 7 * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) ^ 4
        + (441 / 256 : ℝ) / |x|
      = 14 * (((x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) ^ 2 *
        ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) ^ 2)
        - 7 * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) ^ 4
        + (441 / 256 : ℝ) / |x| := by ring
  rw [e, I1_ident x ε t hx0 hεt hu, I2_ident x ε t hx0 hεt hu]
  have e2 : 14 * ((9 / 256 : ℝ) * (4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) / |x|)
      - 7 * ((81 / 256 : ℝ) * (1 + t) ^ (-(5 : ℝ) / 2) / |x|) + (441 / 256 : ℝ) / |x|
      = (1 / |x|) * ((126 / 256 : ℝ) * ((4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) - 1)
          - (567 / 256 : ℝ) * ((1 + t) ^ (-(5 : ℝ) / 2) - 1)) := by ring
  rw [e2, abs_mul, abs_of_pos (one_div_pos.2 hx0)]
  have hA := abs_le.1 (q_weighted_sub_one t ht0 ht1)
  have hB := abs_le.1 (q_abs_sub_one t ht0 ht1)
  have hX : |(126 / 256 : ℝ) * ((4 * t - 1) ^ 2 * (1 + t) ^ (-(5 : ℝ) / 2) - 1)
      - (567 / 256 : ℝ) * ((1 + t) ^ (-(5 : ℝ) / 2) - 1)| ≤ (3087 / 256 : ℝ) * t := by
    rw [abs_le]
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hfin : 1 / |x| * ((3087 / 256 : ℝ) * t) = (3087 / 256 : ℝ) * (ε ^ 2 / |x| ^ 3) := by
    rw [hteq]; ring
  exact le_trans (mul_le_mul_of_nonneg_left hX (one_div_pos.2 hx0).le) (le_of_eq hfin)


theorem f034 (η : ℝ → ℝ) (hη : IsCuspCutoff η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < (1 : ℝ) / 8 →
      (∀ x : ℝ, Summable (fun k : ℤ => η (x - (k : ℝ)) *
        ((x - (k : ℝ)) ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8))) ∧
      ContDiff ℝ ∞ (cutoffCusp η ε) ∧ Function.Periodic (cutoffCusp η ε) 1 ∧
      (∀ x : ℝ, |x| < (1 : ℝ) / 8 →
        cutoffCusp η ε x = (x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) ∧
        deriv (cutoffCusp η ε) x =
          (3 / 4 : ℝ) * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8) ∧
        iteratedDeriv 2 (cutoffCusp η ε) x =
          (3 / 16 : ℝ) * (4 * ε ^ 2 - x ^ 2) *
            (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) ∧
      ∀ x : ℝ, ε < |x| → |x| < (1 : ℝ) / 8 →
        |(cutoffCusp η ε x) ^ 2 * (iteratedDeriv 2 (cutoffCusp η ε) x) ^ 2 -
          (9 / 256 : ℝ) / (|x|)| ≤ C * ε ^ 2 / |x| ^ 3 ∧
        |(deriv (cutoffCusp η ε) x) ^ 4 - (81 / 256 : ℝ) / (|x|)| ≤
          C * ε ^ 2 / |x| ^ 3 ∧
        |cutoffCuspDensity η ε x + (441 / 256 : ℝ) / (|x|)| ≤
          C * ε ^ 2 / |x| ^ 3 := by
  obtain ⟨hC, hsupp, hone⟩ := hη
  refine ⟨100, by norm_num, fun ε hε _ => ?_⟩
  refine ⟨fun x => cutoffCusp_summable η hsupp ε x, cutoffCusp_contDiff η hC hsupp ε hε,
    cutoffCusp_periodic η ε, fun x hx => cusp_deriv_closed_values η hsupp hone ε hε x hx, ?_⟩
  intro x hεx hx8
  have hp : 0 ≤ ε ^ 2 / |x| ^ 3 := by positivity
  have h100 : (100 : ℝ) * ε ^ 2 / |x| ^ 3 = 100 * (ε ^ 2 / |x| ^ 3) := by ring
  have hb1 := bound1 x ε hε hεx
  have hb2 := bound2 x ε hε hεx
  have hb3 := bound3 x ε hε hεx
  obtain ⟨e0, e1, e2⟩ := cusp_deriv_closed_values η hsupp hone ε hε x hx8
  unfold cutoffCuspDensity
  rw [e0, e1, e2]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end

end NlsGge.ThirdConsultation.F
