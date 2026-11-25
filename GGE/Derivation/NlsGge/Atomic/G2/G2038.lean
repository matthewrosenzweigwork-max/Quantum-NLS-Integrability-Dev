import Mathlib
import NlsGge.Analysis.PhysicalH1Bounds
import NlsGge.Atomic.G1.G1062
import NlsGge.Atomic.G1.G1086
import NlsGge.Atomic.KSPS.KSPS005
import NlsGge.Atomic.KST.KST065
import NlsGge.Definitions.PilotInterfaces
import NlsGge.GK38.Defs
import NlsGge.GK38.PairPotential
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS005Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Support
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.Sobolev.Round5

/- G2-038 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G2/G2038.lean, namespace NlsGge.GKDefinitionDesign.
   Head G2_038 VERBATIM from design STATEMENTS/G2.md "## G2-038" (identical in gpt6pro_followup7/9/10; no Pro round 4-12 entry touches G2-038).
   Hosted here (design body verbatim, DEFINITIONS/G2.lean.md): principalArcosh.  Route: Volterra route (see G2038_ROUTE.md), NOT the WKB route of the packet:
   KSPS-005 two-term remainder at lam = i tau, trace of the fundamental matrix (KSPS020Support.discrim_eq_trace), explicit elementary complex-log estimate.
   Smoothness and finite-gap hypotheses are retained; finiteGap is used (via G1-086) to get H^1 for u and conj u. -/
set_option autoImplicit false
open Filter Topology

namespace NlsGge.GKDefinitionDesign
noncomputable section

def principalArcosh (z : ℂ) : ℂ :=
  Complex.log (z + Complex.sqrt (z-1) * Complex.sqrt (z+1))

namespace G2038S

theorem exp_neg_two_le (τ : ℝ) (hτ : 0 < τ) : Real.exp (-τ) ^ 2 ≤ 1 / (2 * τ ^ 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * τ) (by positivity)
  have hpos : 0 < Real.exp (2 * τ) := Real.exp_pos _
  have e : Real.exp (-τ) ^ 2 = 1 / Real.exp (2 * τ) := by
    rw [sq, ← Real.exp_add, one_div, ← Real.exp_neg]; congr 1; ring
  rw [e, div_le_div_iff₀ hpos (by positivity)]
  nlinarith [sq_nonneg τ]

theorem sqrt_prod_props (w : ℂ) (h1 : 0 < (w - 1).re) :
    (Complex.sqrt (w - 1) * Complex.sqrt (w + 1)) ^ 2 = w ^ 2 - 1 ∧
      0 ≤ (Complex.sqrt (w - 1) * Complex.sqrt (w + 1)).re := by
  have h2 : 0 < (w + 1).re := by simp at h1 ⊢; linarith
  have hw1 : w - 1 ≠ 0 := fun h => by simp [h] at h1
  have hw2 : w + 1 ≠ 0 := fun h => by simp [h] at h2
  rw [sqrt_eq_exp hw1, sqrt_eq_exp hw2, ← Complex.exp_add]
  constructor
  · rw [← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * (Complex.log (w - 1) / 2 + Complex.log (w + 1) / 2) =
        Complex.log (w - 1) + Complex.log (w + 1) := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_log hw1, Complex.exp_log hw2]
    ring
  · rw [Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ?_)
    have a1 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h1)
    have a2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h2)
    rw [abs_lt] at a1 a2
    simp only [Complex.add_im, Complex.log_im, Complex.div_ofNat_im]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

theorem arcosh_ray (c : ℂ) (E : ℝ) (hE : 0 ≤ E) :
    ∃ T C : ℝ, 2 ≤ T ∧ 0 < C ∧ ∀ (τ : ℝ) (w : ℂ), T ≤ τ →
      ‖2 * (Real.exp (-τ) : ℂ) * w - 1 - c / (τ : ℂ)‖ ≤ E / τ ^ 2 →
      w - 1 ∈ Complex.slitPlane ∧
      ‖principalArcosh w - (τ : ℂ) - c / (τ : ℂ)‖ ≤ C / τ ^ 2 := by
  set K : ℝ := ‖c‖ + E + 2 with hK
  have hKpos : 2 ≤ K := by have := norm_nonneg c; linarith
  refine ⟨2 + 2 * K, (E + 2) + K ^ 2, by linarith, by positivity, ?_⟩
  intro τ w hT hε
  have hτ2 : 2 ≤ τ := by linarith
  have hτpos : 0 < τ := by linarith
  have hτK : 2 * K ≤ τ := by linarith
  set x : ℂ := 2 * (Real.exp (-τ) : ℂ) * w with hx
  set ε : ℂ := x - 1 - c / (τ : ℂ) with hεdef
  have hexp : 5 ≤ Real.exp τ := by
    have := Real.quadratic_le_exp_of_nonneg (x := τ) hτpos.le
    nlinarith
  have hepos : 0 < Real.exp τ := Real.exp_pos τ
  have hmul : Real.exp (-τ) * Real.exp τ = 1 := by rw [← Real.exp_add]; simp
  have hwx : w = ((Real.exp τ / 2 : ℝ) : ℂ) * x := by
    rw [hx]
    have : ((Real.exp τ / 2 : ℝ) : ℂ) * (2 * (Real.exp (-τ) : ℂ) * w) =
        ((Real.exp τ * Real.exp (-τ) : ℝ) : ℂ) * w := by push_cast; ring
    rw [this, mul_comm (Real.exp τ), hmul]; simp
  -- size of c/τ
  have hcτ : ‖c / (τ : ℂ)‖ = ‖c‖ / τ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hτpos.le]
  have hE2 : E / τ ^ 2 ≤ E / τ := by
    apply div_le_div_of_nonneg_left hE hτpos
    nlinarith
  have hη : ‖x - 1‖ ≤ K / τ := by
    have : x - 1 = ε + c / (τ : ℂ) := by rw [hεdef]; ring
    rw [this]
    calc ‖ε + c / (τ : ℂ)‖ ≤ ‖ε‖ + ‖c / (τ : ℂ)‖ := norm_add_le _ _
      _ ≤ E / τ ^ 2 + ‖c‖ / τ := by rw [hcτ]; linarith [hε]
      _ ≤ K / τ := by
        have : (E + ‖c‖) / τ ≤ K / τ := div_le_div_of_nonneg_right (by linarith) hτpos.le
        rw [add_div] at this; linarith
  have hKτ : K / τ ≤ 1 / 2 := by
    rw [div_le_iff₀ hτpos]; linarith
  have hxre : 1 / 2 ≤ x.re := by
    have := Complex.abs_re_le_norm (x - 1)
    have h2 := abs_le.1 this
    simp at h2
    linarith [h2.1, hη, hKτ]
  have hwre : Real.exp τ / 4 ≤ w.re := by
    rw [hwx, Complex.re_ofReal_mul]
    nlinarith
  have hw1 : 0 < (w - 1).re := by simp; nlinarith
  refine ⟨Complex.mem_slitPlane_iff.2 (Or.inl hw1), ?_⟩
  obtain ⟨hS2, hSre⟩ := sqrt_prod_props w hw1
  set S : ℂ := Complex.sqrt (w - 1) * Complex.sqrt (w + 1) with hS
  have hprod : (S - w) * (S + w) = -1 := by
    have : (S - w) * (S + w) = S ^ 2 - w ^ 2 := by ring
    rw [this, hS2]; ring
  have hSw : ‖S + w‖ ≥ w.re := by
    have := Complex.re_le_norm (S + w)
    simp only [Complex.add_re] at this
    linarith
  have hwpos : 0 < w.re := by linarith
  have hD : ‖S - w‖ ≤ 4 / Real.exp τ := by
    have h1 : ‖S - w‖ * ‖S + w‖ = 1 := by
      rw [← norm_mul, hprod]; simp
    have h2 : ‖S - w‖ * w.re ≤ 1 := by
      calc ‖S - w‖ * w.re ≤ ‖S - w‖ * ‖S + w‖ := mul_le_mul_of_nonneg_left hSw (norm_nonneg _)
        _ = 1 := h1
    rw [le_div_iff₀ hepos]
    nlinarith [norm_nonneg (S - w)]
  have hDe : ‖(S - w) * (Real.exp (-τ) : ℂ)‖ ≤ 2 / τ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have e1 : ‖S - w‖ * Real.exp (-τ) ≤ 4 / Real.exp τ * Real.exp (-τ) :=
      mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
    have e2 : 4 / Real.exp τ * Real.exp (-τ) = 4 * Real.exp (-τ) ^ 2 := by
      rw [Real.exp_neg]; field_simp
    have e3 := exp_neg_two_le τ hτpos
    calc ‖S - w‖ * Real.exp (-τ) ≤ 4 * Real.exp (-τ) ^ 2 := by linarith
      _ ≤ 4 * (1 / (2 * τ ^ 2)) := by linarith
      _ = 2 / τ ^ 2 := by field_simp; ring
  set ν : ℂ := x - 1 + (S - w) * (Real.exp (-τ) : ℂ) with hν
  have hνc : ‖ν - c / (τ : ℂ)‖ ≤ (E + 2) / τ ^ 2 := by
    have : ν - c / (τ : ℂ) = ε + (S - w) * (Real.exp (-τ) : ℂ) := by rw [hν, hεdef]; ring
    rw [this]
    calc _ ≤ ‖ε‖ + ‖(S - w) * (Real.exp (-τ) : ℂ)‖ := norm_add_le _ _
      _ ≤ E / τ ^ 2 + 2 / τ ^ 2 := by linarith
      _ = (E + 2) / τ ^ 2 := by ring
  have hνn : ‖ν‖ ≤ K / τ := by
    calc ‖ν‖ = ‖(ν - c / (τ : ℂ)) + c / (τ : ℂ)‖ := by ring_nf
      _ ≤ ‖ν - c / (τ : ℂ)‖ + ‖c / (τ : ℂ)‖ := norm_add_le _ _
      _ ≤ (E + 2) / τ ^ 2 + ‖c‖ / τ := by rw [hcτ]; linarith
      _ ≤ K / τ := by
        have h3 : (E + 2) / τ ^ 2 ≤ (E + 2) / τ :=
          div_le_div_of_nonneg_left (by linarith) hτpos (by nlinarith)
        have : (E + 2 + ‖c‖) / τ ≤ K / τ := div_le_div_of_nonneg_right (by linarith) hτpos.le
        rw [add_div] at this; linarith
  have hν1 : ‖ν‖ < 1 := by linarith
  have hAeq : w + S = ((Real.exp τ : ℝ) : ℂ) * (1 + ν) := by
    have e : (Real.exp τ : ℂ) * (Real.exp (-τ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_comm, hmul]; simp
    have e2 : ((Real.exp τ : ℝ) : ℂ) * (1 + ν) =
        (Real.exp τ : ℂ) * x + (Real.exp τ : ℂ) * (S - w) * (Real.exp (-τ) : ℂ) := by
      rw [hν]; ring
    rw [e2]
    have e3 : (Real.exp τ : ℂ) * x = 2 * w := by
      rw [hx]
      calc (Real.exp τ : ℂ) * (2 * (Real.exp (-τ) : ℂ) * w) =
          2 * ((Real.exp τ : ℂ) * (Real.exp (-τ) : ℂ)) * w := by ring
        _ = 2 * w := by rw [e]; ring
    have e4 : (Real.exp τ : ℂ) * (S - w) * (Real.exp (-τ) : ℂ) = S - w := by
      calc (Real.exp τ : ℂ) * (S - w) * (Real.exp (-τ) : ℂ) =
          ((Real.exp τ : ℂ) * (Real.exp (-τ) : ℂ)) * (S - w) := by ring
        _ = S - w := by rw [e]; ring
    rw [e3, e4]; ring
  have h1ν : (1 + ν) ≠ 0 := by
    intro h
    have : ν = -1 := by linear_combination h
    rw [this] at hν1; simp at hν1
  have hlog : principalArcosh w = (τ : ℂ) + Complex.log (1 + ν) := by
    unfold principalArcosh
    rw [← hS, hAeq, Complex.log_ofReal_mul hepos h1ν, Real.log_exp]
  have hb := Complex.norm_log_one_add_sub_self_le hν1
  have hν12 : ‖ν‖ ≤ 1 / 2 := by linarith
  have hb2 : ‖Complex.log (1 + ν) - ν‖ ≤ ‖ν‖ ^ 2 := by
    refine hb.trans ?_
    have : (1 - ‖ν‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h0 : 0 ≤ ‖ν‖ ^ 2 := by positivity
    nlinarith
  rw [hlog]
  have hfin : ‖Complex.log (1 + ν) - c / (τ : ℂ)‖ ≤ (E + 2) / τ ^ 2 + K ^ 2 / τ ^ 2 := by
    calc ‖Complex.log (1 + ν) - c / (τ : ℂ)‖
        = ‖(Complex.log (1 + ν) - ν) + (ν - c / (τ : ℂ))‖ := by ring_nf
      _ ≤ ‖Complex.log (1 + ν) - ν‖ + ‖ν - c / (τ : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖ν‖ ^ 2 + (E + 2) / τ ^ 2 := by linarith
      _ ≤ (K / τ) ^ 2 + (E + 2) / τ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg ν) hνn 2
        linarith
      _ = (E + 2) / τ ^ 2 + K ^ 2 / τ ^ 2 := by rw [div_pow]; ring
  calc ‖(τ : ℂ) + Complex.log (1 + ν) - (τ : ℂ) - c / (τ : ℂ)‖
      = ‖Complex.log (1 + ν) - c / (τ : ℂ)‖ := by ring_nf
    _ ≤ (E + 2) / τ ^ 2 + K ^ 2 / τ ^ 2 := hfin
    _ = ((E + 2) + K ^ 2) / τ ^ 2 := by ring

end G2038S
end
end NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section
open scoped Matrix.Norms.L2Operator
open MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPSVolterra (E R phi term integrateMatrix integratedQuadratic)

namespace G2038S

open NlsGge.ThirdConsultation.KSPS NlsGge.GK38 NlsGge.Pilot
open NlsGge.ThirdConsultation.KSPSVolterra (E R phi term integrateMatrix integratedQuadratic)

theorem term_one_diag (p : PotPair) (lam : ℂ) (i : Fin 2) :
    NlsGge.ThirdConsultation.KSPSVolterra.term 1 1 lam p i i = 0 := by
  have h : ∀ t : ℝ, (E lam (1 - t) * R * phi p t * E lam t) i i = 0 := by
    intro t; fin_cases i <;> simp [E, R, phi, Matrix.mul_apply, Fin.sum_univ_two]
  simp [NlsGge.ThirdConsultation.KSPSVolterra.term,
    NlsGge.ThirdConsultation.KSPSVolterra.integrateMatrix, h]

theorem trace_volterra_one (φ : SobolevC 1) (z : ℂ) :
    Matrix.trace (volterraTerm 1 1 z φ) = 0 := by
  rw [Matrix.trace_fin_two]
  unfold volterraTerm
  rw [term_one_diag, term_one_diag]; simp

theorem trace_X (φ : SobolevC 1) (τ : ℝ) (hτ : τ ≠ 0) :
    Matrix.trace ((2 * (Complex.I * (τ : ℂ)))⁻¹ •
        (freePropagator 1 (Complex.I * (τ : ℂ)) * R * integratedQuadratic φ 1)) =
      (∫ t in (0 : ℝ)..1, NlsGge.GK38.potRepFst38 (toPotPair φ) t *
          NlsGge.GK38.potRepSnd38 (toPotPair φ) t) *
        ((Real.exp τ - Real.exp (-τ) : ℝ) : ℂ) / (2 * (τ : ℂ)) := by
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have e1 : Complex.exp (-(Complex.I * (Complex.I * (τ : ℂ)) * ((1 : ℝ) : ℂ))) =
      Complex.exp (τ : ℂ) := by
    congr 1; push_cast; linear_combination (-(τ : ℂ)) * Complex.I_mul_I
  have e2 : Complex.exp (Complex.I * (Complex.I * (τ : ℂ)) * ((1 : ℝ) : ℂ)) =
      Complex.exp (-(τ : ℂ)) := by
    congr 1; push_cast; linear_combination (τ : ℂ) * Complex.I_mul_I
  rw [Matrix.trace_fin_two]
  simp only [integratedQuadratic, freePropagator, R, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [e1, e2]
  have hq : (∫ t in (0 : ℝ)..1, NlsGge.GK38.potRepFst38 (toPotPair φ) t *
          NlsGge.GK38.potRepSnd38 (toPotPair φ) t) =
      ∫ t in (0 : ℝ)..1, potRepFst38 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) t *
          potRepSnd38 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) t := rfl
  rw [hq]
  push_cast

  field_simp
  ring


theorem disc_expansion (φ : SobolevC 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 < τ → ∃ ρ : ℂ,
      ‖ρ‖ ≤ B * Real.exp τ / τ ^ 2 ∧
      discrim (toPotPair φ) (Complex.I * (τ : ℂ)) =
        ((Real.exp τ + Real.exp (-τ) : ℝ) : ℂ) +
          (∫ t in (0 : ℝ)..1, potRepFst38 (toPotPair φ) t * potRepSnd38 (toPotPair φ) t) *
            ((Real.exp τ - Real.exp (-τ) : ℝ) : ℂ) / (2 * (τ : ℂ)) + ρ := by
  obtain ⟨C, hC, h⟩ := fundamental_two_term_remainder_uniform
  refine ⟨2 * C * Real.exp (l2Norm φ) * |sobolevNorm 1 φ ^ 2 * (1 + sobolevNorm 1 φ)|,
    by positivity, fun τ hτ => ?_⟩
  have hne : Complex.I * (τ : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hτ.ne')
  have hrem := h φ 1 ⟨zero_le_one, le_rfl⟩ (Complex.I * (τ : ℂ)) hne
  have him : |(Complex.I * (τ : ℂ)).im| = τ := by simp [abs_of_pos hτ]
  have hnorm : ‖Complex.I * (τ : ℂ)‖ = τ := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le, one_mul]
  rw [him, hnorm] at hrem
  refine ⟨Matrix.trace (fundamentalRemainder φ 1 (Complex.I * (τ : ℂ))), ?_, ?_⟩
  · set s := sobolevNorm 1 φ with hs
    set L := l2Norm φ with hL
    have h1 : ‖Matrix.trace (fundamentalRemainder φ 1 (Complex.I * (τ : ℂ)))‖ ≤
        2 * (C * Real.exp (τ * 1 + L) * s ^ 2 * (1 + s) / τ ^ 2) :=
      (NlsGge.ThirdConsultation.KSPS020Support.norm_trace_le_two _).trans (by linarith)
    refine h1.trans ?_
    have e : 2 * (C * Real.exp (τ * 1 + L) * s ^ 2 * (1 + s) / τ ^ 2) =
        (2 * C * Real.exp L * (s ^ 2 * (1 + s))) * Real.exp τ / τ ^ 2 := by
      rw [mul_one, Real.exp_add]; ring
    rw [e]
    have h2 : 2 * C * Real.exp L * (s ^ 2 * (1 + s)) ≤ 2 * C * Real.exp L * |s ^ 2 * (1 + s)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) (sq_nonneg _)
  · rw [NlsGge.ThirdConsultation.KSPS020Support.discrim_eq_trace]
    have hdec : NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 (Complex.I * (τ : ℂ)) =
        freePropagator 1 (Complex.I * (τ : ℂ)) + volterraTerm 1 1 (Complex.I * (τ : ℂ)) φ +
          (2 * (Complex.I * (τ : ℂ)))⁻¹ •
            (freePropagator 1 (Complex.I * (τ : ℂ)) * R * integratedQuadratic φ 1) +
          fundamentalRemainder φ 1 (Complex.I * (τ : ℂ)) := by
      unfold fundamentalRemainder; abel
    have hcos : 2 * Complex.cos (Complex.I * (τ : ℂ)) =
        ((Real.exp τ + Real.exp (-τ) : ℝ) : ℂ) := by
      rw [show Complex.I * (τ : ℂ) = (τ : ℂ) * Complex.I from mul_comm _ _, Complex.cos_mul_I,
        Complex.two_cosh]; push_cast; ring
    rw [hdec, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      NlsGge.ThirdConsultation.KSPS020Support.trace_freePropagator_one,
      trace_volterra_one, trace_X φ τ hτ.ne', hcos]
    ring

theorem physicalSobolev_star' (u : PhysicalL2) (h : physicalSobolev 1 u) :
    physicalSobolev 1 (star u : PhysicalL2) := by
  unfold physicalSobolev SobolevSquareSummable at h ⊢
  have h' := (Equiv.neg ℤ).summable_iff.mpr h
  refine h'.congr (fun j => ?_)
  have hr : ‖reflectedFourierL2 (star u : PhysicalL2) j‖ = ‖reflectedFourierL2 u (-j)‖ := by
    rw [reflectedFourierL2_apply, reflectedFourierL2_apply]
    unfold reflectedFourier
    rw [NlsGge.Schur.physicalFourier_star38, norm_neg, norm_neg, norm_star, neg_neg]
  simp only [Function.comp, Equiv.neg_apply, hr, neg_neg]
  have : Real.rpow (japaneseBracket (-j)) (2 * 1) = Real.rpow (japaneseBracket j) (2 * 1) := by
    rw [NlsGge.Analysis.japaneseBracket_h1_weight, NlsGge.Analysis.japaneseBracket_h1_weight]; simp
  rw [this]

theorem H_eq (u : PhysicalL2) :
    hierarchyHamiltonian 1 (realSlice u) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  have hin : inner ℂ u u = ∫ x : PhysicalCircle, inner ℂ (u x) (u x) ∂spatialMeasure :=
    MeasureTheory.L2.inner_def u u
  rw [inner_self_eq_norm_sq_to_K] at hin
  simp only [hierarchyHamiltonian, if_true]
  push_cast
  rw [show ((‖u‖ : ℝ) : ℂ) ^ 2 = RCLike.ofReal (K := ℂ) ‖u‖ ^ 2 from rfl, hin]
  refine integral_congr_ae ?_
  filter_upwards [realSlice_snd_ae u] with x hx
  rw [realSlice_fst, hx]
  simp [RCLike.inner_apply, mul_comm]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem Q_eq (u : PhysicalL2) :
    (∫ t in (0 : ℝ)..1, potRepFst38 (realSlice u) t * potRepSnd38 (realSlice u) t) =
      ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∫ t in (0 : ℝ)..1, potRepFst38 (realSlice u) t * potRepSnd38 (realSlice u) t =
      ∫ t in (0 : ℝ)..1, ((‖coverRep38 u t‖ ^ 2 : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [potRepSnd38_realSlice_ae u] with t ht _
    rw [ht]
    have : potRepFst38 (realSlice u) t = coverRep38 u t := rfl
    rw [this]
    simp [Complex.mul_conj', mul_comm]
  rw [h, intervalIntegral.integral_ofReal, integral_sq_coverRep38_one]

end G2038S

theorem G2_038 (u : PhysicalL2)
    (hu : NlsGge.ThirdConsultation.KO.SmoothPhysical u)
    (hfg : NlsGge.ThirdConsultation.finiteGap u) :
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧ ∀ τ : ℝ, T ≤ τ →
      discrim (realSlice u) (Complex.I*(τ : ℂ))/2 - 1 ∈ Complex.slitPlane ∧
      ‖principalArcosh (discrim (realSlice u) (Complex.I*(τ : ℂ))/2) -
        (τ : ℂ) - hierarchyHamiltonian 1 (realSlice u)/(2*(τ : ℂ))‖ ≤ C/τ^2 := by
  have h1 : physicalSobolev ((1 : ℕ) : ℝ) u := by
    have := (G1_086).1 u hfg 1
    exact this
  have h1' : physicalSobolev ((1 : ℕ) : ℝ) (star u : PhysicalL2) := by
    have : physicalSobolev 1 u := by simpa using h1
    simpa using G2038S.physicalSobolev_star' u this
  obtain ⟨v1, hv1⟩ := NlsGge.ThirdConsultation.KST.KST065S.exists_recover 1 u
    ((G1086S.physicalSobolev_iff _ u).1 h1)
  obtain ⟨v2, hv2⟩ := NlsGge.ThirdConsultation.KST.KST065S.exists_recover 1 (star u : PhysicalL2)
    ((G1086S.physicalSobolev_iff _ _).1 h1')
  let φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1 := (v1, v2)
  have hφ : NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice u := by
    rw [realSlice_apply]
    exact Prod.ext hv1 hv2
  obtain ⟨B, hB, hexp⟩ := G2038S.disc_expansion φ
  rw [hφ] at hexp
  rw [G2038S.Q_eq] at hexp
  set Q : ℝ := ‖u‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨T, C, hT2, hC, hray⟩ := G2038S.arcosh_ray ((Q : ℂ) / 2) (1 / 2 + Q / 8 + B) (by positivity)
  refine ⟨T, C, by linarith, hC, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := by linarith
  have hτ2 : 2 ≤ τ := by linarith
  obtain ⟨ρ, hρ, hD⟩ := hexp τ hτpos
  rw [G2038S.H_eq]
  simp only [Complex.ofReal_add, Complex.ofReal_sub] at hD
  set a : ℂ := ((Real.exp (-τ) : ℝ) : ℂ) with ha
  set b : ℂ := ((Real.exp τ : ℝ) : ℂ) with hb
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτpos.ne'
  have hab : a * b = 1 := by
    rw [ha, hb, ← Complex.ofReal_mul, mul_comm, ← Real.exp_add]; simp
  set m : ℂ := (Q : ℂ) / (2 * (τ : ℂ)) with hm
  have e1 : (Q : ℂ) * (b - a) / (2 * (τ : ℂ)) = m * (b - a) := by rw [hm]; ring
  have e2 : (Q : ℂ) / 2 / (τ : ℂ) = m := by rw [hm]; field_simp
  have hX : 2 * a * (discrim (realSlice u) (Complex.I * (τ : ℂ)) / 2) - 1 - (Q : ℂ) / 2 / (τ : ℂ)
      = a ^ 2 * (1 - m) + a * ρ := by
    rw [hD, e1, e2]
    linear_combination (1 + m) * hab
  have hna : ‖a‖ = Real.exp (-τ) := by
    rw [ha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hmn : ‖m‖ ≤ Q / 4 := by
    have : ‖m‖ = Q / (2 * τ) := by
      rw [hm, norm_div, Complex.norm_real, Real.norm_of_nonneg hQ0]
      congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτpos.le]; simp
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hexp2 := G2038S.exp_neg_two_le τ hτpos
  have hbound : ‖2 * a * (discrim (realSlice u) (Complex.I * (τ : ℂ)) / 2) - 1 -
      (Q : ℂ) / 2 / (τ : ℂ)‖ ≤ (1 / 2 + Q / 8 + B) / τ ^ 2 := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    have f1 : ‖a ^ 2 * (1 - m)‖ ≤ (1 / 2 + Q / 8) / τ ^ 2 := by
      rw [norm_mul, norm_pow, hna]
      have h1m : ‖1 - m‖ ≤ 1 + Q / 4 := by
        calc ‖1 - m‖ ≤ ‖(1 : ℂ)‖ + ‖m‖ := norm_sub_le _ _
          _ ≤ 1 + Q / 4 := by simp; linarith
      calc Real.exp (-τ) ^ 2 * ‖1 - m‖ ≤ (1 / (2 * τ ^ 2)) * (1 + Q / 4) :=
            mul_le_mul hexp2 h1m (norm_nonneg _) (by positivity)
        _ = (1 / 2 + Q / 8) / τ ^ 2 := by field_simp; ring
    have f2 : ‖a * ρ‖ ≤ B / τ ^ 2 := by
      rw [norm_mul, hna]
      calc Real.exp (-τ) * ‖ρ‖ ≤ Real.exp (-τ) * (B * Real.exp τ / τ ^ 2) :=
            mul_le_mul_of_nonneg_left hρ (Real.exp_pos _).le
        _ = B / τ ^ 2 := by
            have : Real.exp (-τ) * Real.exp τ = 1 := by rw [← Real.exp_add]; simp
            calc Real.exp (-τ) * (B * Real.exp τ / τ ^ 2)
                = (Real.exp (-τ) * Real.exp τ) * B / τ ^ 2 := by ring
              _ = B / τ ^ 2 := by rw [this]; ring
    calc _ ≤ (1 / 2 + Q / 8) / τ ^ 2 + B / τ ^ 2 := add_le_add f1 f2
      _ = (1 / 2 + Q / 8 + B) / τ ^ 2 := by ring
  obtain ⟨hs, hn⟩ := hray τ _ hτ hbound
  refine ⟨hs, ?_⟩
  rw [← e2]
  exact hn

end
end NlsGge.GKDefinitionDesign
