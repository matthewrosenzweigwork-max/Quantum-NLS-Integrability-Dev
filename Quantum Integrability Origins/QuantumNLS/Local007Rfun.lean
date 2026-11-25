import Mathlib
import QuantumNLS.Local007EvalT
import QuantumNLS.Local007MassB
import QuantumNLS.Local007AlgA

/-! LOCAL-007 stage R: the factor `R(v) = Re Phi(F(v), a(v), |b(v)|²)`.

* `Phi_free`: `Phi(F0, 0, 0) = 1` (free value, `Phi_eval` at the free double zero);
* `analyticAt_Rfun`: `R` is real analytic at `0` when `F`, `a`, `b` are and `F(0) = F0`, `a(0)=0`, `b(0)=0`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Metric Filter Topology Set
namespace QuantumNLS.Local007Rfun
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007AlgB (Phi A F0 analyticAt_Phi cOm)
open QuantumNLS.Local007EvalT (Phi_eval Dtrue OmC sqF)
open QuantumNLS.Local007Factor (H0 f0_eq norm_H0_add sinc sinc_mul sinc_zero differentiable_H0)

theorem sinc_real (y : ℝ) : (sinc (y : ℂ)).im = 0 := by
  by_cases hy : y = 0
  · subst hy; simp [sinc_zero]
  have h := sinc_mul (y : ℂ)
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy
  have e : sinc (y : ℂ) = ((Real.sin y / y : ℝ) : ℂ) := by
    have h2 : sinc (y : ℂ) = Complex.sin (y : ℂ) / (y : ℂ) := by rw [eq_div_iff hy']; exact h
    rw [h2, Complex.ofReal_div, Complex.ofReal_sin]
  rw [e]; exact Complex.ofReal_im _

theorem H0_real (L : ℝ) (x : ℝ) : (H0 L (x : ℂ)).im = 0 := by
  unfold H0
  have h := sinc_real (L * x / 2)
  have e : (L : ℂ) * (x : ℂ) / 2 = ((L * x / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  set s := sinc (((L * x / 2 : ℝ)) : ℂ)
  have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simpa using h)
  rw [hs]
  have : -(L : ℂ) ^ 2 * (s.re : ℂ) ^ 2 = ((-L ^ 2 * s.re ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]; exact Complex.ofReal_im _

theorem Phi_free {L c : ℝ} [Fact (0 < L)] (hc : c = 1 / (8 * L)) : Phi c L (F0 c L) 0 0 = 1 := by
  have hL : 0 < L := Fact.out
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hΔ : Differentiable ℂ (fun z : ℂ => 2 * Complex.cos ((L : ℂ) * z / 2)) := by fun_prop
  have hev := Phi_eval (L := L) (c := c) hL hc (Δ := fun z : ℂ => 2 * Complex.cos ((L : ℂ) * z / 2))
    (H := H0 L) hΔ (differentiable_H0 L) (α := 0) (t := 0) le_rfl (by rw [abs_zero, add_zero]; positivity)
    (fun z => by simpa using f0_eq L z)
    (fun z hz => by
      have h1 := norm_H0_add hL (z := z) (by
        refine hz.trans ?_
        rw [show 3 * (1 / (16 * L)) = 3 / (16 * L) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith)
      have : L ^ 2 / 100 ≤ L ^ 2 / 4 := by gcongr <;> norm_num
      exact h1.trans this)
    (F0 c L) (fun θ => rfl)
  simp only [Complex.ofReal_zero, add_zero, zero_mul] at hev
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at hev
  rw [hev]
  -- value of Dtrue at 0
  have hD0 : ∀ s : ℝ, Dtrue L (H0 L) (fun z => (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4) 0 = ((L / 2 : ℝ) : ℂ) := by
    intro s
    unfold Dtrue sqF
    have h1 : H0 L 0 = -(L : ℂ) ^ 2 := by simp [H0, sinc_zero]
    have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
    have h2 : (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * (-(L : ℂ) ^ 2)) = 1 := by
      push_cast; field_simp
    have h3 : OmC (((fun z : ℂ => (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4) 0) / 4) = 1 := by
      have : ((fun z : ℂ => (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4) 0) / 4 = 0 := by simp; norm_num
      rw [this]
      unfold OmC
      rw [tsum_eq_single 0]
      · simp [cOm]
      · intro j hj; simp [hj]
    rw [h1, h2, Complex.one_cpow, h3]; simp
  have hint : ∫ s in (-1 : ℝ)..1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) *
      Dtrue L (H0 L) (fun z => (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4) 0 =
      (((L / 2) * (Real.pi / 2) : ℝ) : ℂ) := by
    have e : ∀ s : ℝ, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) *
        Dtrue L (H0 L) (fun z => (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4) 0 =
        (((L / 2) * Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) := fun s => by rw [hD0 s]; push_cast; ring
    simp only [e]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  rw [hint]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  push_cast
  field_simp
  norm_num


def Rfun (c L : ℝ) [Fact (0 < L)] (Fh : L2T L → A) (a : L2T L → ℝ) (b : L2T L → ℂ) (v : L2T L) : ℝ :=
  (Phi c L (Fh v) (a v) (‖b v‖ ^ 2)).re

theorem Rfun_zero {L c : ℝ} [Fact (0 < L)] (hc : c = 1 / (8 * L)) {Fh : L2T L → A} {a : L2T L → ℝ}
    {b : L2T L → ℂ} (hF0 : Fh 0 = F0 c L) (ha0 : a 0 = 0) (hb0 : b 0 = 0) : Rfun c L Fh a b 0 = 1 := by
  unfold Rfun
  rw [hF0, ha0, hb0, norm_zero]
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
  have := Phi_free (L := L) (c := c) hc
  rw [this]; simp

theorem analyticAt_Rfun {L c : ℝ} [Fact (0 < L)] (hc : c = 1 / (8 * L)) {Fh : L2T L → A} {a : L2T L → ℝ}
    {b : L2T L → ℂ} (hFh : AnalyticAt ℝ Fh 0) (hF0 : Fh 0 = F0 c L) (ha : AnalyticAt ℝ a 0)
    (hb : AnalyticAt ℝ b 0) (ha0 : a 0 = 0) (hb0 : b 0 = 0) : AnalyticAt ℝ (Rfun c L Fh a b) 0 := by
  have hL : 0 < L := Fact.out
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcL : c * L ≤ 1 / 8 := by rw [hc]; field_simp; norm_num
  have hre : AnalyticAt ℝ (fun v : L2T L => (b v).re) 0 := (Complex.reCLM.analyticAt _).comp hb
  have him : AnalyticAt ℝ (fun v : L2T L => (b v).im) 0 := (Complex.imCLM.analyticAt _).comp hb
  have hn2 : AnalyticAt ℝ (fun v : L2T L => ‖b v‖ ^ 2) 0 := by
    have : (fun v : L2T L => ‖b v‖ ^ 2) = fun v => (b v).re * (b v).re + (b v).im * (b v).im := by
      funext v; rw [Complex.sq_norm, Complex.normSq_apply]
    rw [this]; exact (hre.fun_mul hre).fun_add (him.fun_mul him)
  have hpair : AnalyticAt ℝ (fun v : L2T L => (Fh v, a v, ‖b v‖ ^ 2)) 0 :=
    hFh.prod (ha.prod hn2)
  have hPhi := analyticAt_Phi hc0 hL hcL
  have h0 : (fun v : L2T L => (Fh v, a v, ‖b v‖ ^ 2)) 0 = (F0 c L, 0, 0) := by
    show (Fh 0, a 0, ‖b 0‖ ^ 2) = (F0 c L, 0, 0)
    rw [hF0, ha0, hb0, norm_zero]
    norm_num
  have key := AnalyticAt.comp_of_eq hPhi hpair h0
  have key2 := (Complex.reCLM.analyticAt _).comp key
  exact key2

end QuantumNLS.Local007Rfun
#print axioms QuantumNLS.Local007Rfun.Phi_free
#print axioms QuantumNLS.Local007Rfun.analyticAt_Rfun
#print axioms QuantumNLS.Local007Rfun.Rfun_zero
