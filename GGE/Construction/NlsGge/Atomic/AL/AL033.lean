import Mathlib
import NlsGge.Analysis.AnalyticTsum38
import NlsGge.ThirdConsultation.AL.Basic
import NlsGge.Atomic.AL.AL031
import NlsGge.Atomic.AL.AL032

set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core NlsGge.Pilot

namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al033_majorant_summable (B x : ℝ) (hx : 0 ≤ x) :
    Summable (fun j : ℕ => B * (x ^ j / (Nat.factorial j : ℝ) ^ 4)) := by
  have hfac : ∀ j : ℕ, (1 : ℝ) ≤ (Nat.factorial j : ℝ) := fun j => by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hcmp : Summable (fun j : ℕ => x ^ j / (Nat.factorial j : ℝ)) :=
    Real.summable_pow_div_factorial x
  have hsum2 : Summable (fun j : ℕ => x ^ j / (Nat.factorial j : ℝ) ^ 4) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hcmp
    have h1 := hfac j
    have h3 : (1 : ℝ) ≤ (Nat.factorial j : ℝ) ^ 3 := one_le_pow₀ h1
    have h4 : (Nat.factorial j : ℝ) ≤ (Nat.factorial j : ℝ) ^ 4 := by nlinarith
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) h4
  exact hsum2.mul_left B

theorem al033_key (h R : ℝ) (hh : 0 < h) (j : ℕ) :
    (h⁻¹) ^ (2 * j + 1) * (4 * R) ^ j = h⁻¹ * ((4 * R) / h ^ 2) ^ j := by
  rw [show (4 * R) / h ^ 2 = 4 * R * (h⁻¹) ^ 2 by ring, mul_pow (4 * R) ((h⁻¹) ^ 2) j, ← pow_mul]
  ring

theorem al033_analytic_of_majorant {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (f : ℕ → E → ℂ) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (m : ℕ → ℝ) (hm : Summable m) (hb : ∀ j, ∀ z ∈ U, ‖f j z‖ ≤ m j) :
    AnalyticOnNhd ℂ (fun y => ∑' j, f j y) U := by
  intro p hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU p hp
  have hsub : closedBall p (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  exact NlsGge.AnalyticTsum38.analyticAt_tsum_of_bound38 (f := f) (x := p) (r := r / 2) (by positivity)
    (fun j => (hf j).mono hsub) hm (fun j z hz => hb j z (hsub hz))

theorem al033 {L : ℕ} [NeZero L]
    {lo up : ℝ} (c : ℕ → ℝ) (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    (h : ℝ) (hh : 0 < h)
    (K : Set (ZMod L → ℂ)) (hK : IsCompact K) (hKD : K ⊆ alDisk38 L) :
  AnalyticOnNhd ℝ (alEnergy38 (L := L) c h) (alDisk38 L) ∧
  ∃ (U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))) (R C : ℝ),
    IsOpen U ∧ alIota38 '' K ⊆ U ∧ (∀ p ∈ U, p.swap ∈ U) ∧
    1 < R ∧ 0 ≤ C ∧
    (∀ j : ℕ, AnalyticOnNhd ℂ (fun p => complexMoment p j) U) ∧
    Summable (fun j : ℕ =>
      up*(2*C)*h⁻¹*((4*max 1 (R^2))/h^2)^j/(Nat.factorial j : ℝ)^4) ∧
    (∀ p ∈ U, ∀ j : ℕ,
      ‖(NlsGge.coefficient c j : ℂ)*((h⁻¹ : ℝ) : ℂ)^(2*j+1)*complexMoment p j‖ ≤
        up*(2*C)*h⁻¹*((4*max 1 (R^2))/h^2)^j/(Nat.factorial j : ℝ)^4) ∧
    (∀ p ∈ U, Summable (fun j : ℕ =>
      (NlsGge.coefficient c j : ℂ)*((h⁻¹ : ℝ) : ℂ)^(2*j+1)*complexMoment p j)) ∧
    TendstoUniformlyOn
      (fun (n : ℕ) p => ∑ j ∈ Finset.range n,
        (NlsGge.coefficient c j : ℂ)*((h⁻¹ : ℝ) : ℂ)^(2*j+1)*complexMoment p j)
      (complexEnergy c h) atTop U ∧
    AnalyticOnNhd ℂ (complexEnergy c h) U ∧
    ∀ a : ZMod L → ℂ, IsALField38 a → alIota38 a ∈ U →
      complexEnergy c h (alIota38 a) = (alEnergy38 c h a : ℂ)
  := by
  classical
  have hlo : 0 < lo := hc.1
  have hup : 0 ≤ up := le_trans hlo.le hc.2.1
  have hcoef0 : ∀ j : ℕ, 0 ≤ NlsGge.coefficient c j := fun j => by
    unfold NlsGge.coefficient
    exact div_nonneg (le_trans hlo.le (hc.2.2 j).1) (by positivity)
  have hcoefu : ∀ j : ℕ, NlsGge.coefficient c j ≤ up / (Nat.factorial j : ℝ) ^ 4 := fun j => by
    unfold NlsGge.coefficient
    exact div_le_div_of_nonneg_right (hc.2.2 j).2 (by positivity)
  have hreal : AnalyticOnNhd ℝ (alEnergy38 (L := L) c h) (alDisk38 L) :=
    analyticOnNhd_alEnergy38 (L := L) hc hh
  obtain ⟨U, R, C, hUo, hKU, -, hsw, hR, hC, hlog, hbd, -, -⟩ := al031 K hK hKD
  have hbound : ∀ p ∈ U, ∀ ζ ∈ Metric.closedBall (0 : ℂ) R⁻¹,
      ‖alComplexLog38 p.1 p.2 ζ‖ ≤ C := fun p hp ζ hζ => (hbd p hp ζ hζ).2.2.2
  obtain ⟨-, hAn, hMb, -, hId⟩ := al032 U hUo hsw R C hR hC hlog hbound
  have hx0 : 0 ≤ (4 * max 1 (R ^ 2)) / h ^ 2 := by positivity
  have hMs : Summable (fun j : ℕ => up * (2 * C) * h⁻¹ *
      ((4 * max 1 (R ^ 2)) / h ^ 2) ^ j / (Nat.factorial j : ℝ) ^ 4) :=
    (al033_majorant_summable (up * (2 * C) * h⁻¹) ((4 * max 1 (R ^ 2)) / h ^ 2) hx0).congr
      fun j => by ring
  have hterm : ∀ p ∈ U, ∀ j : ℕ,
      ‖(NlsGge.coefficient c j : ℂ) * ((h⁻¹ : ℝ) : ℂ) ^ (2 * j + 1) * complexMoment p j‖ ≤
        up * (2 * C) * h⁻¹ * ((4 * max 1 (R ^ 2)) / h ^ 2) ^ j / (Nat.factorial j : ℝ) ^ 4 := by
    intro p hp j
    have hhinv : 0 ≤ h⁻¹ := inv_nonneg.mpr hh.le
    have e1 : ‖((h⁻¹ : ℝ) : ℂ) ^ (2 * j + 1)‖ = h⁻¹ ^ (2 * j + 1) := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hhinv]
    have e2 : ‖(NlsGge.coefficient c j : ℂ)‖ = NlsGge.coefficient c j := by
      rw [Complex.norm_real, Real.norm_of_nonneg (hcoef0 j)]
    rw [norm_mul, norm_mul, e1, e2]
    have hm := hMb p hp j
    have hc' := hcoefu j
    have hk := al033_key h (max 1 (R ^ 2)) hh j
    have hpow : 0 ≤ h⁻¹ ^ (2 * j + 1) := pow_nonneg hhinv _
    have hcoefU : 0 ≤ up / (Nat.factorial j : ℝ) ^ 4 :=
      div_nonneg hup (by positivity)
    calc NlsGge.coefficient c j * h⁻¹ ^ (2 * j + 1) * ‖complexMoment p j‖
        ≤ (up / (Nat.factorial j : ℝ) ^ 4) * h⁻¹ ^ (2 * j + 1) * (2 * C * (4 * max 1 (R ^ 2)) ^ j) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc' hpow) hm (norm_nonneg _)
            (mul_nonneg hcoefU hpow)
      _ = (up / (Nat.factorial j : ℝ) ^ 4) * (2 * C) *
            (h⁻¹ ^ (2 * j + 1) * (4 * max 1 (R ^ 2)) ^ j) := by ring
      _ = (up / (Nat.factorial j : ℝ) ^ 4) * (2 * C) *
            (h⁻¹ * ((4 * max 1 (R ^ 2)) / h ^ 2) ^ j) := by rw [hk]
      _ = up * (2 * C) * h⁻¹ * ((4 * max 1 (R ^ 2)) / h ^ 2) ^ j / (Nat.factorial j : ℝ) ^ 4 := by
          ring
  have hiota : ∀ a : ZMod L → ℂ, IsALField38 a → alIota38 a ∈ U →
      complexEnergy c h (alIota38 a) = (alEnergy38 c h a : ℂ) := by
    intro a ha _
    unfold complexEnergy alEnergy38
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    rw [hId a ha j]
    simp only [alEnergyTerm38, alQ38, alMomentK38_eq_alK38]
    push_cast
    ring
  have huni : TendstoUniformlyOn
      (fun (n : ℕ) (p : (ZMod L → ℂ) × (ZMod L → ℂ)) => ∑ j ∈ Finset.range n,
        (NlsGge.coefficient c j : ℂ) * ((h⁻¹ : ℝ) : ℂ) ^ (2 * j + 1) * complexMoment p j)
      (complexEnergy c h) atTop U :=
    tendstoUniformlyOn_tsum_nat hMs (fun n p hp => hterm p hp n)
  have hanal : AnalyticOnNhd ℂ (complexEnergy c h) U :=
    al033_analytic_of_majorant U hUo
      (fun j p => (NlsGge.coefficient c j : ℂ) * ((h⁻¹ : ℝ) : ℂ) ^ (2 * j + 1) * complexMoment p j)
      (fun j => analyticOnNhd_const.mul (hAn j))
      (fun j => up * (2 * C) * h⁻¹ * ((4 * max 1 (R ^ 2)) / h ^ 2) ^ j / (Nat.factorial j : ℝ) ^ 4)
      hMs (fun j p hp => hterm p hp j)
  exact ⟨hreal, U, R, C, hUo, hKU, hsw, hR, hC, hAn, hMs,
    fun p hp j => hterm p hp j,
    fun p hp => Summable.of_norm_bounded hMs (fun j => hterm p hp j),
    huni, hanal, hiota⟩

end
end NlsGge.ThirdConsultation.AL
