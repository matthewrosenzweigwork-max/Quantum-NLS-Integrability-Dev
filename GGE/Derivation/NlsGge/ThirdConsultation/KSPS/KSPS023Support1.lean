import Mathlib
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.Atomic.LIB.LIB019

/- KSPS-023 SUPPORT1 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS023Support1.lean.
   Purpose: the landed KSPS-022 head `inverse_phase_coefficients` is existential (∃ c, ...), while the KSPS-023 head
   uses the concrete `KSPSRiccati.spectralCoefficient` (through `spectralPolynomial`). The landed proof that
   `spectralCoefficient` itself is consistent (`ksps022_consistent`) is PRIVATE in NlsGge/Atomic/KSPS/KSPS022.lean.
   This module re-proves it natively by copying the private proofs of NlsGge/Atomic/KSPS/KSPS022.lean lines 20-273
   (author proof development) BYTE-IDENTICALLY except: identifier prefix `ksps022_` -> `ksps023_`, namespace, and the final
   lemma made public as `spectralCoefficient_consistent`. No definition of a public name; the private helper
   predicate `ksps023_Div` is a support-local abbreviation. (If root prefers, making `ksps022_consistent` public in
   KSPS022 would remove this duplication.) -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.KSPS023T
noncomputable section
open NlsGge.ThirdConsultation.KSPS

/-- Helper: an analytic germ at 0 divisible by `z ^ m`. -/
private def ksps023_Div (m : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ z : ℂ in 𝓝 0, f z = z ^ m * g z

private lemma ksps023_Div_mono {m n : ℕ} {f : ℂ → ℂ} (h : m ≤ n)
    (hf : ksps023_Div n f) : ksps023_Div m f := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun z => z ^ (n - m) * g z, by fun_prop, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

private lemma ksps023_Div_congr {m : ℕ} {f f' : ℂ → ℂ} (h : ksps023_Div m f)
    (hff : ∀ᶠ z : ℂ in 𝓝 0, f z = f' z) : ksps023_Div m f' := by
  obtain ⟨g, hg, hfg⟩ := h
  exact ⟨g, hg, by filter_upwards [hfg, hff] with z h1 h2; rw [← h2, h1]⟩

private lemma ksps023_Div_add {m : ℕ} {f g : ℂ → ℂ} (hf : ksps023_Div m f)
    (hg : ksps023_Div m g) : ksps023_Div m (fun z => f z + g z) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun z => a z + b z, ha.add hb, ?_⟩
  filter_upwards [hfa, hgb] with z h1 h2
  rw [h1, h2]; ring

private lemma ksps023_Div_const_mul {m : ℕ} {f : ℂ → ℂ} (c : ℂ) (hf : ksps023_Div m f) :
    ksps023_Div m (fun z => c * f z) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun z => c * a z, analyticAt_const.mul ha, ?_⟩
  filter_upwards [hfa] with z h1
  rw [h1]; ring

private lemma ksps023_Div_mul_analytic {m : ℕ} {f h : ℂ → ℂ} (hf : ksps023_Div m f)
    (hh : AnalyticAt ℂ h 0) : ksps023_Div m (fun z => f z * h z) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun z => a z * h z, ha.mul hh, ?_⟩
  filter_upwards [hfa] with z h1
  rw [h1]; ring

private lemma ksps023_Div_zero (m : ℕ) : ksps023_Div m (fun _ => 0) :=
  ⟨fun _ => 0, analyticAt_const, Eventually.of_forall (fun z => by simp)⟩

private lemma ksps023_Div_sum {ι : Type*} (s : Finset ι) {m : ℕ} {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, ksps023_Div m (f i)) : ksps023_Div m (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ksps023_Div_zero m
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ksps023_Div_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private lemma ksps023_Div_pow {b : ℂ → ℂ} (hb : ksps023_Div 1 b) (k : ℕ) :
    ksps023_Div k (fun z => b z ^ k) := by
  obtain ⟨g, hg, hbg⟩ := hb
  refine ⟨fun z => g z ^ k, by fun_prop, ?_⟩
  filter_upwards [hbg] with z h1
  rw [h1, mul_pow, pow_one]

private lemma ksps023_Div_one_of_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    ksps023_Div 1 f := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).2 (by
      intro i hi
      have : i = 0 := by omega
      subst this
      simpa using h0)
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt hf).1 h1
  exact ⟨g, hg, by filter_upwards [hfg] with z hz; simpa using hz⟩

private lemma ksps023_phasePoly_zero {N : ℕ} (φ : SobolevC N) (K : ℕ) :
    KSPSRiccati.phasePolynomial φ K 0 = 0 := by
  unfold KSPSRiccati.phasePolynomial
  rw [Finset.sum_eq_zero, mul_zero]
  intro k hk
  have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp [hk1]

private lemma ksps023_phasePoly_analytic {N : ℕ} (φ : SobolevC N) (K : ℕ) (x : ℂ) :
    AnalyticAt ℂ (KSPSRiccati.phasePolynomial φ K) x := by
  unfold KSPSRiccati.phasePolynomial
  fun_prop

private lemma ksps023_phasePoly_split {N : ℕ} (φ : SobolevC N) {J K : ℕ} (hJK : J ≤ K)
    (x y : ℂ) :
    KSPSRiccati.phasePolynomial φ K x - KSPSRiccati.phasePolynomial φ J y =
      Complex.I * ∑ k ∈ Finset.Icc 1 J,
        (((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k) * (x ^ k - y ^ k) +
      Complex.I * ∑ k ∈ Finset.Ioc J K,
        (((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k) * x ^ k := by
  have e : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
    ext t; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold KSPSRiccati.phasePolynomial
  rw [e K, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le J) hJK, e J]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

private lemma ksps023_step {N : ℕ} (φ : SobolevC N) {J K : ℕ} (hJK : J ≤ K) {a b : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hb1 : ksps023_Div 1 b)
    (hab : ksps023_Div (J + 1) (fun z => b z - a z)) :
    ksps023_Div (J + 1) (fun z => KSPSRiccati.phasePolynomial φ K (b z) -
      KSPSRiccati.phasePolynomial φ J (a z)) := by
  refine ksps023_Div_congr
    (f := fun z => Complex.I * ∑ k ∈ Finset.Icc 1 J,
        (((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k) * (b z ^ k - a z ^ k) +
      Complex.I * ∑ k ∈ Finset.Ioc J K,
        (((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k) * b z ^ k) ?_
    (Eventually.of_forall fun z => (ksps023_phasePoly_split φ hJK (b z) (a z)).symm)
  refine ksps023_Div_add
    (ksps023_Div_const_mul _ (ksps023_Div_sum _
      (f := fun k z => (((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k) * (b z ^ k - a z ^ k))
      ?_))
    (ksps023_Div_const_mul _ (ksps023_Div_sum _
      (f := fun k z => (((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k) * b z ^ k) ?_))
  · intro k _
    have hS : AnalyticAt ℂ (fun z => ∑ i ∈ Finset.range k, b z ^ i * a z ^ (k - 1 - i)) 0 := by
      fun_prop
    refine ksps023_Div_const_mul _ (ksps023_Div_congr (ksps023_Div_mul_analytic hab hS)
      (Eventually.of_forall fun z => ?_))
    exact (mul_comm _ _).trans (geom_sum₂_mul (b z) (a z) k)
  · intro k hk
    have hk' : J + 1 ≤ k := (Finset.mem_Ioc.mp hk).1
    exact ksps023_Div_const_mul _ (ksps023_Div_mono hk' (ksps023_Div_pow hb1 k))

private lemma ksps023_iterate_analytic {N : ℕ} (φ : SobolevC N) (j : ℕ) :
    AnalyticAt ℂ (KSPSRiccati.inversePhaseIterate φ j) 0 := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  induction j with
  | zero => exact analyticAt_const
  | succ j ih =>
    have hq : AnalyticAt ℂ (fun z : ℂ =>
        z / ((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z)) 0 :=
      analyticAt_id.div (analyticAt_const.add (analyticAt_id.mul ih)) (by simpa using hπ)
    exact ((ksps023_phasePoly_analytic φ (j + 1) _).comp hq).neg

private lemma ksps023_iterate_div {N : ℕ} (φ : SobolevC N) (K : ℕ) (ζ : ℂ → ℂ)
    (hζ : AnalyticAt ℂ ζ 0) (hζ0 : ζ 0 = 0)
    (heq : ∀ᶠ z : ℂ in 𝓝 0,
      ζ z + KSPSRiccati.phasePolynomial φ K (z / ((Real.pi : ℂ) + z * ζ z)) = 0) :
    ∀ j : ℕ, j ≤ K →
      ksps023_Div (j + 1) (fun z => KSPSRiccati.inversePhaseIterate φ j z - ζ z) := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  intro j
  induction j with
  | zero =>
    intro _
    refine ksps023_Div_one_of_zero (analyticAt_const.sub hζ) ?_
    simp [KSPSRiccati.inversePhaseIterate, hζ0]
  | succ j ih =>
    intro hj
    obtain ⟨g, hg, hpg⟩ := ih (by omega)
    have hpa := ksps023_iterate_analytic φ j
    have hD1a : AnalyticAt ℂ (fun z : ℂ =>
        (Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z) 0 :=
      analyticAt_const.add (analyticAt_id.mul hpa)
    have hD2a : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) + z * ζ z) 0 :=
      analyticAt_const.add (analyticAt_id.mul hζ)
    have hD10 : (fun z : ℂ => (Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z) 0 ≠ 0 := by
      simpa using hπ
    have hD20 : (fun z : ℂ => (Real.pi : ℂ) + z * ζ z) 0 ≠ 0 := by simpa using hπ
    have hD1 := hD1a.continuousAt.eventually_ne hD10
    have hD2 := hD2a.continuousAt.eventually_ne hD20
    have ha : AnalyticAt ℂ (fun z : ℂ =>
        z / ((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z)) 0 :=
      analyticAt_id.div hD1a hD10
    have hb : AnalyticAt ℂ (fun z : ℂ => z / ((Real.pi : ℂ) + z * ζ z)) 0 :=
      analyticAt_id.div hD2a hD20
    have hb1 : ksps023_Div 1 (fun z : ℂ => z / ((Real.pi : ℂ) + z * ζ z)) :=
      ⟨fun z => ((Real.pi : ℂ) + z * ζ z)⁻¹, hD2a.inv hD20,
        Eventually.of_forall fun z => by simp [div_eq_mul_inv]⟩
    have hab : ksps023_Div (j + 1 + 1) (fun z : ℂ =>
        z / ((Real.pi : ℂ) + z * ζ z) -
          z / ((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z)) := by
      refine ksps023_Div_mono (by omega : j + 1 + 1 ≤ j + 1 + 1 + 1) ?_
      refine ⟨fun z => g z / (((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z) *
          ((Real.pi : ℂ) + z * ζ z)),
        hg.div (hD1a.mul hD2a) (mul_ne_zero hD10 hD20), ?_⟩
      filter_upwards [hpg, hD1, hD2] with z hz h1 h2
      have e1 : z / ((Real.pi : ℂ) + z * ζ z) -
          z / ((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z) =
          z * z * (KSPSRiccati.inversePhaseIterate φ j z - ζ z) /
            (((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z) *
              ((Real.pi : ℂ) + z * ζ z)) := by
        field_simp
        ring
      rw [e1, hz]
      field_simp
      ring
    have hstep := ksps023_step φ (J := j + 1) (K := K) hj ha hb hb1 hab
    refine ksps023_Div_congr hstep ?_
    filter_upwards [heq] with z hz
    have e2 : KSPSRiccati.inversePhaseIterate φ (j + 1) z = -KSPSRiccati.phasePolynomial φ (j + 1)
        (z / ((Real.pi : ℂ) + z * KSPSRiccati.inversePhaseIterate φ j z)) := rfl
    rw [e2]
    linear_combination hz

private lemma ksps023_exists_germ {N : ℕ} (φ : SobolevC N) (K : ℕ) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ 0 ∧ ζ 0 = 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, (Real.pi : ℂ) + z * ζ z ≠ 0 ∧
        ζ z + KSPSRiccati.phasePolynomial φ K (z / ((Real.pi : ℂ) + z * ζ z)) = 0) := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let G : ℂ × ℂ → ℂ := fun q =>
    q.2 + KSPSRiccati.phasePolynomial φ K (q.1 / ((Real.pi : ℂ) + q.1 * q.2))
  have hGa : AnalyticAt ℂ G ((0 : ℂ), (0 : ℂ)) := by
    have h1 : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 / ((Real.pi : ℂ) + q.1 * q.2)) (0, 0) :=
      analyticAt_fst.div (analyticAt_const.add (analyticAt_fst.mul analyticAt_snd))
        (by simpa using hπ)
    exact analyticAt_snd.add ((ksps023_phasePoly_analytic φ K _).comp h1)
  have hG0 : G (0, 0) = 0 := by simp [G, ksps023_phasePoly_zero]
  have hder : ∃ e : ℂ ≃L[ℂ] ℂ,
      fderiv ℂ (fun x => G ((0 : ℂ), x)) (0 : ℂ) = (e : ℂ →L[ℂ] ℂ) := by
    refine ⟨ContinuousLinearEquiv.refl ℂ ℂ, ?_⟩
    have : (fun x : ℂ => G ((0 : ℂ), x)) = fun x => x := by
      funext x; simp [G, ksps023_phasePoly_zero]
    rw [this]; simp
  obtain ⟨ζ, hζa, hζ0, hζeq, -⟩ :=
    NlsGge.Atomic.LIB.LIB019_04A G (0 : ℂ) (0 : ℂ) hGa hG0 hder
  refine ⟨ζ, hζa, hζ0, ?_⟩
  have hca : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) + z * ζ z) 0 :=
    analyticAt_const.add (analyticAt_id.mul hζa)
  have hne : ∀ᶠ z : ℂ in 𝓝 0, (Real.pi : ℂ) + z * ζ z ≠ 0 :=
    hca.continuousAt.eventually_ne (by simpa [hζ0] using hπ)
  filter_upwards [hne, hζeq] with z h1 h2
  exact ⟨h1, h2⟩

private lemma ksps023_taylor {N : ℕ} (φ : SobolevC N) (K : ℕ) (ζ : ℂ → ℂ)
    (hζ : AnalyticAt ℂ ζ 0) (hζ0 : ζ 0 = 0)
    (heq : ∀ᶠ z : ℂ in 𝓝 0,
      ζ z + KSPSRiccati.phasePolynomial φ K (z / ((Real.pi : ℂ) + z * ζ z)) = 0)
    (k : ℕ) (hk : k ≤ K) :
    KSPSRiccati.spectralCoefficient φ k = iteratedDeriv k ζ 0 / (Nat.factorial k : ℂ) := by
  unfold KSPSRiccati.spectralCoefficient
  congr 1
  obtain ⟨g, hg, hfg⟩ := ksps023_iterate_div φ K ζ hζ hζ0 heq k hk
  have hpa := ksps023_iterate_analytic φ k
  have han : AnalyticAt ℂ (fun z => KSPSRiccati.inversePhaseIterate φ k z - ζ z) 0 :=
    hpa.sub hζ
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun z => KSPSRiccati.inversePhaseIterate φ k z - ζ z) 0 :=
    (natCast_le_analyticOrderAt han).2 ⟨g, hg, by
      filter_upwards [hfg] with z hz
      simpa using hz⟩
  have h0 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).1 hle k
    (Nat.lt_succ_self k)
  rw [iteratedDeriv_fun_sub hpa.contDiffAt hζ.contDiffAt] at h0
  exact sub_eq_zero.1 h0

theorem spectralCoefficient_consistent {N : ℕ} (φ : SobolevC N) :
    ConsistentRiccatiSpectralCoefficients φ (KSPSRiccati.spectralCoefficient φ) := by
  intro K _
  obtain ⟨ζ, hζa, hζ0, hev⟩ := ksps023_exists_germ φ K
  have heq : ∀ᶠ z : ℂ in 𝓝 0,
      ζ z + KSPSRiccati.phasePolynomial φ K (z / ((Real.pi : ℂ) + z * ζ z)) = 0 :=
    hev.mono fun z hz => hz.2
  exact ⟨ζ, hζa, hζ0, hev, fun k hk => ksps023_taylor φ K ζ hζa hζ0 heq k hk⟩

end
end NlsGge.ThirdConsultation.KSPS023T
