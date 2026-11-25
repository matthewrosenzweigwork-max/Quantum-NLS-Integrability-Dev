import Mathlib
import NlsGge.Atomic.KSPS.KSPS006
import NlsGge.ThirdConsultation.KSPS.KSPS007Support8
import NlsGge.ThirdConsultation.KSPS.KSPS007Support9

                                                                                                                         
                                                                                        
                                                                                                                       
                                                                                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS007Support5 NlsGge.ThirdConsultation.KSPS007Support6
  NlsGge.ThirdConsultation.KSPS007Support7 NlsGge.ThirdConsultation.KSPS007Support9
open scoped Matrix Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS007Support10

theorem EB_of_norm (A : Mt) : EB A ‖A‖ :=
  fun i j => NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 A i j

theorem maj_le {φ : SobolevC 1} {B Λ x : ℝ} {lam : ℂ} (hs : sobolevNorm 1 φ ≤ B)
    (hΛ : |lam.im| ≤ Λ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    fundamentalRemainderMajorant φ x lam ≤
      Real.exp (Λ + B) * B ^ 2 * (1 + B) / ‖lam‖ ^ 2 := by
  unfold fundamentalRemainderMajorant
  have hs0 : 0 ≤ sobolevNorm 1 φ := Real.sqrt_nonneg _
  have hl2 : l2Norm φ ≤ B := (l2Norm_le φ).trans hs
  have hexp : |lam.im| * x + l2Norm φ ≤ Λ + B := by
    have : |lam.im| * x ≤ Λ := by
      calc |lam.im| * x ≤ |lam.im| * 1 := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
        _ ≤ Λ := by linarith
    linarith
  have h1 : Real.exp (|lam.im| * x + l2Norm φ) ≤ Real.exp (Λ + B) := Real.exp_le_exp.mpr hexp
  have h2 : sobolevNorm 1 φ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have h3 : 1 + sobolevNorm 1 φ ≤ 1 + B := by linarith
  gcongr

theorem fundamental_decomp (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    KSPSVolterra.fundamental φ x lam =
      KSPSVolterra.E lam x + KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) +
        (2 * lam)⁻¹ • (KSPSVolterra.E lam x * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) +
        fundamentalRemainder φ x lam := by
  have h : fundamentalRemainder φ x lam = KSPSVolterra.fundamental φ x lam -
      KSPSVolterra.E lam x - KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) -
      (2 * lam)⁻¹ • (KSPSVolterra.E lam x * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) := rfl
  rw [h]; abel

theorem inverse_decomp (φ : SobolevC 1) (t : ℝ) (lam : ℂ) :
    KSPSVolterra.inverseFundamental φ t lam =
      KSPSVolterra.E lam (-t) - KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) -
        (2 * lam)⁻¹ • (KSPSVolterra.E lam (-t) * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ t) +
        inverseFundamentalRemainder φ t lam := by
  have h : inverseFundamentalRemainder φ t lam = KSPSVolterra.inverseFundamental φ t lam -
      KSPSVolterra.E lam (-t) + KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) +
      (2 * lam)⁻¹ • (KSPSVolterra.E lam (-t) * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ t) := rfl
  rw [h]; abel

theorem R_entries : KSPSVolterra.R 0 0 = Complex.I ∧ KSPSVolterra.R 0 1 = 0 ∧
    KSPSVolterra.R 1 0 = 0 ∧ KSPSVolterra.R 1 1 = -Complex.I := by
  simp [KSPSVolterra.R]

theorem E_entries (lam : ℂ) (u : ℝ) :
    KSPSVolterra.E lam u 0 0 = Complex.exp (-(Complex.I * lam * (u : ℂ))) ∧
    KSPSVolterra.E lam u 0 1 = 0 ∧ KSPSVolterra.E lam u 1 0 = 0 ∧
    KSPSVolterra.E lam u 1 1 = Complex.exp (Complex.I * lam * (u : ℂ)) := by
  simp [KSPSVolterra.E]

theorem Q_entries (φ : SobolevC 1) (u : ℝ) :
    KSPSVolterra.integratedQuadratic φ u 0 0 = ∫ s in (0 : ℝ)..u,
      coverRep38 (physicalSobolevEmbed 1 φ.1) s * coverRep38 (physicalSobolevEmbed 1 φ.2) s ∧
    KSPSVolterra.integratedQuadratic φ u 0 1 = 0 ∧ KSPSVolterra.integratedQuadratic φ u 1 0 = 0 ∧
    KSPSVolterra.integratedQuadratic φ u 1 1 = ∫ s in (0 : ℝ)..u,
      coverRep38 (physicalSobolevEmbed 1 φ.1) s * coverRep38 (physicalSobolevEmbed 1 φ.2) s := by
  rw [NlsGge.ThirdConsultation.KSPS003Support2.integratedQuadratic_eq]
  simp [Matrix.smul_apply]

theorem Theta_eq (φ : SobolevC 1) {lam : ℂ} (hlam : lam ≠ 0) (x t : ℝ) :
    Theta φ lam x t =
      -(KSPSVolterra.E lam x * (inverseFundamentalRemainder φ t lam * KSPSVolterra.R)) -
        fundamentalRemainder φ x lam * (KSPSVolterra.E lam (-t) * KSPSVolterra.R) -
        (KSPSVolterra.fundamental φ x lam - KSPSVolterra.E lam x) *
          ((KSPSVolterra.inverseFundamental φ t lam - KSPSVolterra.E lam (-t)) * KSPSVolterra.R) := by
  have hExt : KSPSVolterra.E lam (x - t) = KSPSVolterra.E lam x * KSPSVolterra.E lam (-t) := by
    have := NlsGge.GK38.freeE_add lam x (-t)
    rw [← sub_eq_add_neg] at this
    exact this
  have hc : (2 * lam)⁻¹ * (2 * lam) = 1 := inv_mul_cancel₀ (by simp [hlam])
  obtain ⟨r0, r1, r2, r3⟩ := R_entries
  obtain ⟨e0, e1, e2, e3⟩ := E_entries lam x
  obtain ⟨f0, f1, f2, f3⟩ := E_entries lam (-t)
  obtain ⟨p0, p1, p2, p3⟩ := Q_entries φ x
  obtain ⟨q0, q1, q2, q3⟩ := Q_entries φ t
  unfold Theta
  rw [hExt]
  exact NlsGge.ThirdConsultation.KSPS007Support8.theta_alg
    (Complex.exp (-(Complex.I * lam * (x : ℂ)))) (Complex.exp (Complex.I * lam * (x : ℂ)))
    (Complex.exp (-(Complex.I * lam * ((-t : ℝ) : ℂ)))) (Complex.exp (Complex.I * lam * ((-t : ℝ) : ℂ)))
    (∫ s in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.1) s * coverRep38 (physicalSobolevEmbed 1 φ.2) s)
    (∫ s in (0 : ℝ)..t, coverRep38 (physicalSobolevEmbed 1 φ.1) s * coverRep38 (physicalSobolevEmbed 1 φ.2) s)
    (2 * lam)⁻¹ lam Complex.I Complex.I_mul_I hc
    KSPSVolterra.R (KSPSVolterra.E lam x) (KSPSVolterra.E lam (-t))
    (KSPSVolterra.integratedQuadratic φ x) (KSPSVolterra.integratedQuadratic φ t)
    (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ)) (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ))
    (fundamentalRemainder φ x lam) (inverseFundamentalRemainder φ t lam)
    (KSPSVolterra.fundamental φ x lam) (KSPSVolterra.inverseFundamental φ t lam)
    r0 r1 r2 r3 e0 e1 e2 e3 f0 f1 f2 f3 p0 p1 p2 p3 q0 q1 q2 q3
    (fundamental_decomp φ x lam) (inverse_decomp φ t lam)

theorem theta_pointwise (Λ B : ℝ) (hΛ0 : 0 ≤ Λ) (hB0 : 0 ≤ B) (C6 : ℝ) (hC6 : 0 ≤ C6)
    (h6 : ∀ φ : SobolevC 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ lam : ℂ, lam ≠ 0 →
      ‖fundamentalRemainder φ x lam‖ ≤ C6 * fundamentalRemainderMajorant φ x lam ∧
      ‖inverseFundamentalRemainder φ x lam‖ ≤ 4 * C6 * fundamentalRemainderMajorant φ x lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B → ∀ lam : ℂ, 1 ≤ ‖lam‖ →
      |lam.im| ≤ Λ → ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) x,
        EB (Theta φ lam x t) (K / ‖lam‖ ^ 2) := by
  set ε := Real.exp Λ with hε
  set κ := 2 * ‖iotaCLM‖ + ‖derivCLM‖ with hκ
  set A1 := Real.exp (3 * Λ) * (κ * B) with hA1
  set br0 := C6 * (Real.exp (Λ + B) * B ^ 2 * (1 + B)) with hbr0
  set bp0 := 4 * br0 with hbp0
  set Km := A1 + 2 * ε * B ^ 2 + br0 with hKm
  set Kn := A1 + 2 * ε * B ^ 2 + bp0 with hKn
  have hε0 : 0 < ε := Real.exp_pos _
  have hκ0 : 0 ≤ κ := by positivity
  have hA10 : 0 ≤ A1 := by positivity
  have hbr00 : 0 ≤ br0 := by positivity
  have hbp00 : 0 ≤ bp0 := by positivity
  have hKm0 : 0 ≤ Km := by positivity
  have hKn0 : 0 ≤ Kn := by positivity
  refine ⟨4 * ε * bp0 + 4 * br0 * ε + 4 * Km * Kn, by positivity, ?_⟩
  intro φ hs lam hL hΛ x hx t ht
  have hLpos : 0 < ‖lam‖ := by linarith
  have hlam : lam ≠ 0 := norm_pos_iff.mp hLpos
  set u := ‖lam‖⁻¹ with hu
  have hu0 : 0 < u := inv_pos.mpr hLpos
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hL
  have hdiv1 : ∀ X : ℝ, X / ‖lam‖ = X * u := fun X => by rw [hu, div_eq_mul_inv]
  have hdiv2 : ∀ X : ℝ, X / ‖lam‖ ^ 2 = X * u ^ 2 := fun X => by rw [hu, div_eq_mul_inv, inv_pow]
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hxt : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
  have hs0 : 0 ≤ sobolevNorm 1 φ := Real.sqrt_nonneg _
  have hcn : ‖(2 * lam)⁻¹‖ = u / 2 := by
    rw [norm_inv, norm_mul, hu]
    simp only [RCLike.norm_ofNat]
    field_simp
  have hEx : EB (KSPSVolterra.E lam x) ε :=
    EB_E lam hΛ (abs_le.2 ⟨by linarith [hx.1], hx.2⟩)
  have hEt : EB (KSPSVolterra.E lam (-t)) ε :=
    EB_E lam hΛ (abs_le.2 ⟨by linarith [hxt.2], by linarith [hxt.1]⟩)
  have hrx : EB (fundamentalRemainder φ x lam) (br0 * u ^ 2) := by
    refine (EB_of_norm _).mono ?_
    calc _ ≤ C6 * fundamentalRemainderMajorant φ x lam := (h6 φ x hx lam hlam).1
      _ ≤ C6 * (Real.exp (Λ + B) * B ^ 2 * (1 + B) / ‖lam‖ ^ 2) := by
          gcongr; exact maj_le hs hΛ hx
      _ = br0 * u ^ 2 := by rw [hdiv2]; ring
  have hrp : EB (inverseFundamentalRemainder φ t lam) (bp0 * u ^ 2) := by
    refine (EB_of_norm _).mono ?_
    calc _ ≤ 4 * C6 * fundamentalRemainderMajorant φ t lam := (h6 φ t hxt lam hlam).2
      _ ≤ 4 * C6 * (Real.exp (Λ + B) * B ^ 2 * (1 + B) / ‖lam‖ ^ 2) := by
          gcongr; exact maj_le hs hΛ hxt
      _ = bp0 * u ^ 2 := by rw [hdiv2, hbp0, hbr0]; ring
  have hM1x : EB (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ)) (A1 * u) :=
    EB.mono (M1_EB φ hlam hΛ hx) (by
      rw [hdiv1, hA1]
      have : sobolevNorm 1 φ ≤ B := hs
      gcongr)
  have hM1t : EB (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ)) (A1 * u) :=
    EB.mono (M1_EB φ hlam hΛ hxt) (by
      rw [hdiv1, hA1]
      have : sobolevNorm 1 φ ≤ B := hs
      gcongr)
  have hQ1 : EB (KSPSVolterra.integratedQuadratic φ x) (B ^ 2) :=
    EB.mono (Q_EB φ hx) (pow_le_pow_left₀ hs0 hs 2)
  have hQ2 : EB (KSPSVolterra.integratedQuadratic φ t) (B ^ 2) :=
    EB.mono (Q_EB φ hxt) (pow_le_pow_left₀ hs0 hs 2)
  have hm : EB (KSPSVolterra.fundamental φ x lam - KSPSVolterra.E lam x) (Km * u) := by
    have e : KSPSVolterra.fundamental φ x lam - KSPSVolterra.E lam x =
        KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) +
          (2 * lam)⁻¹ • (KSPSVolterra.E lam x * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) +
          fundamentalRemainder φ x lam := by
      rw [fundamental_decomp φ x lam]; abel
    rw [e]
    have h1 := (hM1x.add (((hEx.mul EB_R).mul hQ1).smul ((2 * lam)⁻¹))).add hrx
    refine h1.mono ?_
    rw [hcn, hKm]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hbr00]
  have hn : EB (KSPSVolterra.inverseFundamental φ t lam - KSPSVolterra.E lam (-t)) (Kn * u) := by
    have e : KSPSVolterra.inverseFundamental φ t lam - KSPSVolterra.E lam (-t) =
        -KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) -
          (2 * lam)⁻¹ • (KSPSVolterra.E lam (-t) * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ t) +
          inverseFundamentalRemainder φ t lam := by
      rw [inverse_decomp φ t lam]; abel
    rw [e]
    have h1 := (hM1t.neg.sub (((hEt.mul EB_R).mul hQ2).smul ((2 * lam)⁻¹))).add hrp
    refine h1.mono ?_
    rw [hcn, hKn]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hbp00]
  have hΘ := NlsGge.ThirdConsultation.KSPS007Support8.theta_EB hEx hEt EB_R hrx hrp hm hn
  rw [Theta_eq φ hlam x t, hdiv2]
  refine hΘ.mono (le_of_eq ?_)
  ring

end NlsGge.ThirdConsultation.KSPS007Support10
