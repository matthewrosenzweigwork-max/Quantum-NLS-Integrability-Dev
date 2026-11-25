import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support2
import NlsGge.Atomic.G1.G1004
import NlsGge.GK38.GradFundamentalODE
import NlsGge.GK38.GradFundamentalDet
import NlsGge.ThirdConsultation.KSPSSupport.ANA01

/- KSPS-014 SUPPORT3 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS014Support3.lean.
   Two prior leaves of KSPS-014 (Pro round 14, Cluster 1), independent of the KSPS-014 host:
   * sourceFundamental_eq_fundPair (Pro's support head, verbatim, namespace KSPS): the Picard series
     sourceFundamental (KSPS011Host) is the GK38 fundamental matrix fundPair on [0,1]
     (KSPS011Support2.sourceFundamental_eq_Mf + G1004GenT.tsum_terms_eq_fundContT at T = 1);
   * the fundamental-matrix facts used by variation of constants (entries AC on [0,1], a.e. ODE M' = A M,
     det = 1; from GK38.GradFundamentalODE / GradFundamentalDet);
   * k14_rho_ae: the a.e. Riccati residual identity, for every N (including N = 0):
       cover(rho) = sgn * sum c^-k cover(D coef_k) - c * sum c^-k cover(coef_k)
                    + cover(side) * (sum c^-k cover(coef_k))^2 - cover(sideInput),   c = 2 i lam. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.Pilot NlsGge.GK38

theorem sourceFundamental_eq_fundPair
    (N : ℕ) (φ : SobolevC N) (lam : ℂ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSWKB.sourceFundamental φ x lam =
      fundPair (toPotPair φ) lam ⟨x, hx⟩ := by
  rw [KSPSWKB.sourceFundamental_eq_Mf φ lam hx.1]
  unfold NlsGge.Atomic.G1011S2.Mf
  rw [NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT _ lam zero_le_one hx]
  rfl

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS014W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

/-! ### The fundamental matrix, extended from [0,1] -/

/-- `M(x)` on the real line (constant outside [0,1]). -/
def fundExt (p : PotPair) (z : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair p z) x

theorem fundExt_of_mem (p : PotPair) (z : ℂ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    fundExt p z x = fundPair p z ⟨x, hx⟩ := by
  unfold fundExt
  rw [Set.IccExtend_of_mem]

theorem fundExt_ac (p : PotPair) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun x => fundExt p z x i j) 0 1 :=
  ac_fundContP_entry38 p z i j

theorem fundExt_ae_hasDerivAt (p : PotPair) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => fundExt p z r i j) ((zsCoeffPot38 p z s * fundExt p z s) i j) s :=
  ae_hasDerivAt_fundContP_entry38 p z i j

theorem fundExt_continuousOn (p : PotPair) (z : ℂ) (i j : Fin 2) :
    ContinuousOn (fun x => fundExt p z x i j) (Set.Icc (0 : ℝ) 1) := by
  have h := (fundExt_ac p z i j).continuousOn
  rwa [Set.uIcc_of_le zero_le_one] at h

theorem fundExt_det (p : PotPair) (z : ℂ) (x : ℝ) : (fundExt p z x).det = 1 := by
  unfold fundExt Set.IccExtend
  exact det_fundPair38 p z _

theorem fundExt_zero (p : PotPair) (z : ℂ) : fundExt p z 0 = 1 := by
  rw [fundExt_of_mem p z ⟨le_rfl, zero_le_one⟩]
  exact fundPair_zero p z

theorem zsCoeffPot38_apply (p : PotPair) (z : ℂ) (s : ℝ) :
    zsCoeffPot38 p z s 0 0 = -(Complex.I * z) ∧
    zsCoeffPot38 p z s 0 1 = Complex.I * coverRep38 p.1 s ∧
    zsCoeffPot38 p z s 1 0 = -(Complex.I * coverRep38 p.2 s) ∧
    zsCoeffPot38 p z s 1 1 = Complex.I * z := by
  rw [zsCoeffPot38_eq]
  simp [potCoeff38, potRepFst38, potRepSnd38]

/-! ### a.e. linear algebra of representatives -/

theorem cover_sum_smul_ae {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (f : ι → PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (∑ i ∈ s, c i • f i) t = ∑ i ∈ s, c i * coverRep38 (f i) t := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 := coverRep38_smul_ae (0 : ℂ) (0 : PhysicalL2)
    simpa using h0
  | insert a s ha ih =>
    filter_upwards [coverRep38_add_ae (c a • f a) (∑ i ∈ s, c i • f i),
      coverRep38_smul_ae (c a) (f a), ih] with t h1 h2 h3
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h2, h3]

theorem cover_zero_ae : ∀ᵐ t : ℝ, coverRep38 (0 : PhysicalL2) t = 0 := by
  have h0 := coverRep38_smul_ae (0 : ℂ) (0 : PhysicalL2)
  simpa using h0

theorem ae_real_of_ae_phys {p : PhysicalCircle → Prop} (h : ∀ᵐ y ∂spatialMeasure, p y) :
    ∀ᵐ t : ℝ, p (t : PhysicalCircle) := by
  have h1 : ∀ᵐ x ∂NlsGge.Schur.spectralHaar, p (NlsGge.Analysis.naturalPhysicalCover x) :=
    NlsGge.Analysis.naturalPhysicalCover_preserving.quasiMeasurePreserving.ae h
  have h2 := ae_real_of_ae_spectral h1
  simpa only [NlsGge.Analysis.naturalPhysicalCover_coe] using h2

theorem cover_mul_ae (u v : PhysicalL2) (huv : productInL2 u v) :
    ∀ᵐ s : ℝ, coverRep38 (physicalProduct u v) s = coverRep38 u s * coverRep38 v s := by
  have h1 : ∀ᵐ x ∂spatialMeasure, (physicalProduct u v : PhysicalCircle → ℂ) x = u x * v x :=
    physicalProduct_ae u v huv
  have h2 := ae_real_of_ae_phys (p := fun x : PhysicalCircle =>
    (physicalProduct u v : PhysicalCircle → ℂ) x = u x * v x) h1
  filter_upwards [h2, coverRep38_ae_phys (physicalProduct u v), coverRep38_ae_phys u,
    coverRep38_ae_phys v] with s hs1 hs2 hs3 hs4
  rw [hs2, hs3, hs4]
  exact hs1

/-! ### The Riccati residual, a.e. on the real line -/

theorem partial_cover_ae {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    ∀ᵐ x : ℝ, coverRep38 (KSPSRiccati.«partial» φ b lam) x =
      ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
        coverRep38 (KSPSRiccati.coefficient φ b k) x :=
  cover_sum_smul_ae _ _ _

theorem partial_deriv_cover_ae {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    ∀ᵐ x : ℝ, coverRep38 (weakDerivative (KSPSRiccati.«partial» φ b lam)) x =
      ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
        coverRep38 (weakDerivative (KSPSRiccati.coefficient φ b k)) x := by
  have hD : weakDerivative (KSPSRiccati.«partial» φ b lam) =
      ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ •
        weakDerivative (KSPSRiccati.coefficient φ b k) := by
    unfold KSPSRiccati.«partial»
    refine g35_D_sum _ _ _ (fun k hk => ?_)
    have hk' := Finset.mem_Icc.mp hk
    exact NlsGge.ThirdConsultation.KSPSSupport.h150_coef_H1 N (le_trans hk'.1 hk'.2) φ b k hk'.1 hk'.2
  rw [hD]
  exact cover_sum_smul_ae _ _ _

theorem quad_cover_ae {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    ∀ᵐ x : ℝ, coverRep38 (physicalProduct (KSPSRiccati.sidePotential φ b)
        (physicalProduct (KSPSRiccati.«partial» φ b lam) (KSPSRiccati.«partial» φ b lam))) x =
      coverRep38 (KSPSRiccati.sidePotential φ b) x *
        coverRep38 (KSPSRiccati.«partial» φ b lam) x ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hP : KSPSRiccati.«partial» φ b lam = 0 := by
      unfold KSPSRiccati.«partial»
      simp
    rw [hP, physicalProduct_zero', physicalProduct_zero']
    filter_upwards [cover_zero_ae] with x hx
    rw [hx]
    ring
  · filter_upwards [cover_mul_ae _ _
        (NlsGge.ThirdConsultation.KSPSSupport.h150_C6_side_productInL2 hN φ b lam),
      cover_mul_ae _ _ (NlsGge.ThirdConsultation.KSPSSupport.h150_C6_partial_productInL2 hN φ b lam)]
      with x h1 h2
    rw [h1, h2]
    ring

theorem k14_rho_ae {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    ∀ᵐ x : ℝ, coverRep38 (KSPSRiccati.rho φ b lam) x =
      (if b then (-1 : ℂ) else 1) *
          (∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
            coverRep38 (weakDerivative (KSPSRiccati.coefficient φ b k)) x) -
        (2 * Complex.I * lam) *
          (∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
            coverRep38 (KSPSRiccati.coefficient φ b k) x) +
        coverRep38 (KSPSRiccati.sidePotential φ b) x *
          (∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
            coverRep38 (KSPSRiccati.coefficient φ b k) x) ^ 2 -
        coverRep38 (KSPSRiccati.sideInput φ b) x := by
  set P := KSPSRiccati.«partial» φ b lam with hPdef
  have hsd : ∀ᵐ x : ℝ, coverRep38 (KSPSRiccati.signedDerivative b P) x =
      (if b then (-1 : ℂ) else 1) * coverRep38 (weakDerivative P) x := by
    cases b
    · exact Filter.Eventually.of_forall (fun x => by simp [KSPSRiccati.signedDerivative])
    · filter_upwards [coverRep38_smul_ae (-1 : ℂ) (weakDerivative P)] with x hx
      simp only [KSPSRiccati.signedDerivative, if_true]
      rw [← hx, neg_one_smul]
  unfold KSPSRiccati.rho
  rw [← hPdef]
  filter_upwards [coverRep38_sub_ae
      (KSPSRiccati.signedDerivative b P - (2 * Complex.I * lam) • P +
        physicalProduct (KSPSRiccati.sidePotential φ b) (physicalProduct P P))
      (KSPSRiccati.sideInput φ b),
    coverRep38_add_ae (KSPSRiccati.signedDerivative b P - (2 * Complex.I * lam) • P)
      (physicalProduct (KSPSRiccati.sidePotential φ b) (physicalProduct P P)),
    coverRep38_sub_ae (KSPSRiccati.signedDerivative b P) ((2 * Complex.I * lam) • P),
    coverRep38_smul_ae (2 * Complex.I * lam) P,
    hsd, partial_cover_ae φ b lam, partial_deriv_cover_ae φ b lam, quad_cover_ae φ b lam]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, h8, h7, h6]

end
end NlsGge.ThirdConsultation.KSPS014W
