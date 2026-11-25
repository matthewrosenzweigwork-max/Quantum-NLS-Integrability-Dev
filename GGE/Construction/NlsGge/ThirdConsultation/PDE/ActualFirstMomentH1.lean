import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.Birkhoff.S01Translation38
import NlsGge.GK38.MolnarSignedSquare
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.Spectral.F04MomentTightness38
import NlsGge.Spectral.R3cExpansionK1_38
import NlsGge.Atomic.M.M006
import NlsGge.Analysis.NaturalCover

                                                          
                                                                               
                                                                       

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.PDE

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- Supporting fact: the literal first spectral moment is absolutely integrable
for every physical H1 field. No smooth representative or finite-gap premise. -/
theorem actual_firstSpectralMoment_integrable_h1 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (fun t : ℝ => (2 * t) * actualGapHeightE02_38 u t) := by
  have hi := NlsGge.GK38.MolnarBounds38.actual_height_first_moment_integrable38 u hu
  exact (hi.const_mul 2).congr (Eventually.of_forall fun t => by ring)

/-- Supporting fact: the actual action first-moment series converges on every
physical H1 field and equals minus the project's Fourier momentum. This is NOT
the missing equality with the literal spectral integral. -/
theorem actual_actionFirstMoment_h1 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) ∧
    Summable (fun n : ℤ => 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2) ∧
    (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) =
      -momentumFourier38 u := by
  have hx : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) u).2 (by simpa only [Nat.cast_one] using hu)
  have hTx := actualBirkhoffTop38.mapsTo_T 1 (fourierSeq38 u) hx
  have hterm (n : ℤ) :
      2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n =
        (2 * Real.pi) * ((n : ℝ) * ‖actualBirkhoffTop38.T (fourierSeq38 u) n‖ ^ 2) := by
    rw [← actualBirkhoffTop38.action_L2 u n]
    ring
  have hs : Summable (fun n : ℤ =>
      (2 * Real.pi) * ((n : ℝ) * ‖actualBirkhoffTop38.T (fourierSeq38 u) n‖ ^ 2)) :=
    (summable_mom_sq38 hTx).mul_left (2 * Real.pi)
  have hp : physicalFourier u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (mem_seqSobolev38_iff ((1 : ℕ) : ℝ) (physicalFourier u)).2
      (by simpa only [Nat.cast_one] using hu)
  have hsphys : Summable (fun n : ℤ =>
      2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2) := by
    exact ((summable_mom_sq38 hp).mul_left (2 * Real.pi)).congr (fun n => by ring)
  refine ⟨hs.congr (fun n => (hterm n).symm), hsphys, ?_⟩
  calc
    (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) =
        (2 * Real.pi) * momSeq38 (actualBirkhoffTop38.T (fourierSeq38 u)) := by
          unfold momSeq38
          rw [← tsum_mul_left]
          exact tsum_congr hterm
    _ = (2 * Real.pi) * momSeq38 (fourierSeq38 u) := by
      rw [BirkhoffTop38.momSeq38_T actualBirkhoffTop38 (fourierSeq38 u) hx]
    _ = -momentumFourier38 u := by
      rw [momentumFourier38_eq_neg_canonical]
      ring

private theorem firstIntegrand_norm_le (u : PhysicalL2) (t : ℝ) :
    ‖(2 * t) * actualGapHeightE02_38 u t‖ ≤ momentDensity38 1 u t := by
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (actualGapHeightE02_38_nonneg u t)]
  have hlin : |2 * t| ≤ 1 + (2 * t) ^ 2 := by
    nlinarith [sq_abs (2 * t), sq_nonneg (|2 * t| - 1 / 2)]
  exact mul_le_mul_of_nonneg_right hlin (actualGapHeightE02_38_nonneg u t)

private theorem firstMoment_tail_le (y : SobolevHilbert ((1 : ℕ) : ℝ)) (L : ℝ) :
    |(∫ t : ℝ, (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t) -
      (∫ t in Icc (-L) L, (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t)| ≤
      ∫ t in (Icc (-L) L)ᶜ, momentDensity38 1 (sobolevToL2_38 1 y) t := by
  have hu : SobolevSquareSummable 1 (physicalFourier (sobolevToL2_38 1 y)) := by
    simpa only [Nat.cast_one] using sobolevToL2_38_sobolev 1 y
  have hi := actual_firstSpectralMoment_integrable_h1 (sobolevToL2_38 1 y) hu
  have hm := (fullMoment38 1 le_rfl nonlinRiccatiSmoothBound38_one y).1
  have hsplit := integral_add_compl (s := Icc (-L) L) measurableSet_Icc hi
  have heq :
      (∫ t : ℝ, (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t) -
        (∫ t in Icc (-L) L, (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t) =
      ∫ t in (Icc (-L) L)ᶜ, (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t := by
    linarith
  rw [heq, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono hi.norm.integrableOn hm.integrableOn
    (fun t => firstIntegrand_norm_le _ t)

private theorem momentTail_mono (y : SobolevHilbert ((1 : ℕ) : ℝ))
    (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in (Icc (-B) B)ᶜ, momentDensity38 1 (sobolevToL2_38 1 y) t) ≤
      ∫ t in (Icc (-A) A)ᶜ, momentDensity38 1 (sobolevToL2_38 1 y) t := by
  have hsub : (Icc (-B) B)ᶜ ⊆ (Icc (-A) A)ᶜ := by
    intro t ht hsmall
    exact ht ⟨by linarith [hsmall.1], by linarith [hsmall.2]⟩
  exact setIntegral_mono_set
    (fullMoment38 1 le_rfl nonlinRiccatiSmoothBound38_one y).1.integrableOn
    (Eventually.of_forall fun t => momentDensity38_nonneg 1 _ t) hsub.eventuallyLE

private theorem firstMoment_tendsto_h1
    (y : ℕ → SobolevHilbert ((1 : ℕ) : ℝ))
    (yLim : SobolevHilbert ((1 : ℕ) : ℝ)) (hy : Tendsto y atTop (𝓝 yLim)) :
    Tendsto (fun j => ∫ t : ℝ,
      (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 (y j)) t) atTop
      (𝓝 (∫ t : ℝ, (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 yLim) t)) := by
  have hu := ((sobolevToL2_38 1).continuous.tendsto yLim).comp hy
  have hunif : ∀ L ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Icc (-L) L,
      |actualGapHeightE02_38 (sobolevToL2_38 1 (y j)) t -
        actualGapHeightE02_38 (sobolevToL2_38 1 yLim) t| < ε := by
    intro L ε hε
    exact eventually_atTop.mp (heights_uniform_eventually38 _ _ hu L hε)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hA, jA, hjA⟩ := moment_tight38 1 le_rfl
    nonlinRiccatiSmoothBound38_one y yLim hy (ε / 4) (by positivity)
  obtain ⟨B, hB, jB, hjB⟩ := moment_tight38 1 le_rfl
    nonlinRiccatiSmoothBound38_one (fun _ : ℕ => yLim) yLim
    tendsto_const_nhds (ε / 4) (by positivity)
  let L := max A B
  have hL : 0 ≤ L := hA.trans (le_max_left A B)
  have hcompact := setIntegral_tendsto_of_unif38
    (fun t : ℝ => 2 * t) (continuous_const.mul continuous_id)
    (fun j => actualGapHeightE02_38 (sobolevToL2_38 1 (y j)))
    (actualGapHeightE02_38 (sobolevToL2_38 1 yLim))
    (fun j => continuous_actualGapHeightE02_38 _)
    (continuous_actualGapHeightE02_38 _) hunif L hL
  obtain ⟨jC, hjC⟩ := (Metric.tendsto_atTop.mp hcompact) (ε / 4) (by positivity)
  refine ⟨max jA jC, fun j hj => ?_⟩
  have hjA' : jA ≤ j := (le_max_left jA jC).trans hj
  have hjC' : jC ≤ j := (le_max_right jA jC).trans hj
  have htailj := (firstMoment_tail_le (y j) L).trans
    ((momentTail_mono (y j) A L (le_max_left A B)).trans (hjA j hjA'))
  have htailLim := (firstMoment_tail_le yLim L).trans
    ((momentTail_mono yLim B L (le_max_right A B)).trans (hjB jB le_rfl))
  have hjc := hjC j hjC'
  rw [Real.dist_eq, abs_lt] at hjc ⊢
  have h1 := (abs_le.mp htailj).1
  have h2 := (abs_le.mp htailj).2
  have h3 := (abs_le.mp htailLim).1
  have h4 := (abs_le.mp htailLim).2
  constructor <;> linarith [hjc.1, hjc.2]

private theorem continuous_firstMoment_ordinary_h1 :
    Continuous (fun y : SobolevHilbert ((1 : ℕ) : ℝ) =>
      (2 / Real.pi) * ∫ t : ℝ,
        (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t) := by
  rw [continuous_iff_seqContinuous]
  intro y yLim hy
  exact (firstMoment_tendsto_h1 y yLim hy).const_mul (2 / Real.pi)

private theorem ordinary_field_eq (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
    sobolevToL2_38 m (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates m u) =
      physicalSobolevEmbed m u := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, sobolevToL2_38_fourier]
  exact ordinarySobolevCarrier38_fourier m u n

/-- The literal signed spectral first moment is continuous on the genuine
completed physical H1 carrier. The bound used above is the actual spectral
mass plus second moment, with its R3c input discharged at k = 1. -/
theorem actual_firstSpectralMoment_continuous_h1 :
    Continuous (fun u : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      (2 / Real.pi) * ∫ t : ℝ,
        (2 * t) * actualGapHeightE02_38 (physicalSobolevEmbed 1 u) t) := by
  have hc := continuous_firstMoment_ordinary_h1.comp
    (NlsGge.ThirdConsultation.M.continuous_ordinarySobolevCoordinates 1)
  exact hc.congr (fun u => by
    simp only [Function.comp_apply]
    rw [ordinary_field_eq 1 u])

/-- The actual action first-moment series is continuous on the genuine H1
carrier, by continuity of the SAME actual Birkhoff map on h1 and its momentum
quadratic form. This does not use the spectral first-moment identity. -/
theorem actual_actionFirstMoment_continuous_h1 :
    Continuous (fun u : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      ∑' n : ℤ, 2 * Real.pi * (n : ℝ) *
        actualGapActionAllE02_38 (physicalSobolevEmbed 1 u) n) := by
  have hc : Continuous (fun u : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      (2 * Real.pi) * momSeq38 (carrierCoe38 ((1 : ℕ) : ℝ)
        (actualBirkhoffTop38.TC 1 (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u)))) :=
    continuous_const.mul (BirkhoffTop38.continuous_momSeq38_carrier.comp
      ((actualBirkhoffTop38.continuous_TC 1).comp
        (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).continuous))
  refine hc.congr (fun u => ?_)
  have hcoef : carrierCoe38 ((1 : ℕ) : ℝ)
      (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u) =
      fourierSeq38 (physicalSobolevEmbed 1 u) := by
    funext n
    exact (physicalSobolevEmbed_fourier 1 u n).symm
  unfold momSeq38
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [BirkhoffTop38.TC_coe, hcoef, actualBirkhoffTop38.action_L2]
  ring

private theorem continuous_momentumFourier_ordinary_h1 :
    Continuous (fun y : SobolevHilbert ((1 : ℕ) : ℝ) =>
      momentumFourier38 (sobolevToL2_38 1 y)) := by
  have hc : Continuous (fun y : SobolevHilbert ((1 : ℕ) : ℝ) =>
      (2 * Real.pi) * momSeq38 (carrierCoe38 ((1 : ℕ) : ℝ)
        (toCarrier38 ((1 : ℕ) : ℝ) y))) :=
    continuous_const.mul (BirkhoffTop38.continuous_momSeq38_carrier.comp
      (continuous_toCarrier38 ((1 : ℕ) : ℝ)))
  refine hc.congr (fun y => ?_)
  unfold momentumFourier38 momSeq38
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sobolevToL2_38_fourier]
  change (2 * Real.pi) * ((n : ℝ) *
      ‖(show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from y) n‖ ^ 2) = _
  ring

private theorem firstMoment_eq_neg_fourier_ordinary_h1
    (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    ((2 / Real.pi) * ∫ t : ℝ,
      (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 y) t) =
      -momentumFourier38 (sobolevToL2_38 1 y) := by
  let z := toCarrier38 ((1 : ℕ) : ℝ) y
  let yN : ℕ → SobolevHilbert ((1 : ℕ) : ℝ) := fun N =>
    ofCarrier38 ((1 : ℕ) : ℝ) (truncC38 ((1 : ℕ) : ℝ) N z)
  have hyN : Tendsto yN atTop (𝓝 y) :=
    ((continuous_ofCarrier38 ((1 : ℕ) : ℝ)).tendsto z).comp
      (tendsto_truncC38 ((1 : ℕ) : ℝ) z)
  have hN : ∀ N : ℕ,
      ((2 / Real.pi) * ∫ t : ℝ,
        (2 * t) * actualGapHeightE02_38 (sobolevToL2_38 1 (yN N)) t) =
        -momentumFourier38 (sobolevToL2_38 1 (yN N)) := by
    intro N
    have hcoef : physicalFourier (sobolevToL2_38 1 (yN N)) =
        carrierCoe38 ((1 : ℕ) : ℝ) (truncC38 ((1 : ℕ) : ℝ) N z) := by
      funext n
      exact sobolevToL2_38_fourier 1 (yN N) n
    have hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ)
        (physicalFourier (sobolevToL2_38 1 (yN N))) := by
      intro m
      rw [hcoef]
      exact (mem_seqSobolev38_iff (m : ℝ) _).1
        (finiteSupport_mem_seqSobolev38 (m : ℝ) _
          (finiteSupport_truncC38 ((1 : ℕ) : ℝ) N z))
    obtain ⟨U, hU, hper, hUeq⟩ := exists_smooth_rep38 _ hall
    have hu1 : SobolevSquareSummable 1
        (physicalFourier (sobolevToL2_38 1 (yN N))) := by
      simpa only [Nat.cast_one] using hall 1
    have hae :
        (fun s : ℝ => (NlsGge.Analysis.naturalPhysicalCoverL2 (sobolevToL2_38 1 (yN N)) :
          SpectralCircle → ℂ) (s : SpectralCircle))
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] U := by
      rw [← hUeq]
      exact smoothL2_38_cover_ae U hU hper
    have hP : momentumE02_38 U = momentumFourier38 (sobolevToL2_38 1 (yN N)) := by
      rw [← hUeq]
      exact momentumE02_eq_momentumFourier38 U hU hper
    have hs := (actualFirstMoment_eq_neg_momentum_E02_38 _ hu1 U hU hper hae).2
    rw [hP] at hs
    exact hs
  have hspec := (continuous_firstMoment_ordinary_h1.tendsto y).comp hyN
  have hphys := ((continuous_momentumFourier_ordinary_h1.tendsto y).comp hyN).neg
  exact tendsto_nhds_unique (hspec.congr hN) hphys

/-- Literal first spectral moment equals the full actual action series and
minus the Fourier momentum on every physical H1 field. Both series converge. -/
theorem actual_firstSpectralMoment_eq_actions_h1 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (fun t : ℝ => (2 * t) * actualGapHeightE02_38 u t) ∧
    Summable (fun n : ℤ => 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) ∧
    Summable (fun n : ℤ => 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2) ∧
    ((2 / Real.pi) * ∫ t : ℝ, (2 * t) * actualGapHeightE02_38 u t) =
      (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) ∧
    (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) =
      -momentumFourier38 u := by
  obtain ⟨y, hy⟩ := exists_sobolev_link38 ((1 : ℕ) : ℝ) u
    (by simpa only [Nat.cast_one] using hu)
  have hfield : sobolevToL2_38 1 y = u := by
    apply physicalFourierL2.injective
    apply lp.ext
    funext n
    rw [physicalFourierL2_apply, physicalFourierL2_apply, sobolevToL2_38_fourier, hy n]
  have hs := firstMoment_eq_neg_fourier_ordinary_h1 y
  rw [hfield] at hs
  obtain ⟨ha, hp, heq⟩ := actual_actionFirstMoment_h1 u hu
  exact ⟨actual_firstSpectralMoment_integrable_h1 u hu, ha, hp, hs.trans heq.symm, heq⟩

private theorem weakMomentum_integrable (u w : PhysicalL2) :
    Integrable (fun x : PhysicalCircle => star (u x) * w x) spatialMeasure := by
  have h := L2.integrable_inner (𝕜 := ℂ) u w
  exact h.congr (Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

private theorem weakMomentum_hasSum (u w : PhysicalL2) (hw : IsFourierDeriv38 u w) :
    HasSum (fun n : ℤ => 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2)
      (∫ x : PhysicalCircle, star (u x) * w x ∂spatialMeasure).im := by
  have hP := (fourierBasis (T := (1 : ℝ))).hasSum_inner_mul_inner u w
  have hcoef (v : PhysicalL2) (i : ℤ) :
      inner ℂ ((fourierBasis (T := (1 : ℝ))) i) v = physicalFourier v i :=
    (HilbertBasis.repr_apply_apply _ v i).symm.trans (fourierBasis_repr v i)
  have hterm (i : ℤ) :
      (inner ℂ u ((fourierBasis (T := (1 : ℝ))) i) *
        inner ℂ ((fourierBasis (T := (1 : ℝ))) i) w).im =
        2 * Real.pi * (i : ℝ) * ‖physicalFourier u i‖ ^ 2 := by
    have he : inner ℂ u ((fourierBasis (T := (1 : ℝ))) i) =
        (starRingEnd ℂ) (physicalFourier u i) := by
      rw [← hcoef u i]
      exact (inner_conj_symm _ _).symm
    rw [he, hcoef w i, hw i]
    set c := physicalFourier u i
    have hm : (starRingEnd ℂ) c *
        (2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * c) =
        (((2 * Real.pi * (i : ℝ) * ‖c‖ ^ 2 : ℝ) : ℂ)) * Complex.I := by
      have hc := Complex.conj_mul' c
      push_cast
      calc
        (starRingEnd ℂ) c * (2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * c) =
            2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * ((starRingEnd ℂ) c * c) := by ring
        _ = _ := by rw [hc]; ring
    rw [hm, Complex.mul_I_im, Complex.ofReal_re]
  have hJ : inner ℂ u w =
      ∫ x : PhysicalCircle, star (u x) * w x ∂spatialMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp [RCLike.inner_apply, mul_comm]
  have hIm := hP.mapL Complex.imCLM
  have hIm' : HasSum (fun n : ℤ =>
      2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2) (inner ℂ u w).im := by
    refine hIm.congr_fun (fun n => ?_)
    exact (hterm n).symm
  rw [hJ] at hIm'
  exact hIm'

/-- The source's full H1 first-moment identity, with an earned weak L2
derivative and the literal physical momentum integral. -/
theorem actual_firstSpectralMoment_h1 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ w : PhysicalL2,
      IsFourierDeriv38 u w ∧
      Integrable (fun x : PhysicalCircle => star (u x) * w x) spatialMeasure ∧
      Integrable (fun t : ℝ => (2 * t) * actualGapHeightE02_38 u t) ∧
      Summable (fun n : ℤ =>
        2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) ∧
      ((2 / Real.pi) * ∫ t : ℝ,
        (2 * t) * actualGapHeightE02_38 u t) =
        (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) ∧
      (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) =
        -(∫ x : PhysicalCircle, star (u x) * w x ∂spatialMeasure).im := by
  obtain ⟨w, hw⟩ := exists_fourierDeriv38 u hu
  have hwi := weakMomentum_integrable u w
  have hsumP := weakMomentum_hasSum u w hw
  obtain ⟨hi, hsA, _, hspec, ha⟩ := actual_firstSpectralMoment_eq_actions_h1 u hu
  refine ⟨w, hw, hwi, hi, hsA, hspec, ?_⟩
  calc
    (∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) =
        -momentumFourier38 u := ha
    _ = -(∫ x : PhysicalCircle, star (u x) * w x ∂spatialMeasure).im := by
      exact congrArg Neg.neg hsumP.tsum_eq

end NlsGge.ThirdConsultation.PDE

