import Mathlib
import NlsGge.Spectral.ActualFullPeriodTwoSelfAdjointV4
import NlsGge.Spectral.ActualTraceFormulaE02_38
import NlsGge.Spectral.ActualGapsActionsE02_38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Atomic.AL.AL094
import NlsGge.GK38.PairPotential
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Atomic.IntervalZS

set_option autoImplicit false

                                                                        
                                                                                                                         
                                                                                                          
                                                                                                                         
                                                                                                                           
                                                                                                                                   
                                                                                                       
                                                                                                                                
                                
                                                                                                                         
                                                                                                                    
                                                                                                                   
                                                                                                                                 
                                                                               

open MeasureTheory Set Filter NlsGge.Pilot NlsGge.Schur
open NlsGge.Analysis NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core
open scoped Topology LinearPMap ContDiff

namespace NlsGge.Atomic.S001
noncomputable section

abbrev DoubledPair := ActualTwoChannelSpectralL2
abbrev DoubledDomain := actualFullPeriodTwoSourceDoubledCircleDomain

abbrev reflectedDirac (u : PhysicalL2) : DoubledPair →ₗ.[ℂ] DoubledPair :=
  actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u (star u)

def physicalDiracAction (u : PhysicalL2) : DoubledDomain →ₗ[ℂ] DoubledPair :=
  -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-u) (star (-u))

def physicalDirac (u : PhysicalL2) : DoubledPair →ₗ.[ℂ] DoubledPair :=
  ⟨actualFullPeriodTwoSourceDoubledCircleDomain, physicalDiracAction u⟩

def phaseSign (x : DoubledPair) : DoubledPair :=
  WithLp.toLp 2 (fun b : Bool => if b then x b else -x b)

def reflectedHalfTrace (u : PhysicalL2) (z : ℂ) : ℂ :=
  actualPhysicalUnitHalfTrace32 (-u) (-z)

def reflectedQuasimomentum (u : PhysicalL2) (z : ℂ) : ℂ :=
  -star (actualQuasimomentumE02_38 (-u) (-star z))

def reflectedBoundary (u : PhysicalL2) (x : ℝ) : ℂ :=
  -star (actualQuasimomentumBoundaryE02_38 (-u) (-x))

def reflectedHeight (u : PhysicalL2) (x : ℝ) : ℝ :=
  Real.arcosh (max 1 ‖reflectedHalfTrace u (x : ℂ)‖)

def reflectedGapLevel (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  {x | (reflectedBoundary u x).re = (n : ℝ) * Real.pi}

def reflectedGapLower (u : PhysicalL2) (n : ℤ) : ℝ :=
  sInf (reflectedGapLevel u n)

def reflectedGapUpper (u : PhysicalL2) (n : ℤ) : ℝ :=
  sSup (reflectedGapLevel u n)

def reflectedAction (u : PhysicalL2) (n : ℤ) : ℝ :=
  (2 / Real.pi) * ∫ x in (reflectedGapLower u n)..
    (reflectedGapUpper u n), reflectedHeight u x

def evenMomentENN (u : PhysicalL2) (j : ℕ) : ENNReal :=
  ENNReal.ofReal (2 / Real.pi) *
    ∫⁻ x : ℝ, ENNReal.ofReal ((2 * x) ^ (2 * j) * actualGapHeightE02_38 u x)

def reflectedEvenMomentENN (u : PhysicalL2) (j : ℕ) : ENNReal :=
  ENNReal.ofReal (2 / Real.pi) *
    ∫⁻ x : ℝ, ENNReal.ofReal ((2 * x) ^ (2 * j) * reflectedHeight u x)

/-! ### operator sign -/

theorem reflectedDirac_sign (u : PhysicalL2) (x : DoubledDomain) :
    reflectedDirac u x = -physicalDirac (-u) x := by
  have h1 : reflectedDirac u x =
      actualFullPeriodTwoDoubledCirclePerturbedDiracAction u (star u) x := rfl
  have h2 : -(physicalDirac (-u) x) =
      actualFullPeriodTwoDoubledCirclePerturbedDiracAction u (star u) x := by
    change -(physicalDiracAction (-u) x) = _
    unfold physicalDiracAction
    simp only [LinearMap.neg_apply, neg_neg]
  exact h1.trans h2.symm

/-! ### S001.04 -/

theorem halfTrace_minusI_potential (u : PhysicalL2) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 ((-Complex.I) • u) z = actualPhysicalUnitHalfTrace32 u z := by
  have hae : (fun t : ℝ => (naturalPhysicalCoverL2 ((-Complex.I) • u) : SpectralCircle → ℂ)
        (t : SpectralCircle)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)]
      (fun s : ℝ => -Complex.I * (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
        (s : SpectralCircle)) :=
    ae_restrict_of_ae (NlsGge.GK38.coverRep38_smul_ae (-Complex.I) u)
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨zero_le_one, by norm_num⟩
  unfold actualPhysicalUnitHalfTrace32
  rw [actualComplexZsDysonTsum_eq_of_ae_eq _ _ z hae 1 h1,
    NlsGge.Atomic.AL094.actualComplexZsDysonTsum_minusI_physical38 u z 1 h1,
    NlsGge.Atomic.AL094.trace_conj_phase38]

theorem halfTrace_neg_potential (u : PhysicalL2) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 (-u) z = actualPhysicalUnitHalfTrace32 u z := by
  have e : (-Complex.I) • ((-Complex.I) • u) = -u := by
    rw [smul_smul]
    have : (-Complex.I) * (-Complex.I) = -1 := by
      rw [neg_mul_neg, Complex.I_mul_I]
    rw [this, neg_one_smul]
  rw [← e, halfTrace_minusI_potential, halfTrace_minusI_potential]

theorem quasimomentum_neg_potential (u : PhysicalL2) :
    EqOn (actualQuasimomentumE02_38 (-u)) (actualQuasimomentumE02_38 u)
      {z : ℂ | 0 < z.im} := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hk' : IsActualQuasimomentumBranchE02_38 (-u) (actualQuasimomentumE02_38 u) :=
    ⟨hk.1, fun z hz => by rw [hk.2.1 z hz, halfTrace_neg_potential], hk.2.2.1, hk.2.2.2⟩
  exact actualQuasimomentumE02_38_eqOn_of_isBranch (-u) _ hk'

theorem boundary_neg_potential (u : PhysicalL2) (x : ℝ) :
    actualQuasimomentumBoundaryE02_38 (-u) x = actualQuasimomentumBoundaryE02_38 u x := by
  have h1 := tendsto_actualQuasimomentumBoundaryE02_38 (-u) x
  have h2 := tendsto_actualQuasimomentumBoundaryE02_38 u x
  have hev : actualQuasimomentumE02_38 (-u) =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)]
      actualQuasimomentumE02_38 u :=
    eventually_nhdsWithin_of_forall (fun z hz => quasimomentum_neg_potential u hz)
  haveI : (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp
      (mem_closure_upperHalfPlane_E02_38 (z := (x : ℂ)) (by simp))
  exact tendsto_nhds_unique (Tendsto.congr' hev h1) h2

/-! ### S001.LIB and S001.05 -/

theorem analyticOnNhd_conj_neg_conj (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im}) :
    AnalyticOnNhd ℂ (fun z => -star (f (-star z))) {z : ℂ | 0 < z.im} := by
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiff : DifferentiableOn ℂ (fun z => -star (f (-star z))) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hw : (-star z) ∈ {w : ℂ | 0 < w.im} := by
      simpa [Complex.star_def] using hz
    have hfd : DifferentiableAt ℂ f (-star z) := (hf _ hw).differentiableAt
    have hh : DifferentiableAt ℂ (fun w : ℂ => f (-w)) (starRingEnd ℂ z) := by
      have e : (-(starRingEnd ℂ z)) = -star z := rfl
      have hf' : DifferentiableAt ℂ f (-(starRingEnd ℂ z)) := by rw [e]; exact hfd
      exact hf'.comp (starRingEnd ℂ z) (differentiableAt_id.neg)
    have hc := hh.conj_conj
    rw [Complex.conj_conj] at hc
    have hn := hc.neg
    exact hn.differentiableWithinAt
  exact hdiff.analyticOnNhd hUo

theorem star_neg_star_im (z : ℂ) : (-star z).im = z.im := by
  simp [Complex.star_def]

theorem reflectedQuasimomentum_spec (u : PhysicalL2) :
    AnalyticOnNhd ℂ (reflectedQuasimomentum u) {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im →
      Complex.cos (reflectedQuasimomentum u z) = reflectedHalfTrace u z) ∧
    (∀ z : ℂ, 0 < z.im → 0 < (reflectedQuasimomentum u z).im) ∧
    (∀ eps : ℝ, 0 < eps → ∃ R : ℝ, 0 < R ∧
      ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
        ‖reflectedQuasimomentum u ((x : ℂ) + Complex.I * (Y : ℂ)) -
          ((x : ℂ) + Complex.I * (Y : ℂ))‖ < eps) := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 (-u)
  refine ⟨analyticOnNhd_conj_neg_conj _ hk.1, ?_, ?_, ?_⟩
  · intro z hz
    unfold reflectedQuasimomentum reflectedHalfTrace
    have hw : 0 < (-star z).im := by rw [star_neg_star_im]; exact hz
    rw [Complex.cos_neg]
    change Complex.cos ((starRingEnd ℂ) (actualQuasimomentumE02_38 (-u) (-star z))) = _
    rw [Complex.cos_conj, hk.2.1 _ hw, ← actualPhysicalUnitHalfTrace32_conj_E02_38]
    congr 1
    simp [Complex.star_def]
  · intro z hz
    have hw : 0 < (-star z).im := by rw [star_neg_star_im]; exact hz
    have h := hk.2.2.1 _ hw
    unfold reflectedQuasimomentum
    simpa [Complex.star_def] using h
  · intro ε hε
    obtain ⟨R, hR, hnorm⟩ := hk.2.2.2 ε hε
    refine ⟨R, hR, fun Y hY x => ?_⟩
    have hw : -star ((x : ℂ) + Complex.I * (Y : ℂ)) = (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ)) := by
      apply Complex.ext <;> simp [Complex.star_def]
    have h := hnorm Y hY (-x)
    unfold reflectedQuasimomentum
    rw [hw]
    have e : -star (actualQuasimomentumE02_38 (-u) (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ))) -
        ((x : ℂ) + Complex.I * (Y : ℂ)) =
        -star (actualQuasimomentumE02_38 (-u) (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ)) -
          (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ))) := by
      apply Complex.ext <;> simp [Complex.star_def] <;> ring
    rw [e, norm_neg]
    have : ‖star (actualQuasimomentumE02_38 (-u) (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ)) -
          (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ)))‖ =
        ‖actualQuasimomentumE02_38 (-u) (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ)) -
          (((-x : ℝ) : ℂ) + Complex.I * (Y : ℂ))‖ := norm_star _
    rw [this]
    exact h

theorem reflectedQuasimomentum_boundary (u : PhysicalL2) (x : ℝ) :
    Tendsto (fun y : ℝ => reflectedQuasimomentum u
      ((x : ℂ) + Complex.I * (y : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (reflectedBoundary u x)) := by
  have hpath : Tendsto (fun y : ℝ => (((-x : ℝ) : ℂ) + Complex.I * (y : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝[{z : ℂ | 0 < z.im}] (((-x : ℝ) : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun y : ℝ => (((-x : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by fun_prop
      have := hc.continuousAt (x := (0 : ℝ)).tendsto
      simpa using tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have h1 := (tendsto_actualQuasimomentumBoundaryE02_38 (-u) (-x)).comp hpath
  have h2 := ((continuous_neg.comp continuous_star).continuousAt
    (x := actualQuasimomentumBoundaryE02_38 (-u) (-x))).tendsto.comp h1
  refine h2.congr (fun y => ?_)
  unfold reflectedQuasimomentum
  have hw : -star ((x : ℂ) + Complex.I * (y : ℂ)) = (((-x : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
    apply Complex.ext <;> simp [Complex.star_def]
  rw [hw]
  rfl

/-! ### S001.06 -/

theorem reflectedBoundary_re (u : PhysicalL2) (x : ℝ) :
    (reflectedBoundary u x).re = -actualQuasimomentumRealPartE02_38 u (-x) := by
  unfold reflectedBoundary actualQuasimomentumRealPartE02_38
  rw [boundary_neg_potential]
  simp [Complex.star_def]

theorem reflectedGapLevel_eq (u : PhysicalL2) (n : ℤ) :
    reflectedGapLevel u n = Neg.neg '' actualGapLevelSetE02_38 u (-n) := by
  ext x
  constructor
  · intro h
    refine ⟨-x, ?_, neg_neg x⟩
    have h' : (reflectedBoundary u x).re = (n : ℝ) * Real.pi := h
    rw [reflectedBoundary_re] at h'
    show actualQuasimomentumRealPartE02_38 u (-x) = ((-n : ℤ) : ℝ) * Real.pi
    push_cast
    linarith
  · rintro ⟨y, hy, rfl⟩
    have hy' : actualQuasimomentumRealPartE02_38 u y = ((-n : ℤ) : ℝ) * Real.pi := hy
    show (reflectedBoundary u (-y)).re = (n : ℝ) * Real.pi
    rw [reflectedBoundary_re, neg_neg, hy']
    push_cast
    ring

theorem reflectedHeight_eq (u : PhysicalL2) (x : ℝ) :
    reflectedHeight u x = actualGapHeightE02_38 u (-x) := by
  unfold reflectedHeight reflectedHalfTrace actualGapHeightE02_38
  rw [halfTrace_neg_potential]
  push_cast
  rfl

/-! ### S001.07 and S001.08 -/

theorem reflectedGap_endpoints (u : PhysicalL2) (n : ℤ) :
    reflectedGapLower u n = -actualGapUpperAllE02_38 u (-n) ∧
    reflectedGapUpper u n = -actualGapLowerAllE02_38 u (-n) := by
  constructor
  · unfold reflectedGapLower actualGapUpperAllE02_38
    rw [reflectedGapLevel_eq, Set.image_neg_eq_neg, Real.sInf_neg]
  · unfold reflectedGapUpper actualGapLowerAllE02_38
    rw [reflectedGapLevel_eq, Set.image_neg_eq_neg, Real.sSup_neg]

theorem reflectedAction_eq (u : PhysicalL2) (n : ℤ) :
    reflectedAction u n = actualGapActionAllE02_38 u (-n) := by
  unfold reflectedAction actualGapActionAllE02_38
  rw [(reflectedGap_endpoints u n).1, (reflectedGap_endpoints u n).2]
  have hH : ∀ x : ℝ, reflectedHeight u x = actualGapHeightE02_38 u (-x) := reflectedHeight_eq u
  simp only [hH]
  have key := intervalIntegral.integral_comp_neg (a := actualGapLowerAllE02_38 u (-n))
    (b := actualGapUpperAllE02_38 u (-n)) (fun x => actualGapHeightE02_38 u (-x))
  simp only [neg_neg] at key
  rw [key]

/-! ### S001.09 -/

theorem reflected_evenMomentENN (u : PhysicalL2) (j : ℕ) :
    reflectedEvenMomentENN u j = evenMomentENN u j := by
  unfold reflectedEvenMomentENN evenMomentENN
  congr 1
  have key := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding
    (fun x : ℝ => ENNReal.ofReal ((2 * x) ^ (2 * j) * actualGapHeightE02_38 u x))
  have e : ∀ x : ℝ, (2 * (-x)) ^ (2 * j) = (2 * x) ^ (2 * j) := fun x => by
    rw [mul_neg, Even.neg_pow (even_two_mul j)]
  rw [← key]
  refine lintegral_congr (fun x => ?_)
  rw [reflectedHeight_eq]
  show _ = ENNReal.ofReal ((2 * (-x)) ^ (2 * j) * actualGapHeightE02_38 u (-x))
  rw [e]

theorem reflected_weightedAction_hasSum_iff (u : PhysicalL2)
    (a : ℤ → ℝ) (ha : ∀ n, a (-n) = a n) (s : ℝ) :
    HasSum (fun n : ℤ => a n * reflectedAction u n) s ↔
      HasSum (fun n : ℤ => a n * actualGapActionAllE02_38 u n) s := by
  have e : (fun n : ℤ => a n * reflectedAction u n) =
      (fun m : ℤ => a m * actualGapActionAllE02_38 u m) ∘ (Equiv.neg ℤ) := by
    funext n
    simp only [Function.comp, Equiv.neg_apply, reflectedAction_eq, ha]
  rw [e]
  exact (Equiv.neg ℤ).hasSum_iff

/-! ### S001.10 -/

theorem evenMomentENN_ne_top_iff (u : PhysicalL2) (j : ℕ) :
    evenMomentENN u j ≠ ⊤ ↔
      Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x) := by
  have hf0 : ∀ x : ℝ, 0 ≤ (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x := fun x =>
    mul_nonneg ((even_two_mul j).pow_nonneg _) (actualGapHeightE02_38_nonneg u x)
  have hcont : Continuous (fun x : ℝ => (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x) :=
    ((continuous_const.mul continuous_id).pow _).mul (continuous_actualGapHeightE02_38 u)
  rw [← lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable (ae_of_all _ hf0)]
  unfold evenMomentENN
  have hc : ENNReal.ofReal (2 / Real.pi) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  constructor
  · intro h h2
    apply h
    rw [h2, ENNReal.mul_top hc]
  · intro h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

theorem reflected_evenMoment_real (u : PhysicalL2) (j : ℕ)
    (hfinite : evenMomentENN u j ≠ ⊤) :
    Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x) ∧
    Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * reflectedHeight u x) ∧
    (2 / Real.pi) * (∫ x : ℝ, (2 * x) ^ (2 * j) * reflectedHeight u x) =
      (2 / Real.pi) * (∫ x : ℝ, (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x) := by
  have hint := (evenMomentENN_ne_top_iff u j).mp hfinite
  have e : (fun x : ℝ => (2 * x) ^ (2 * j) * reflectedHeight u x) =
      fun x : ℝ => (fun y : ℝ => (2 * y) ^ (2 * j) * actualGapHeightE02_38 u y) (-x) := by
    funext x
    simp only [reflectedHeight_eq, mul_neg, Even.neg_pow (even_two_mul j)]
  refine ⟨hint, ?_, ?_⟩
  · rw [e]
    exact hint.comp_neg
  · rw [e, integral_neg_eq_self (fun y : ℝ => (2 * y) ^ (2 * j) * actualGapHeightE02_38 u y)
      volume]

/-! ### S001.11 -/

theorem reflected_evenMoment_smooth (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (j : ℕ) :
    let u := smoothL2_38 U hU hper
    Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x) ∧
    Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * reflectedHeight u x) ∧
    evenMomentENN u j < ⊤ ∧
    reflectedEvenMomentENN u j < ⊤ ∧
    (2 / Real.pi) * (∫ x : ℝ, (2 * x) ^ (2 * j) * reflectedHeight u x) =
      localCharge38 U j ∧
    (2 / Real.pi) * (∫ x : ℝ, (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x) =
      localCharge38 U j := by
  intro u
  have hu := smoothL2_38_sobolev U hU hper
  obtain ⟨hint, heq⟩ := actualTraceFormula_E02_38 u hu U hU hper
    (smoothL2_38_cover_ae U hU hper) j
  have hfin : evenMomentENN u j ≠ ⊤ := (evenMomentENN_ne_top_iff u j).mpr hint
  obtain ⟨_, hint2, hreal⟩ := reflected_evenMoment_real u j hfin
  have hlc : localCharge38 U j = (2 / Real.pi) * ∫ x : ℝ, (2 * x) ^ (2 * j) *
      actualGapHeightE02_38 u x := by
    unfold localCharge38
    exact heq
  refine ⟨hint, hint2, lt_top_iff_ne_top.mpr hfin, ?_, ?_, ?_⟩
  · rw [reflected_evenMomentENN]
    exact lt_top_iff_ne_top.mpr hfin
  · rw [hreal, hlc]
  · rw [hlc]


/-! ### S001.01 (unitarity) and S001.02 (expression bridge) -/

theorem phaseSign_involutive (x : DoubledPair) : phaseSign (phaseSign x) = x := by
  apply PiLp.ext
  intro b
  cases b <;> simp [phaseSign]

theorem phaseSign_unitary :
    ∃ U : DoubledPair ≃ₗᵢ[ℂ] DoubledPair,
      (∀ x, U x = phaseSign x) ∧ (∀ x, U (U x) = x) := by
  have hadd : ∀ x y : DoubledPair, phaseSign (x + y) = phaseSign x + phaseSign y := by
    intro x y
    apply PiLp.ext
    intro b
    cases b <;> simp [phaseSign, neg_add, add_comm]
  have hsmul : ∀ (c : ℂ) (x : DoubledPair), phaseSign (c • x) = c • phaseSign x := by
    intro c x
    apply PiLp.ext
    intro b
    cases b <;> simp [phaseSign]
  have hnorm : ∀ x : DoubledPair, ‖phaseSign x‖ = ‖x‖ := by
    intro x
    have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2) (phaseSign x)
    have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2) x
    have h3 : ‖phaseSign x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [h1, h2]
      simp [Fintype.sum_bool, phaseSign, norm_neg]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3
  let e : DoubledPair ≃ₗ[ℂ] DoubledPair :=
    { toFun := phaseSign
      map_add' := hadd
      map_smul' := hsmul
      invFun := phaseSign
      left_inv := fun x => phaseSign_involutive x
      right_inv := fun x => phaseSign_involutive x }
  exact ⟨⟨e, hnorm⟩, fun x => rfl, fun x => phaseSign_involutive x⟩

def reflectedExpression (phi : SourcePairL2) (f df : Bool → ℝ → ℂ)
    (b : Bool) (x : ℝ) : ℂ :=
  (if b then -Complex.I else Complex.I) * df b x + phi b x * f (!b) x

theorem reflectedExpression_eq_neg (phi : SourcePairL2)
    (f df : Bool → ℝ → ℂ) (b : Bool) :
    (fun x => reflectedExpression phi f df b x) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => -NlsGge.Atomic.Interval.zsExpression (-phi) f df b x) := by
  filter_upwards [Lp.coeFn_neg (phi b)] with x hx
  have hx' : ((-phi) b : SourceIntervalL2) x = -(phi b x) := hx
  unfold reflectedExpression NlsGge.Atomic.Interval.zsExpression
  rw [hx']
  cases b <;> simp <;> ring

/-! ### main spectral theorem -/

theorem reflectedDirac_moments_and_actions (u : PhysicalL2) :
    (∀ n : ℤ,
      reflectedGapLower u n = -actualGapUpperAllE02_38 u (-n) ∧
      reflectedGapUpper u n = -actualGapLowerAllE02_38 u (-n) ∧
      reflectedAction u n = actualGapActionAllE02_38 u (-n)) ∧
    (∀ j : ℕ, reflectedEvenMomentENN u j = evenMomentENN u j) ∧
    (∀ (a : ℤ → ℝ) (_ : ∀ n, a (-n) = a n) (s : ℝ),
      HasSum (fun n : ℤ => a n * reflectedAction u n) s ↔
      HasSum (fun n : ℤ => a n * actualGapActionAllE02_38 u n) s) :=
  ⟨fun n => ⟨(reflectedGap_endpoints u n).1, (reflectedGap_endpoints u n).2,
      reflectedAction_eq u n⟩,
    reflected_evenMomentENN u,
    fun a ha s => reflected_weightedAction_hasSum_iff u a ha s⟩

end


end NlsGge.Atomic.S001
