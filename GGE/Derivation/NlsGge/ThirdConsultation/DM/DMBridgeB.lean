import Mathlib
import NlsGge.Atomic.KST.KST013
import NlsGge.Atomic.DM.DM002
import NlsGge.Atomic.DM.DM004
import NlsGge.ThirdConsultation.DM.DMShared78
import NlsGge.Atomic.DM.DM016Eig

/- DMBridgeB PRODUCTION (proof development, author; not self-reviewed; supporting module, not a packet).
   Target: NlsGge/ThirdConsultation/DM/DMBridgeB.lean.  Bridges S4 (both directions, separate lemmas) and S5 of
   Pro round 11 section 2.4 (DM2831_BRIDGE_STOP.md as amended by REVIEW_DM028_031_01.md).
   Route: block lift/sector components of KST013.dirac (private KST013 lemma re-proved), sector separation from the
   KST013 uniqueness clause, unit-interval ZS <-> sector eigenvector via the actual-source API, piDirac via DM002. -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace NlsGge.ThirdConsultation.DM.BridgeB
noncomputable section

open NlsGge.Schur NlsGge.Schur.TransportBridgeV4 NlsGge.Atomic.DM001 NlsGge.Atomic.DM002
open NlsGge.SpectralFoundations

/-- The source-interval potential of `unitPhysical f` is `f` itself, a.e. on the unit interval. -/
theorem sourcePot_ae (f : UnitL2) :
    (actualPhysicalL2SourcePotential (unitPhysical f) : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (f : ℝ → ℂ) := by
  have h1 := scalarParityRestrictValue_ae 0
    ⟨NlsGge.Analysis.naturalPhysicalCoverL2 (unitPhysical f),
      NlsGge.Analysis.naturalPhysicalCoverL2_mem_even _⟩
  have h2 := N08.e02Pot_ae_unitPhysical f
  exact h1.trans h2

theorem sourcePot_neg_ae (f : UnitL2) :
    (actualPhysicalL2SourcePotential (-(unitPhysical f)) : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => -(f : ℝ → ℂ) t := by
  have hneg : actualPhysicalL2SourcePotential (-(unitPhysical f)) =
      -actualPhysicalL2SourcePotential (unitPhysical f) := by
    unfold actualPhysicalL2SourcePotential
    rw [← map_neg]
    congr 1
    apply Subtype.ext
    exact map_neg _ _
  rw [hneg]
  filter_upwards [Lp.coeFn_neg (actualPhysicalL2SourcePotential (unitPhysical f)), sourcePot_ae f]
    with t h1 h2
  rw [h1]
  simp only [Pi.neg_apply, h2]



/-- Component formula of the block operator on the recovered source domain (free part plus potential part). -/
theorem action_component (n : ℤ) (u₁ u₂ : NlsGge.Pilot.PhysicalL2)
    (Y : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ Y : SourcePairL2) b =
      (if b then -Complex.I else Complex.I) •
          sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b +
        actualL2PotentialParityPairSourceOperator u₁ u₂
          (actualSourceWeightedDomainLInfRepresentativeMap n
            (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y)) b := by
  change actualSourceFreeDiracMapAfterAE n Y b +
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ Y b = _
  rw [actualSourceFreeDiracMapAfterAE_component_eq_sourceFreeDiracAction,
    actualSourcePotentialOnRecoveredWeightedDomain_apply]
  rfl

theorem potop_component (ψ : SourcePairL2) (n : ℤ)
    (Y : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    actualL2PotentialParityPairSourceOperator
        (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false)))
        (actualSourceWeightedDomainLInfRepresentativeMap n
          (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y)) b =
      actualSourceL2PotentialTimesLInf (-(unitPhysical (ψ b)))
        (sourceIntervalLInfOfContinuousOn (actualSourceGraphContinuousRepresentative n Y (!b))
          (continuous_actualSourceGraphContinuousRepresentative n Y (!b)).continuousOn) := by
  cases b
  · rw [actualL2PotentialParityPairSourceOperator_apply_false,
      actualSourceGraphContinuousRepresentative_LInf_eq]
    rfl
  · rw [actualL2PotentialParityPairSourceOperator_apply_true,
      actualSourceGraphContinuousRepresentative_LInf_eq]
    rfl

/-- A.e. pointwise form of the block operator with potentials `-unitPhysical (ψ b)`. -/
theorem action_component_ae (ψ : SourcePairL2) (n : ℤ)
    (Y : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      (actualSourcePerturbedDiracPMapAfterAE n
          (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false))) Y : SourcePairL2) b t =
        (if b then -Complex.I else Complex.I) *
            (sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b :
              SourceIntervalL2) t +
          (-((ψ b : SourceIntervalL2) t)) * actualSourceGraphContinuousRepresentative n Y (!b) t := by
  have h0 := action_component n (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false))) Y b
  rw [potop_component ψ n Y b] at h0
  filter_upwards [Lp.coeFn_add ((if b then -Complex.I else Complex.I) •
        sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b)
      (actualSourceL2PotentialTimesLInf (-(unitPhysical (ψ b)))
        (sourceIntervalLInfOfContinuousOn (actualSourceGraphContinuousRepresentative n Y (!b))
          (continuous_actualSourceGraphContinuousRepresentative n Y (!b)).continuousOn)),
    Lp.coeFn_smul (if b then -Complex.I else Complex.I)
      (sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b),
    actualSourceL2PotentialTimesLInf_ae (-(unitPhysical (ψ b)))
      (sourceIntervalLInfOfContinuousOn (actualSourceGraphContinuousRepresentative n Y (!b))
        (continuous_actualSourceGraphContinuousRepresentative n Y (!b)).continuousOn),
    sourceIntervalLInfOfContinuousOn_ae (actualSourceGraphContinuousRepresentative n Y (!b))
      (continuous_actualSourceGraphContinuousRepresentative n Y (!b)).continuousOn,
    sourcePot_neg_ae (ψ b)] with t h1 h2 h3 h4 h5
  rw [h0, h1]
  simp only [Pi.add_apply]
  rw [h2, h3, h4, h5]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem dfun_alg_true (lam P Q Dd a : ℂ)
    (h : -Complex.I * Dd + (-P) * Q = (-lam) * a) :
    Dd = (-Complex.I) * (lam * a - P * Q) := by
  linear_combination (Complex.I) * h + Dd * Complex.I_mul_I

theorem dfun_alg_false (lam P Q Dd a : ℂ)
    (h : Complex.I * Dd + (-P) * Q = (-lam) * a) :
    Dd = Complex.I * (lam * a - P * Q) := by
  linear_combination (-Complex.I) * h + Dd * Complex.I_mul_I

/-- A sector eigenvector of the actual block operator (potentials `-unitPhysical (ψ b)`, eigenvalue `-lam`)
is a unit-interval `H1Pair` ZS eigenpair of `ψ` with eigenvalue `lam` and the twisted boundary of its sector. -/
theorem sector_eigen_to_h1 (ψ : SourcePairL2) (n : ℤ) (lam : ℂ)
    (Y : recoveredActualSourceFreeWeightedDomain n)
    (hY : actualSourcePerturbedDiracPMapAfterAE n
        (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false))) Y = (-lam) • (Y : SourcePairL2)) :
    ∃ g : NlsGge.Atomic.Interval.H1Pair, NlsGge.Atomic.Interval.h1PairValue g = (Y : SourcePairL2) ∧
      (∀ b, NlsGge.Atomic.LIB026.traceRight (g b) =
        spectralSign n * NlsGge.Atomic.LIB026.traceLeft (g b)) ∧
      NlsGge.Atomic.Interval.zsApply ψ g = lam • NlsGge.Atomic.Interval.h1PairValue g := by
  classical
  let F : ℝ → Fin 2 → ℂ := actualSourceGraphContinuousVector n Y
  have hFb : ∀ (b : Bool) (s : ℝ),
      F s (N08.kk b) = actualSourceGraphContinuousRepresentative n Y b s := by
    intro b s; cases b <;> rfl
  have hcomp : ∀ b : Bool, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc (0 : ℝ) 1 →
      HasDerivAt (actualSourceGraphContinuousRepresentative n Y b) (N08.dfun ψ lam F b t) t := by
    intro b
    have hY0 := actualSourceGraphContinuousRepresentative_ae_source_class n Y b
    have hder0 := freeDomainContinuousComponent_source_ae_hasDerivAt n (sourcePairRepr n Y.val)
      Y.property b
    have hpt : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        (if b then -Complex.I else Complex.I) *
            (sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b :
              SourceIntervalL2) t +
          (-((ψ b : SourceIntervalL2) t)) * actualSourceGraphContinuousRepresentative n Y (!b) t =
        (-lam) * actualSourceGraphContinuousRepresentative n Y b t := by
      filter_upwards [action_component_ae ψ n Y b, hY0,
        Lp.coeFn_smul (-lam) (Y.val b)] with t h1 h2 h3
      have h : (actualSourcePerturbedDiracPMapAfterAE n
          (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false))) Y : SourcePairL2) b t =
          (((-lam) • (Y : SourcePairL2)) b : SourceIntervalL2) t :=
        congrArg (fun P : SourcePairL2 => (P b : SourceIntervalL2) t) hY
      rw [← h1, h]
      change ((-lam) • Y.val b : SourceIntervalL2) t = _
      rw [h3, h2]
      simp only [Pi.smul_apply, smul_eq_mul]
    filter_upwards [hder0, (ae_restrict_iff' measurableSet_Ioc).mp hpt] with t hd hp ht
    have hd' : HasDerivAt (actualSourceGraphContinuousRepresentative n Y b)
        (sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b t) t :=
      hd (by rw [uIcc_of_le zero_le_one]; exact ⟨ht.1.le, ht.2⟩)
    have hp' := hp ht
    have hdf : N08.dfun ψ lam F b t = (if b then -Complex.I else Complex.I) *
        (lam * actualSourceGraphContinuousRepresentative n Y b t -
          (ψ b : SourceIntervalL2) t * actualSourceGraphContinuousRepresentative n Y (!b) t) := by
      simp only [N08.dfun, hFb]
    rw [hdf]
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hp' ⊢
      rw [← dfun_alg_false lam _ _ _ _ hp']
      exact hd'
    · simp only [ite_true] at hp' ⊢
      rw [← dfun_alg_true lam _ _ _ _ hp']
      exact hd'
  have hder : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc (0 : ℝ) 1 → ∀ b : Bool,
      HasDerivAt (fun s => F s (N08.kk b)) (N08.dfun ψ lam F b t) t := by
    filter_upwards [hcomp true, hcomp false] with t h1 h2 ht b
    have hfe : (fun s => F s (N08.kk b)) = actualSourceGraphContinuousRepresentative n Y b :=
      funext (hFb b)
    rw [hfe]
    cases b
    · exact h2 ht
    · exact h1 ht
  obtain ⟨g, hL, hR, hv, heig⟩ := N08.h1_of_solution ψ lam F
    (absolutelyContinuous_actualSourceGraphContinuousVector n Y) hder
  refine ⟨g, ?_, ?_, heig⟩
  · apply PiLp.ext
    intro b
    apply Lp.ext
    filter_upwards [hv b, actualSourceGraphContinuousRepresentative_ae_source_class n Y b]
      with t h1 h2
    change (g b).value t = Y.val b t
    rw [h1, hFb, h2]
  · intro b
    have htw := congrFun (actualSourceGraphContinuousVector_twisted_endpoint n Y) (N08.kk b)
    rw [hR b, hL b]
    simpa only [Pi.smul_apply, smul_eq_mul] using htw


/-! ### Block lift: a sector vector gives a `dirac` eigenvector, and conversely every sector component of a `dirac`
eigenvector is a sector eigenvector.  (The private KST013 lemma `source13_full_actual_operator_eigenvector_iff_parity_branch`
is re-proved here for the original-sign operator `dirac`, with sector bookkeeping kept explicit.) -/

/-- The vector of the doubled carrier supported in sector `p`. -/
def sectorVec (p : Fin 2) (Y : SourcePairL2) : ActualFullPeriodTwoSourcePair :=
  WithLp.toLp 2 (fun q : Fin 2 => if q = p then Y else 0)

theorem sectorVec_mem (p : Fin 2) (Y : recoveredActualSourceFreeWeightedDomain (p.val : ℤ)) :
    sectorVec p (Y : SourcePairL2) ∈ actualFullPeriodTwoSourceBlockDomain := by
  intro q
  by_cases hq : q = p
  · subst hq
    simpa only [sectorVec, ↓reduceIte] using Y.property
  · simpa only [sectorVec, hq, ↓reduceIte] using
      (recoveredActualSourceFreeWeightedDomain (q.val : ℤ)).zero_mem

theorem sector_lift (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (p : Fin 2) (lam : ℂ)
    (Y : recoveredActualSourceFreeWeightedDomain (p.val : ℤ))
    (hY : actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) (-(φ true)) (-(φ false)) Y =
      (-lam) • (Y : SourcePairL2)) :
    ∃ f : (NlsGge.Atomic.KST013.dirac φ).domain,
      actualFullPeriodTwoSourceIntervalAssembly (f : NlsGge.Atomic.KST003.KSTPairL2) =
        sectorVec p (Y : SourcePairL2) ∧
      NlsGge.Atomic.KST013.dirac φ f = lam • (f : NlsGge.Atomic.KST003.KSTPairL2) := by
  classical
  set a := sectorVec p (Y : SourcePairL2) with ha_def
  have ha : a ∈ actualFullPeriodTwoSourceBlockDomain := sectorVec_mem p Y
  have haComp : ∀ q : Fin 2, a q ∈ recoveredActualSourceFreeWeightedDomain (q.val : ℤ) := ha
  have haAction : actualFullPeriodTwoSourceBlockAction (-(φ true)) (-(φ false)) ⟨a, ha⟩ =
      (-lam) • a := by
    apply PiLp.ext
    intro q
    by_cases hq : q = p
    · subst hq
      change actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) (-(φ true)) (-(φ false))
        ⟨a q, haComp q⟩ = (-lam) • a q
      have hY' : (⟨a q, haComp q⟩ : recoveredActualSourceFreeWeightedDomain (q.val : ℤ)) = Y := by
        apply Subtype.ext
        simp only [a, sectorVec, ↓reduceIte]
      have hActionEq := congrArg
        (fun X : recoveredActualSourceFreeWeightedDomain (q.val : ℤ) =>
          actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) (-(φ true)) (-(φ false)) X) hY'
      exact hActionEq.trans (hY.trans (by simp only [a, sectorVec, ↓reduceIte]))
    · change actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) (-(φ true)) (-(φ false))
        ⟨a q, haComp q⟩ = (-lam) • a q
      have hzero : (⟨a q, haComp q⟩ : recoveredActualSourceFreeWeightedDomain (q.val : ℤ)) = 0 := by
        apply Subtype.ext
        simp only [a, sectorVec, hq, ↓reduceIte, Submodule.coe_zero]
      have hActionEq := congrArg
        (fun X : recoveredActualSourceFreeWeightedDomain (q.val : ℤ) =>
          actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) (-(φ true)) (-(φ false)) X) hzero
      have hmapZero := LinearPMap.map_zero
        (actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) (-(φ true)) (-(φ false)))
      exact hActionEq.trans (hmapZero.trans (by simp only [a, sectorVec, hq, ↓reduceIte, smul_zero]))
  let f : NlsGge.Atomic.KST003.KSTPairL2 := actualFullPeriodTwoSourceIntervalAssembly.symm a
  have haf : actualFullPeriodTwoSourceIntervalAssembly f = a :=
    actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply a
  have hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain := by
    change actualFullPeriodTwoSourceIntervalAssembly f ∈ actualFullPeriodTwoSourceBlockDomain
    rw [haf]; exact ha
  refine ⟨⟨f, hf⟩, haf, ?_⟩
  have hdirac : NlsGge.Atomic.KST013.dirac φ ⟨f, hf⟩ =
      -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false)) ⟨f, hf⟩ := rfl
  rw [hdirac]
  apply actualFullPeriodTwoSourceIntervalAssembly.injective
  have hrepr : actualFullPeriodTwoSourceIntervalAssembly
      (actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false)) ⟨f, hf⟩) =
        actualFullPeriodTwoSourceBlockAction (-(φ true)) (-(φ false))
          ⟨actualFullPeriodTwoSourceIntervalAssembly f, hf⟩ :=
    actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr _ _ _
  have hdomeq : (⟨actualFullPeriodTwoSourceIntervalAssembly f, hf⟩ :
      actualFullPeriodTwoSourceBlockDomain) = ⟨a, ha⟩ := Subtype.ext haf
  rw [hdomeq, haAction] at hrepr
  rw [map_neg, hrepr]
  change -((-lam) • a) = actualFullPeriodTwoSourceIntervalAssembly (lam • f)
  rw [map_smul, haf, neg_smul, neg_neg]

/-- Every sector component of a `dirac` eigenvector is a sector eigenvector of the block operator. -/
theorem eigen_sector_component (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (lam : ℂ)
    (f : (NlsGge.Atomic.KST013.dirac φ).domain)
    (hf : NlsGge.Atomic.KST013.dirac φ f = lam • (f : NlsGge.Atomic.KST003.KSTPairL2))
    (p : Fin 2) :
    actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) (-(φ true)) (-(φ false))
      ⟨actualFullPeriodTwoSourceIntervalAssembly (f : NlsGge.Atomic.KST003.KSTPairL2) p,
        f.property p⟩ =
      (-lam) • actualFullPeriodTwoSourceIntervalAssembly (f : NlsGge.Atomic.KST003.KSTPairL2) p := by
  have hdirac : NlsGge.Atomic.KST013.dirac φ f =
      -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
        ⟨(f : NlsGge.Atomic.KST003.KSTPairL2), f.property⟩ := rfl
  have hact : actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
      ⟨(f : NlsGge.Atomic.KST003.KSTPairL2), f.property⟩ =
        (-lam) • (f : NlsGge.Atomic.KST003.KSTPairL2) := by
    have h := congrArg (fun x : NlsGge.Atomic.KST003.KSTPairL2 => -x) (hdirac.symm.trans hf)
    simpa only [neg_neg, neg_smul] using h
  have hrepr : actualFullPeriodTwoSourceIntervalAssembly
      (actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
        ⟨(f : NlsGge.Atomic.KST003.KSTPairL2), f.property⟩) =
        actualFullPeriodTwoSourceBlockAction (-(φ true)) (-(φ false))
          ⟨actualFullPeriodTwoSourceIntervalAssembly (f : NlsGge.Atomic.KST003.KSTPairL2),
            f.property⟩ :=
    actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr _ _ _
  rw [hact, map_smul] at hrepr
  have hp := congrArg (fun a : ActualFullPeriodTwoSourcePair => a p) hrepr
  exact hp.symm

/-- A unit-interval ZS eigenpair `g` with the twisted boundary of sector `p` is a sector eigenvector of the
actual block operator (potentials `-unitPhysical (ψ b)`, eigenvalue `-lam`). -/
theorem h1_to_sector_eigen (ψ : SourcePairL2) (n : ℤ) (lam : ℂ)
    (g : NlsGge.Atomic.Interval.H1Pair)
    (hbc : ∀ b, NlsGge.Atomic.LIB026.traceRight (g b) =
      spectralSign n * NlsGge.Atomic.LIB026.traceLeft (g b))
    (heig : NlsGge.Atomic.Interval.zsApply ψ g = lam • NlsGge.Atomic.Interval.h1PairValue g) :
    ∃ hY : NlsGge.Atomic.Interval.h1PairValue g ∈
        recoveredActualSourceFreeWeightedDomain n,
      actualSourcePerturbedDiracPMapAfterAE n
        (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false)))
        ⟨NlsGge.Atomic.Interval.h1PairValue g, hY⟩ =
        (-lam) • NlsGge.Atomic.Interval.h1PairValue g := by
  classical
  let Fr : Bool → ℝ → ℂ := fun b =>
    Set.IccExtend zero_le_one (NlsGge.Atomic.LIB026.representative (g b))
  have hspec := fun b => NlsGge.Atomic.LIB026.representative_spec (g b)
  have hint : ∀ b, IntervalIntegrable (fun t => (g b).derivative t) volume 0 1 := fun b =>
    NlsGge.Atomic.LIB026.intervalIntegrable_L2 (g b).derivative
  have hF : ∀ b, sourceCoordinateComponent n (sourcePairRepr n (NlsGge.Atomic.Interval.h1PairValue g)) b
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] Fr b := by
    intro b
    rw [sourceCoordinateComponent_sourcePairRepr]
    exact (NlsGge.Atomic.LIB026.representative_ae (g b)).symm
  have hFtrace : ∀ b, Fr b 1 = spectralSign n * Fr b 0 := by
    intro b
    have h1 : Fr b 1 = NlsGge.Atomic.LIB026.traceRight (g b) := by
      simp only [Fr, NlsGge.Atomic.LIB026.traceRight]
      exact Set.IccExtend_of_mem zero_le_one _ ⟨zero_le_one, le_rfl⟩
    have h0 : Fr b 0 = NlsGge.Atomic.LIB026.traceLeft (g b) := by
      simp only [Fr, NlsGge.Atomic.LIB026.traceLeft]
      exact Set.IccExtend_of_mem zero_le_one _ ⟨le_rfl, zero_le_one⟩
    rw [h1, h0]
    exact hbc b
  have hx : sourcePairRepr n (NlsGge.Atomic.Interval.h1PairValue g) ∈ freeWeightedDomainPointwise n :=
    sourceFreeDomain_of_actualAC_components n (sourcePairRepr n (NlsGge.Atomic.Interval.h1PairValue g))
      (fun b => (g b).derivative) Fr (fun b t => (g b).derivative t)
      (fun b => (hspec b).1) hint (fun b => (hspec b).2) hF (fun b => Filter.EventuallyEq.rfl) hFtrace
  refine ⟨hx, ?_⟩
  let Y : recoveredActualSourceFreeWeightedDomain n := ⟨NlsGge.Atomic.Interval.h1PairValue g, hx⟩
  have hD : ∀ b, sourceFreeCoordinateDerivative n (sourcePairRepr n (NlsGge.Atomic.Interval.h1PairValue g)) hx b =
      (g b).derivative := by
    intro b
    exact sourceTwistedWeakDerivative_unique_derivative n _ _ _
      (sourceFreeDomain_has_twisted_weak_derivative n _ hx b)
      (sourceTwistedWeakDerivative_of_actualAC_representatives n _ ((g b).derivative) (Fr b)
        (fun t => (g b).derivative t) (hspec b).1 (hint b) (hspec b).2 (hF b)
        Filter.EventuallyEq.rfl (hFtrace b))
  apply PiLp.ext
  intro b
  apply Lp.ext
  have hz : NlsGge.Atomic.Interval.zsApply ψ g b = lam • (g b).value :=
    congrArg (fun P : SourcePairL2 => P b) heig
  have hDb : sourceFreeCoordinateDerivative n (sourcePairRepr n Y.val) Y.property b =
      (g b).derivative := hD b
  filter_upwards [action_component_ae ψ n Y b,
      Lp.coeFn_smul (-lam) (g b).value,
      NlsGge.Atomic.Interval.zsApply_ae ψ g b, Lp.coeFn_smul lam (g b).value,
      actualSourceGraphContinuousRepresentative_ae_source_class n Y (!b)] with t h1 h2 h3 h4 h5
  have h5' : actualSourceGraphContinuousRepresentative n Y (!b) t = (g (!b)).value t := h5
  have e1 : (NlsGge.Atomic.Interval.zsApply ψ g b : SourceIntervalL2) t =
      (lam • (g b).value : SourceIntervalL2) t := by rw [hz]
  rw [h3, h4] at e1
  rw [hDb, h5'] at h1
  change ((actualSourcePerturbedDiracPMapAfterAE n
      (-(unitPhysical (ψ true))) (-(unitPhysical (ψ false))) Y : SourcePairL2) b : SourceIntervalL2) t =
    (((-lam) • (g b).value : SourceIntervalL2) : ℝ → ℂ) t
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul] at e1 ⊢
  cases b
  · simp only [NlsGge.Atomic.Interval.zsExpression, Bool.false_eq_true, ite_false, Bool.not_false] at e1 ⊢
    linear_combination (-1 : ℂ) * e1
  · simp only [NlsGge.Atomic.Interval.zsExpression, ite_true, Bool.not_true] at e1 ⊢
    linear_combination (-1 : ℂ) * e1

/-! ### Sector separation: resonant vectors live in the sector of parity `n`. -/

theorem parity_proj_basis_zero (m : ℤ) (p : Fin 2) (hp : (p.val : ℤ) % 2 ≠ m % 2) :
    actualScalarParityProjectionLinearEquiv (spectralBasis m) p = 0 := by
  have hT := halfTranslation_basis m
  fin_cases p
  · have hm : m % 2 ≠ 0 := by
      intro h; apply hp; simpa using h.symm
    have hs : spectralSign m = -1 := by simp [spectralSign, hm]
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • (spectralBasis m + halfTranslation (spectralBasis m)) = (0 : SpectralScalarL2)
    rw [hT, hs]; module
  · have hm : m % 2 = 0 := by
      have : m % 2 ≠ 1 := by intro h; apply hp; simpa using h.symm
      omega
    have hs : spectralSign m = 1 := by simp [spectralSign, hm]
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • (spectralBasis m - halfTranslation (spectralBasis m)) = (0 : SpectralScalarL2)
    rw [hT, hs]; module

theorem assembly_resonant_zero (n : ℤ) (p : Fin 2) (hp : (p.val : ℤ) % 2 ≠ n % 2) :
    actualFullPeriodTwoSourceIntervalAssembly (NlsGge.Atomic.KST003.kstPnUpper n) p = 0 ∧
    actualFullPeriodTwoSourceIntervalAssembly (NlsGge.Atomic.KST003.kstPnLower n) p = 0 := by
  constructor
  · apply PiLp.ext
    intro b
    rw [actualFullPeriodTwoSourceIntervalAssembly_apply]
    cases b
    · have h0 : (NlsGge.Atomic.KST003.kstPnUpper n) false = 0 := by
        simp [NlsGge.Atomic.KST003.kstPnUpper]
      rw [h0, map_zero]; simp
    · have h1 : (NlsGge.Atomic.KST003.kstPnUpper n) true = spectralBasis (-n) := by
        simp [NlsGge.Atomic.KST003.kstPnUpper]
      rw [h1, parity_proj_basis_zero (-n) p (by intro h; apply hp; omega), map_zero]; simp
  · apply PiLp.ext
    intro b
    rw [actualFullPeriodTwoSourceIntervalAssembly_apply]
    cases b
    · have h1 : (NlsGge.Atomic.KST003.kstPnLower n) false = spectralBasis n := by
        simp [NlsGge.Atomic.KST003.kstPnLower]
      rw [h1, parity_proj_basis_zero n p hp, map_zero]; simp
    · have h0 : (NlsGge.Atomic.KST003.kstPnLower n) true = 0 := by
        simp [NlsGge.Atomic.KST003.kstPnLower]
      rw [h0, map_zero]; simp

/-- The parity sector index of `n`. -/
def parityIdx (n : ℤ) : Fin 2 := if n % 2 = 0 then 0 else 1

theorem parityIdx_mod (n : ℤ) : ((parityIdx n).val : ℤ) % 2 = n % 2 := by
  by_cases h : n % 2 = 0
  · simp [parityIdx, h]
  · have : n % 2 = 1 := by omega
    simp [parityIdx, this]

theorem spectralSign_parityIdx (n : ℤ) : spectralSign ((parityIdx n).val : ℤ) = spectralSign n := by
  unfold spectralSign
  rw [parityIdx_mod]

theorem resonant_proj_eq (n : ℤ) (p0 : Fin 2) (hp0 : (p0.val : ℤ) % 2 = n % 2)
    (f f' : NlsGge.Atomic.KST003.KSTPairL2)
    (h : actualFullPeriodTwoSourceIntervalAssembly f p0 =
      actualFullPeriodTwoSourceIntervalAssembly f' p0) :
    NlsGge.Atomic.KST003.spectralPn n f = NlsGge.Atomic.KST003.spectralPn n f' := by
  have key : ∀ e : NlsGge.Atomic.KST003.KSTPairL2,
      (∀ p : Fin 2, (p.val : ℤ) % 2 ≠ n % 2 → actualFullPeriodTwoSourceIntervalAssembly e p = 0) →
      inner ℂ e f = inner ℂ e f' := by
    intro e he
    rw [← sub_eq_zero, ← inner_sub_right,
      ← actualFullPeriodTwoSourceIntervalAssembly.inner_map_map, PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : (q.val : ℤ) % 2 = n % 2
    · have hqp : q = p0 := Fin.ext (by have := q.isLt; have := p0.isLt; omega)
      subst hqp
      simp [map_sub, h]
    · rw [he q hq]; simp
  rw [NlsGge.Atomic.KST003.spectralPn_apply, NlsGge.Atomic.KST003.spectralPn_apply,
    key _ (fun p hp => (assembly_resonant_zero n p hp).1),
    key _ (fun p hp => (assembly_resonant_zero n p hp).2)]

/-- An eigenvector of `dirac φ`, whose eigenspace is injected by `P_n` (KST013 uniqueness clause),
lies in the sector of parity `n`: all opposite-parity sector components vanish. -/
theorem eigen_in_sector (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (lam : ℂ) (n : ℤ)
    (huniq : ∀ f₁ f₂ : (NlsGge.Atomic.KST013.dirac φ).domain,
      NlsGge.Atomic.KST013.dirac φ f₁ = lam • (f₁ : NlsGge.Atomic.KST003.KSTPairL2) →
      NlsGge.Atomic.KST013.dirac φ f₂ = lam • (f₂ : NlsGge.Atomic.KST003.KSTPairL2) →
      NlsGge.Atomic.KST003.spectralPn n (f₁ : NlsGge.Atomic.KST003.KSTPairL2) =
        NlsGge.Atomic.KST003.spectralPn n (f₂ : NlsGge.Atomic.KST003.KSTPairL2) →
      (f₁ : NlsGge.Atomic.KST003.KSTPairL2) = (f₂ : NlsGge.Atomic.KST003.KSTPairL2))
    (f : (NlsGge.Atomic.KST013.dirac φ).domain)
    (hf : NlsGge.Atomic.KST013.dirac φ f = lam • (f : NlsGge.Atomic.KST003.KSTPairL2))
    (q : Fin 2) (hq : (q.val : ℤ) % 2 ≠ n % 2) :
    actualFullPeriodTwoSourceIntervalAssembly (f : NlsGge.Atomic.KST003.KSTPairL2) q = 0 := by
  have hp0 := parityIdx_mod n
  have hY := eigen_sector_component φ lam f hf (parityIdx n)
  obtain ⟨f', hf'a, hf'e⟩ := sector_lift φ (parityIdx n) lam _ hY
  have hproj : NlsGge.Atomic.KST003.spectralPn n (f : NlsGge.Atomic.KST003.KSTPairL2) =
      NlsGge.Atomic.KST003.spectralPn n (f' : NlsGge.Atomic.KST003.KSTPairL2) :=
    resonant_proj_eq n (parityIdx n) hp0 _ _ (by rw [hf'a]; simp [sectorVec])
  have heq := huniq f f' hf hf'e hproj
  have hq0 : q ≠ parityIdx n := by intro h; subst h; exact hq hp0
  have := congrArg (fun x => actualFullPeriodTwoSourceIntervalAssembly x q) heq
  simp only [hf'a, sectorVec, hq0, ↓reduceIte] at this
  exact this

/-! ### Unit interval ZS eigenpairs versus `piDirac` eigenvectors. -/

theorem unit_to_pi (v : PiPairL2) (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition) (c : ℂ)
    (g : NlsGge.Atomic.Interval.H1Pair)
    (hbc : NlsGge.Atomic.Interval.HasZSBoundaryCondition bc g)
    (hg0 : NlsGge.Atomic.Interval.h1PairValue g ≠ 0)
    (heig : NlsGge.Atomic.Interval.zsApply (scaledPotential v) g =
      ((Real.pi : ℂ) * c) • NlsGge.Atomic.Interval.h1PairValue g) :
    ∃ f : (piDirac v bc).domain, (f : PiPairL2) ≠ 0 ∧ piDirac v bc f = c • (f : PiPairL2) := by
  have hres : rescaleH1Pair (inverseRescaleH1Pair g) = g := by
    funext b
    exact rescale_inverseRescaleH1 (g b)
  have hfb : piBoundary bc (inverseRescaleH1Pair g) := by
    unfold piBoundary
    rw [hres]
    exact hbc
  obtain ⟨hx, hact⟩ := piDirac_literal v bc (inverseRescaleH1Pair g) hfb
  have h3 : NlsGge.Atomic.Interval.h1PairValue g =
      unitaryRescalePair (piH1Value (inverseRescaleH1Pair g)) := by
    have h := h1PairValue_rescale (inverseRescaleH1Pair g)
    rw [hres] at h
    exact h
  refine ⟨⟨piH1Value (inverseRescaleH1Pair g), hx⟩, ?_, ?_⟩
  · intro h0
    apply hg0
    rw [h3]
    have h0' : piH1Value (inverseRescaleH1Pair g) = 0 := h0
    rw [h0', map_zero]
  · change piDirac v bc ⟨piH1Value (inverseRescaleH1Pair g), hx⟩ = c • piH1Value (inverseRescaleH1Pair g)
    rw [hact]
    have h1 := dirac_period_rescaling v (inverseRescaleH1Pair g)
    rw [hres, heig, h3] at h1
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) • unitaryRescalePair (piZSApply v (inverseRescaleH1Pair g)) =
        (Real.pi : ℂ) • unitaryRescalePair (c • piH1Value (inverseRescaleH1Pair g)) := by
      rw [← h1, map_smul, smul_smul]
    exact unitaryRescalePair.injective (smul_right_injective _ hπ h2)

theorem pi_to_unit (v : PiPairL2) (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition) (c : ℂ)
    (f : (piDirac v bc).domain) (hf0 : (f : PiPairL2) ≠ 0)
    (hf : piDirac v bc f = c • (f : PiPairL2)) :
    ∃ g : NlsGge.Atomic.Interval.H1Pair, NlsGge.Atomic.Interval.HasZSBoundaryCondition bc g ∧
      NlsGge.Atomic.Interval.h1PairValue g ≠ 0 ∧
      NlsGge.Atomic.Interval.zsApply (scaledPotential v) g =
        ((Real.pi : ℂ) * c) • NlsGge.Atomic.Interval.h1PairValue g := by
  obtain ⟨f', hb, hval⟩ := (piDomain_literal bc (f : PiPairL2)).mp f.property
  obtain ⟨hx, hact⟩ := piDirac_literal v bc f' hb
  have hfeq : (⟨piH1Value f', hx⟩ : (piDirac v bc).domain) = f := Subtype.ext hval
  have hz : piZSApply v f' = c • (f : PiPairL2) := by
    rw [← hact, hfeq]; exact hf
  refine ⟨rescaleH1Pair f', hb, ?_, ?_⟩
  · rw [h1PairValue_rescale, hval]
    intro h0
    apply hf0
    exact unitaryRescalePair.injective (by rw [h0, map_zero])
  · rw [dirac_period_rescaling, hz, map_smul, h1PairValue_rescale, hval, smul_smul]

theorem boundary_iff_twist (n : ℤ) (g : NlsGge.Atomic.Interval.H1Pair) :
    NlsGge.Atomic.Interval.HasZSBoundaryCondition (labelBoundary n) g ↔
      ∀ b, NlsGge.Atomic.LIB026.traceRight (g b) =
        spectralSign n * NlsGge.Atomic.LIB026.traceLeft (g b) := by
  unfold labelBoundary spectralSign
  split_ifs with h
  · change (∀ b, NlsGge.Atomic.LIB026.traceRight (g b) = NlsGge.Atomic.LIB026.traceLeft (g b)) ↔ _
    simp
  · change (∀ b, NlsGge.Atomic.LIB026.traceRight (g b) = -NlsGge.Atomic.LIB026.traceLeft (g b)) ↔ _
    simp

theorem exists_sector_of_sign (s : ℂ) (hs : s * s = 1) :
    ∃ p : Fin 2, spectralSign (p.val : ℤ) = s := by
  rcases mul_self_eq_one_iff.mp hs with rfl | rfl
  · exact ⟨0, by simp [spectralSign]⟩
  · exact ⟨1, by simp [spectralSign]⟩

theorem sector_ne_zero_of_eigen (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (lam : ℂ) (n : ℤ)
    (huniq : ∀ f₁ f₂ : (NlsGge.Atomic.KST013.dirac φ).domain,
      NlsGge.Atomic.KST013.dirac φ f₁ = lam • (f₁ : NlsGge.Atomic.KST003.KSTPairL2) →
      NlsGge.Atomic.KST013.dirac φ f₂ = lam • (f₂ : NlsGge.Atomic.KST003.KSTPairL2) →
      NlsGge.Atomic.KST003.spectralPn n (f₁ : NlsGge.Atomic.KST003.KSTPairL2) =
        NlsGge.Atomic.KST003.spectralPn n (f₂ : NlsGge.Atomic.KST003.KSTPairL2) →
      (f₁ : NlsGge.Atomic.KST003.KSTPairL2) = (f₂ : NlsGge.Atomic.KST003.KSTPairL2))
    (f : (NlsGge.Atomic.KST013.dirac φ).domain)
    (hf0 : (f : NlsGge.Atomic.KST003.KSTPairL2) ≠ 0)
    (hf : NlsGge.Atomic.KST013.dirac φ f = lam • (f : NlsGge.Atomic.KST003.KSTPairL2)) :
    actualFullPeriodTwoSourceIntervalAssembly (f : NlsGge.Atomic.KST003.KSTPairL2) (parityIdx n) ≠ 0 := by
  intro h0
  apply hf0
  apply actualFullPeriodTwoSourceIntervalAssembly.injective
  rw [map_zero]
  apply PiLp.ext
  intro q
  by_cases hq : q = parityIdx n
  · subst hq; exact h0
  · have hpar : (q.val : ℤ) % 2 ≠ n % 2 := by
      rw [← parityIdx_mod n]
      intro h; apply hq
      exact Fin.ext (by have := q.isLt; have := (parityIdx n).isLt; omega)
    have h := eigen_in_sector φ lam n huniq f hf q hpar
    rw [h]; rfl

end
end NlsGge.ThirdConsultation.DM.BridgeB

/-! ### Public bridge statements S4 (both directions) and S5.

Eigenvalue relation: `dirac (dmKstPotential v)` is the unit-interval operator (spectral parameter
`λ = dmSpectralPoint n z = π (n + z)`), while `piDirac v (labelBoundary n) = π⁻¹ • (rescaled unit operator)`
has the eigenvalue `n + z`.  Parity: sector `parityIdx n = n % 2`, i.e. boundary `labelBoundary n`. -/

namespace NlsGge.ThirdConsultation.DM
noncomputable section
open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST013
open NlsGge.ThirdConsultation.DM.BridgeB

/-- S4, direction `piDirac -> KST` (no cutoff, any `n`, any `z`): an eigenvector of the period-`π` operator with the
label boundary condition is extended to the doubled circle, in the sector of parity `n`, as an eigenvector of the
original-sign operator `dirac (dmKstPotential v)` at `π (n + z)`. -/
theorem dm_bridgeB_pi_to_kst (v : PiPairL2) (n : ℤ) (z : ℂ)
    (h : ∃ g : (piDirac v (labelBoundary n)).domain, (g : PiPairL2) ≠ 0 ∧
      piDirac v (labelBoundary n) g = ((n : ℂ) + z) • (g : PiPairL2)) :
    ∃ f : (dirac (dmKstPotential v)).domain, (f : KSTPairL2) ≠ 0 ∧
      dirac (dmKstPotential v) f = dmSpectralPoint n z • (f : KSTPairL2) := by
  obtain ⟨g0, hg0, hg0e⟩ := h
  obtain ⟨g, hbc, hgne, hgeig⟩ := pi_to_unit v (labelBoundary n) ((n : ℂ) + z) g0 hg0 hg0e
  have htw : ∀ b, NlsGge.Atomic.LIB026.traceRight (g b) =
      NlsGge.Schur.spectralSign ((parityIdx n).val : ℤ) * NlsGge.Atomic.LIB026.traceLeft (g b) := by
    rw [spectralSign_parityIdx]
    exact (boundary_iff_twist n g).mp hbc
  obtain ⟨hY, hYe⟩ := h1_to_sector_eigen (scaledPotential v) ((parityIdx n).val : ℤ) (dmSpectralPoint n z)
    g htw hgeig
  obtain ⟨f, hfa, hfe⟩ := sector_lift (dmKstPotential v) (parityIdx n) (dmSpectralPoint n z)
    ⟨NlsGge.Atomic.Interval.h1PairValue g, hY⟩ hYe
  refine ⟨f, ?_, hfe⟩
  intro hf0
  apply hgne
  have h1 := congrArg (fun x => (NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly x) (parityIdx n)) hf0
  simp only [hfa, sectorVec, map_zero, ↓reduceIte] at h1
  exact h1

/-- S4, direction `KST -> piDirac` (large `|n|`, `‖z‖ ≤ 1/4`): a nonzero eigenvector of `dirac (dmKstPotential v)` at
`π (n + z)` is forced into the sector of parity `n` by the KST013 uniqueness clause, and its sector component is a
nonzero eigenvector of `piDirac v (labelBoundary n)` at `n + z`. -/
theorem dm_bridgeB_kst_to_pi (v : PiPairL2) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z : ℂ, ‖z‖ ≤ (1/4 : ℝ) →
        (∃ f : (dirac (dmKstPotential v)).domain, (f : KSTPairL2) ≠ 0 ∧
          dirac (dmKstPotential v) f = dmSpectralPoint n z • (f : KSTPairL2)) →
        ∃ g : (piDirac v (labelBoundary n)).domain, (g : PiPairL2) ≠ 0 ∧
          piDirac v (labelBoundary n) g = ((n : ℂ) + z) • (g : PiPairL2) := by
  obtain ⟨N₀, h5, hN⟩ := dirac_eigen_iff_reduced_kernel (dmKstPotential v)
  refine ⟨N₀, h5, ?_⟩
  rintro n hn z hz ⟨f, hf0, hf⟩
  have hstrip : dmSpectralPoint n z ∈ NlsGge.Atomic.KST004.spectralStrip n := by
    show |(dmSpectralPoint n z).re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
    have hre : (dmSpectralPoint n z).re - (n : ℝ) * Real.pi = Real.pi * z.re := by
      simp [dmSpectralPoint, Complex.mul_re]
      ring
    rw [hre, abs_mul, abs_of_pos Real.pi_pos]
    have hzre := Complex.abs_re_le_norm z
    nlinarith [Real.pi_pos]
  have huniq := (hN n hn _ hstrip).2
  have hY := eigen_sector_component (dmKstPotential v) (dmSpectralPoint n z) f hf (parityIdx n)
  obtain ⟨g, hgY, hbc, heig⟩ := sector_eigen_to_h1 (scaledPotential v) ((parityIdx n).val : ℤ)
    (dmSpectralPoint n z) ⟨NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly (f : KSTPairL2) (parityIdx n),
      f.property (parityIdx n)⟩ hY
  have hne : NlsGge.Atomic.Interval.h1PairValue g ≠ 0 := by
    rw [hgY]
    exact sector_ne_zero_of_eigen (dmKstPotential v) (dmSpectralPoint n z) n huniq f hf0 hf
  have hbc' : NlsGge.Atomic.Interval.HasZSBoundaryCondition (labelBoundary n) g := by
    apply (boundary_iff_twist n g).mpr
    rw [← spectralSign_parityIdx]
    exact hbc
  exact unit_to_pi v (labelBoundary n) ((n : ℂ) + z) g hbc' hne heig

/-- S4 combined: for `|n| ≥ N₀`, `‖z‖ ≤ 1/4`, eigenvectors of the two operators correspond. -/
theorem dm_bridgeB_eigen_iff (v : PiPairL2) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z : ℂ, ‖z‖ ≤ (1/4 : ℝ) →
        ((∃ f : (dirac (dmKstPotential v)).domain, (f : KSTPairL2) ≠ 0 ∧
            dirac (dmKstPotential v) f = dmSpectralPoint n z • (f : KSTPairL2)) ↔
          ∃ g : (piDirac v (labelBoundary n)).domain, (g : PiPairL2) ≠ 0 ∧
            piDirac v (labelBoundary n) g = ((n : ℂ) + z) • (g : PiPairL2)) := by
  obtain ⟨N₀, h5, hN⟩ := dm_bridgeB_kst_to_pi v
  exact ⟨N₀, h5, fun n hn z hz => ⟨hN n hn z hz, dm_bridgeB_pi_to_kst v n z⟩⟩



/-- S5: a zero of the periodic characteristic in the `1/8`-disc about the large integer `n` gives a nonzero
eigenvector of `piDirac v (labelBoundary n)` (in the parity sector of `n`, not merely of some boundary condition). -/
theorem dm_bridgeB_perChar_zero_eigenvector (v : PiPairL2) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs → ∀ lam : ℂ, lam ∈ Metric.ball (n : ℂ) (1/8 : ℝ) →
        dmPeriodicCharacteristic v lam = 0 →
        ∃ g : (piDirac v (labelBoundary n)).domain, (g : PiPairL2) ≠ 0 ∧
          piDirac v (labelBoundary n) g = lam • (g : PiPairL2) := by
  obtain ⟨N₀, h5, hN⟩ := dirac_eigen_iff_reduced_kernel (dmKstPotential v)
  refine ⟨N₀, h5, ?_⟩
  intro n hn lam hlam hzero
  set z : ℂ := lam - (n : ℂ) with hzdef
  have hz8 : ‖z‖ < (1/8 : ℝ) := by
    have := Metric.mem_ball.mp hlam
    rwa [dist_eq_norm, ← hzdef] at this
  have hlz : lam = (n : ℂ) + z := by rw [hzdef]; ring
  have hstrip : dmSpectralPoint n z ∈ NlsGge.Atomic.KST004.spectralStrip n := by
    show |(dmSpectralPoint n z).re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
    have hre : (dmSpectralPoint n z).re - (n : ℝ) * Real.pi = Real.pi * z.re := by
      simp [dmSpectralPoint, Complex.mul_re]
      ring
    rw [hre, abs_mul, abs_of_pos Real.pi_pos]
    have hzre := Complex.abs_re_le_norm z
    nlinarith [Real.pi_pos]
  have huniq := (hN n hn _ hstrip).2
  have h' : NlsGge.GK38.perChar
      (unitPhysical (scaledPotential v true), unitPhysical (scaledPotential v false))
      ((Real.pi : ℂ) * lam) = 0 := hzero
  obtain ⟨s, hs, g, hg0, hgb, hgeig⟩ :=
    NlsGge.ThirdConsultation.DM.Support016.exists_eigenpair_of_perChar_zero
      (scaledPotential v) ((Real.pi : ℂ) * lam) h'
  obtain ⟨p, hps⟩ := exists_sector_of_sign s hs
  have htw : ∀ b, NlsGge.Atomic.LIB026.traceRight (g b) =
      NlsGge.Schur.spectralSign (p.val : ℤ) * NlsGge.Atomic.LIB026.traceLeft (g b) := by
    intro b; rw [hps]; exact hgb b
  have hgeig' : NlsGge.Atomic.Interval.zsApply (scaledPotential v) g =
      dmSpectralPoint n z • NlsGge.Atomic.Interval.h1PairValue g := by
    rw [hgeig, hlz]; rfl
  obtain ⟨hY, hYe⟩ := h1_to_sector_eigen (scaledPotential v) (p.val : ℤ) (dmSpectralPoint n z) g htw hgeig'
  obtain ⟨f, hfa, hfe⟩ := sector_lift (dmKstPotential v) p (dmSpectralPoint n z)
    ⟨NlsGge.Atomic.Interval.h1PairValue g, hY⟩ hYe
  have hf0 : (f : KSTPairL2) ≠ 0 := by
    intro hf0
    apply hg0
    have h1 := congrArg (fun x => (NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly x) p) hf0
    simp only [hfa, sectorVec, map_zero, ↓reduceIte] at h1
    exact h1
  have hpar : (p.val : ℤ) % 2 = n % 2 := by
    by_contra hne
    have h0 := eigen_in_sector (dmKstPotential v) (dmSpectralPoint n z) n huniq f hfe p hne
    apply hg0
    have h1 : NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly (f : KSTPairL2) p =
        NlsGge.Atomic.Interval.h1PairValue g := by
      simp only [hfa, sectorVec, ↓reduceIte]
    rw [← h1]
    exact h0
  have hsign : NlsGge.Schur.spectralSign (p.val : ℤ) = NlsGge.Schur.spectralSign n := (NlsGge.Schur.spectralSign_eq_iff _ _).mpr hpar
  have hbc : NlsGge.Atomic.Interval.HasZSBoundaryCondition (labelBoundary n) g := by
    apply (boundary_iff_twist n g).mpr
    rw [← hsign]
    exact htw
  have hgeig'' : NlsGge.Atomic.Interval.zsApply (scaledPotential v) g =
      ((Real.pi : ℂ) * lam) • NlsGge.Atomic.Interval.h1PairValue g := hgeig
  exact unit_to_pi v (labelBoundary n) lam g hbc hg0 hgeig''

/-- S5 in the `z`-form used by the labelled-endpoint theorem: `z = zMinus/zPlus` with `‖z‖ < 1/8`. -/
theorem dm_bridgeB_perChar_zero_eigenvector_z (v : PiPairL2) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z : ℂ, ‖z‖ < (1/8 : ℝ) →
        dmPeriodicCharacteristic v ((n : ℂ) + z) = 0 →
        ∃ g : (piDirac v (labelBoundary n)).domain, (g : PiPairL2) ≠ 0 ∧
          piDirac v (labelBoundary n) g = ((n : ℂ) + z) • (g : PiPairL2) := by
  obtain ⟨N₀, h5, hN⟩ := dm_bridgeB_perChar_zero_eigenvector v
  refine ⟨N₀, h5, fun n hn z hz h => hN n hn _ ?_ h⟩
  rw [Metric.mem_ball, dist_eq_norm]
  simpa using hz

end
end NlsGge.ThirdConsultation.DM
