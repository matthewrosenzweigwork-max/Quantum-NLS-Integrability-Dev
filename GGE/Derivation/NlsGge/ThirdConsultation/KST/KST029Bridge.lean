/- KST029Bridge PRODUCTION01 (proof development, author; not self-reviewed).  Supporting module.
   Target NlsGge/ThirdConsultation/KST/KST029Bridge.lean.  Exports
   `NlsGge.ThirdConsultation.KST.operatorPerCharBridge : OperatorPerCharBridge`
   (statement from KST029Support, hosted by proof development's KST029SUP02, unchanged).
   Route: KST029_BRIDGE_ROUTE.md. -/
import Mathlib
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.Atomic.M.M024Local
import NlsGge.Atomic.M.M025
import NlsGge.ThirdConsultation.DM.DMBridgeB
import NlsGge.Atomic.DM.DM016Eig
import NlsGge.Atomic.G1.G1104

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.ThirdConsultation.KST.KST029Bridge

open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.MTwoMode
open NlsGge.GKDefinitionDesign
open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002
open NlsGge.ThirdConsultation.DM.BridgeB
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open NlsGge.Atomic.Interval
open NlsGge.Atomic.KST002 NlsGge.Atomic.LIB033 NlsGge.Schur NlsGge.Atomic.KST016

/-! ### P0: `unitPhysical (sourceIntervalClass p) = p` -/

/-- Two physical `L2` classes whose real-line representatives agree a.e. on `(0,1]` are equal
(Fourier coefficients are determined by the unit-interval integral). -/
theorem physical_ext_of_ae_unit (u v : PhysicalL2)
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      u ((t : ℝ) : PhysicalCircle) = v ((t : ℝ) : PhysicalCircle)) : u = v := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext k
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  unfold physicalFourier
  rw [fourierCoeff_eq_intervalIntegral (u : PhysicalCircle → ℂ) k 0,
    fourierCoeff_eq_intervalIntegral (v : PhysicalCircle → ℂ) k 0]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have h' := (ae_restrict_iff' measurableSet_Ioc).1 h
  filter_upwards [h'] with t ht hmem
  have hmem' : t ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [zero_add, Set.uIoc_of_le zero_le_one] at hmem
    exact hmem
  rw [ht hmem']

theorem unitPhysical_sourceIntervalClass (p : PhysicalL2) :
    unitPhysical (sourceIntervalClass p) = p := by
  apply physical_ext_of_ae_unit
  have h1 := unitPhysical_interval_ae (sourceIntervalClass p)
  have h2 := (NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec p).2
  have h3 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), coverRep38 p t = p ((t : ℝ) : PhysicalCircle) :=
    ae_restrict_of_ae (coverRep38_ae_phys p)
  filter_upwards [h1, h2, h3] with t e1 e2 e3
  exact e1.trans (e2.trans e3)

/-! ### P1: `schurPhysicalPair (periodicPair φ) = φ` and the determinant identity -/

theorem schurPhysicalPair_periodicPair (φ : PhysicalPairLp) :
    schurPhysicalPair (periodicPair φ) = φ := by
  apply PiLp.ext
  intro b
  cases b <;> rfl

theorem det_schur_eq (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hsm : ‖ambientT (periodicPair φ) n z hz ^ 2‖ ≤ (1 / 2 : ℝ)) :
    determinant n (a φ n) (b φ n) (c φ n) z =
      Matrix.det (schurMatrix (periodicPair φ) n z hz) := by
  have hP := schurPhysicalPair_periodicPair φ
  have hdiag := NlsGge.ThirdConsultation.M.schur_diagonals_equal (periodicPair φ) n z hz hsm
  have habc := abc_eq_reduced φ n z hz
  have ha : a φ n z = reducedA φ n z hz := congrArg Prod.fst habc
  have hb : b φ n z = reducedB φ n z hz := congrArg (fun t => t.2.1) habc
  have hc : c φ n z = reducedC φ n z hz := congrArg (fun t => t.2.2) habc
  have hE : ∀ i j, schurEntry (periodicPair φ) n z hz i j = entry φ n z hz i j := by
    intro i j
    unfold schurEntry entry
    rw [hP]
    rfl
  have hEq : entry φ n z hz false false = entry φ n z hz true true := by
    unfold schurDiagonalPlus schurDiagonalMinus at hdiag
    rw [hE, hE] at hdiag
    linear_combination -hdiag
  unfold determinant
  rw [ha, hb, hc]
  simp only [reducedA, reducedB, reducedC, center, schurMatrix, Matrix.det_fin_two_of,
    schurDiagonalPlus, schurDiagonalMinus, offDiagonal, hE, ↓reduceIte, Bool.false_eq_true]
  rw [← hEq]
  ring

/-! ### P2: a nonzero eigenvector of `dirac` gives `det schurMatrix = 0` (small square) -/

theorem eigen_to_det (P : PotPair) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hsmall : ‖ambientT P n z hz ^ 2‖ ≤ (1 / 2 : ℝ))
    (F : (NlsGge.Atomic.KST013.dirac (schurPhysicalPair P)).domain)
    (hFne : (F : KSTPairL2) ≠ 0)
    (heq : NlsGge.Atomic.KST013.dirac (schurPhysicalPair P) F = z • (F : KSTPairL2)) :
    Matrix.det (schurMatrix P n z hz) = 0 := by
  have hT := NlsGge.ThirdConsultation.MTwoModeSupp.sq_norm_lt_one P n z hz hsmall
  have hT' : ‖NlsGge.Atomic.KST006.qOperator (schurPhysicalPair P) n z hz ^ 2‖ < 1 := hT
  obtain ⟨hunit, _, _, _⟩ := NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt
    (NlsGge.Atomic.KST006.qOperator (schurPhysicalPair P) n z hz) hT'
  have hdirac : NlsGge.Atomic.KST013.dirac (schurPhysicalPair P) F =
      -actualFullPeriodTwoDoubledCirclePerturbedDiracAction
        (-(schurPhysicalPair P true)) (-(schurPhysicalPair P false))
        ⟨(F : KSTPairL2), F.property⟩ := rfl
  have hact : actualFullPeriodTwoDoubledCirclePerturbedDiracAction
      (-(schurPhysicalPair P true)) (-(schurPhysicalPair P false))
      ⟨(F : KSTPairL2), F.property⟩ = -(z • (F : KSTPairL2)) := by
    rw [hdirac] at heq
    exact neg_eq_iff_eq_neg.mp heq
  obtain ⟨g, hgraph, hprod⟩ :=
    (NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff (schurPhysicalPair P)
      (F : KSTPairL2) (z • (F : KSTPairL2))).2 ⟨F.property, hact⟩
  have hpne : spectralPn n (F : KSTPairL2) ≠ 0 := fun h0 =>
    hFne (NlsGge.Atomic.KST013.stage13G_projection_zero_forces_zero (schurPhysicalPair P) n z hz
      (F : KSTPairL2) g hgraph hprod hunit h0)
  have hi : spectralPn n (spectralPn n (F : KSTPairL2)) = spectralPn n (F : KSTPairL2) := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (F : KSTPairL2))
      (spectralPn_idempotent n)
    simpa only [ContinuousLinearMap.comp_apply] using hi
  exact (NlsGge.ThirdConsultation.MTwoModeSupp.kernel_iff_det P n z hz).1
    ((NlsGge.ThirdConsultation.MTwoModeSupp.raw_iff_kernel (schurPhysicalPair P) n z hz).1
      ⟨spectralPn n (F : KSTPairL2), hpne, hi,
        NlsGge.Atomic.KST013.stage13K_actual_forward_reduced_formula (schurPhysicalPair P) n z hz
          (F : KSTPairL2) g hgraph hprod hunit⟩)

/-! ### P3: eigenvectors of `dirac φ` versus zeros of the periodic characteristic -/

/-- Eigenvalue statement for the original-sign Dirac operator on the doubled circle. -/
def DiracEigen (φ : PhysicalPairLp) (z : ℂ) : Prop :=
  ∃ F : (NlsGge.Atomic.KST013.dirac φ).domain, (F : KSTPairL2) ≠ 0 ∧
    NlsGge.Atomic.KST013.dirac φ F = z • (F : KSTPairL2)

theorem diracEigen_congr {X Y : PhysicalPairLp} (h : X = Y) (z : ℂ) :
    DiracEigen X z ↔ DiracEigen Y z := by
  subst h
  exact Iff.rfl

/-- The unit-interval potential carrying the physical pair `φ`. -/
def unitPot (φ : PhysicalPairLp) : SourcePairL2 := intervalPotential (periodicPair φ)

theorem unitPot_spec (φ : PhysicalPairLp) (b : Bool) :
    unitPhysical (unitPot φ b) = φ b := by
  cases b
  · exact unitPhysical_sourceIntervalClass (φ false)
  · exact unitPhysical_sourceIntervalClass (φ true)

theorem perChar_to_diracEigen (φ : PhysicalPairLp) (z : ℂ)
    (hz : perChar (periodicPair φ) z = 0) : DiracEigen φ z := by
  have hu1 := unitPot_spec φ true
  have hu2 := unitPot_spec φ false
  have hz0 : perChar (unitPhysical (unitPot φ true), unitPhysical (unitPot φ false)) z = 0 := by
    rw [hu1, hu2]
    exact hz
  obtain ⟨s, hs, g, hg0, hgb, hgeig⟩ :=
    NlsGge.ThirdConsultation.DM.Support016.exists_eigenpair_of_perChar_zero (unitPot φ) z hz0
  obtain ⟨p, hps⟩ := exists_sector_of_sign s hs
  have htw : ∀ b, NlsGge.Atomic.LIB026.traceRight (g b) =
      NlsGge.Schur.spectralSign (p.val : ℤ) * NlsGge.Atomic.LIB026.traceLeft (g b) := by
    intro b
    rw [hps]
    exact hgb b
  obtain ⟨hY, hYe⟩ := h1_to_sector_eigen (unitPot φ) (p.val : ℤ) z g htw hgeig
  rw [hu1, hu2] at hYe
  obtain ⟨f, hfa, hfe⟩ := sector_lift φ p z ⟨h1PairValue g, hY⟩ hYe
  refine ⟨f, ?_, hfe⟩
  intro hf0
  apply hg0
  have h1 := congrArg
    (fun x => (NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly x) p) hf0
  simp only [hfa, sectorVec, map_zero, ↓reduceIte] at h1
  exact h1

/-- A nonzero `H1` eigenpair of the unit-interval ZS expression with periodic or antiperiodic
boundary condition forces a zero of the periodic characteristic (G1-104, clause 2). -/
theorem perChar_zero_of_h1_eigen (P : PotPair) (bc : ZSBoundaryCondition)
    (hbc : bc = ZSBoundaryCondition.periodic ∨ bc = ZSBoundaryCondition.antiperiodic)
    (z : ℂ) (g : H1Pair) (hg : HasZSBoundaryCondition bc g) (hg0 : h1PairValue g ≠ 0)
    (heig : zsApply (intervalPotential P) g = z • h1PairValue g) : perChar P z = 0 := by
  classical
  by_contra hne
  have hcore := NlsGge.Atomic.G1104.core P
  have hfd := (hcore.1 bc z).1
  have hmem : h1PairValue g ∈ (zsRealization (intervalPotential P) bc).domain := ⟨g, hg, rfl⟩
  have hroot : rootVector (zsRealization (intervalPotential P) bc) z (h1PairValue g) := by
    refine ⟨1, fun j => if j = 0 then h1PairValue g else 0, if_pos rfl, if_neg one_ne_zero, ?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    refine ⟨hmem, ?_⟩
    show (zsRealization (intervalPotential P) bc) ⟨h1PairValue g, hmem⟩ - z • h1PairValue g = 0
    rw [zsRealization_apply (intervalPotential P) bc g hg, heig, sub_self]
  have hspan : h1PairValue g ∈ NlsGge.GKDefinitionDesign.rootSpace (zsRealization (intervalPotential P) bc) z :=
    Submodule.subset_span hroot
  haveI := hfd
  have hpos : 0 < algebraicMultiplicity (zsRealization (intervalPotential P) bc) z := by
    unfold algebraicMultiplicity
    exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨h1PairValue g, hspan⟩, fun h => hg0 (by
      simpa using congrArg Subtype.val h)⟩
  have hord : analyticOrderAt (perChar P) z = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr hne)
  have hsum := (hcore.2 z)
  rw [hord] at hsum
  have hzero : algebraicMultiplicity (zsRealization (intervalPotential P) .periodic) z +
      algebraicMultiplicity (zsRealization (intervalPotential P) .antiperiodic) z = 0 := by
    exact_mod_cast hsum
  rcases hbc with rfl | rfl <;> omega

theorem diracEigen_to_perChar (φ : PhysicalPairLp) (z : ℂ) (h : DiracEigen φ z) :
    perChar (periodicPair φ) z = 0 := by
  obtain ⟨f, hf0, hf⟩ := h
  have hu1 := unitPot_spec φ true
  have hu2 := unitPot_spec φ false
  obtain ⟨q, hq⟩ : ∃ q : Fin 2,
      NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly (f : KSTPairL2) q ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hf0
    apply NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly.injective
    rw [map_zero]
    apply PiLp.ext
    intro q
    exact hall q
  have hY := eigen_sector_component φ z f hf q
  rw [← hu1, ← hu2] at hY
  obtain ⟨g, hgY, hbc, heig⟩ := sector_eigen_to_h1 (unitPot φ) (q.val : ℤ) z
    ⟨NlsGge.Schur.actualFullPeriodTwoSourceIntervalAssembly (f : KSTPairL2) q, f.property q⟩ hY
  have hg0 : h1PairValue g ≠ 0 := by
    rw [hgY]
    exact hq
  have hbc' : HasZSBoundaryCondition (labelBoundary (q.val : ℤ)) g :=
    (boundary_iff_twist (q.val : ℤ) g).2 hbc
  refine perChar_zero_of_h1_eigen (periodicPair φ) (labelBoundary (q.val : ℤ)) ?_ z g hbc' hg0 heig
  unfold labelBoundary
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem diracEigen_iff_perChar (φ : PhysicalPairLp) (z : ℂ) :
    DiracEigen φ z ↔ perChar (periodicPair φ) z = 0 :=
  ⟨diracEigen_to_perChar φ z, perChar_to_diracEigen φ z⟩

end NlsGge.ThirdConsultation.KST.KST029Bridge

namespace NlsGge.ThirdConsultation.KST

open NlsGge.ThirdConsultation.KST.KST029Bridge NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.ThirdConsultation.MTwoMode

theorem operatorPerCharBridge : OperatorPerCharBridge := by
  intro φ n z hz hsmall
  have hP := schurPhysicalPair_periodicPair φ
  have hamb : ambientT (periodicPair φ) n z hz = qOperator φ n z hz := by
    unfold ambientT
    rw [hP]
  have hsm : ‖ambientT (periodicPair φ) n z hz ^ 2‖ ≤ (1 / 2 : ℝ) := by
    rw [hamb]
    exact hsmall
  rw [det_schur_eq φ n z hz hsm, ← diracEigen_iff_perChar]
  constructor
  · intro h0
    obtain ⟨f, hf0, -, hfe⟩ :=
      (NlsGge.ThirdConsultation.M.eigenvalue_iff_schur_det_zero (periodicPair φ) n z hz hsm).2 h0
    exact (diracEigen_congr hP z).1 ⟨f, hf0, hfe⟩
  · intro h0
    obtain ⟨f, hf0, hfe⟩ := (diracEigen_congr hP z).2 h0
    exact eigen_to_det (periodicPair φ) n z hz hsm f hf0 hfe

end NlsGge.ThirdConsultation.KST
end
