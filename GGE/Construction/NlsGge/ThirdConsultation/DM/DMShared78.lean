import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.DM.DM002
import NlsGge.Atomic.DM.DM010
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.LIB.LIB031
import NlsGge.Atomic.LIB.LIB032
import NlsGge.Atomic.LIB.LIB033
import NlsGge.Atomic.LIB.LIB036
import NlsGge.Atomic.LIB.LIB038

                                                                                                                                              
                                                                                               
                                                                                   
                                                                                                       
                                                                                                               
                                                                                                              
                                                                                                                     
                                                                                                      
                                                                  
                                                                                                                  
                                                                                                              
                                                                                        

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace NlsGge.ThirdConsultation.DM
noncomputable section
open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002

/-- DEFINITIONS/DM.lean.md lines 188-189 (verbatim). -/
def dmSpectralPoint (n : ℤ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * ((n : ℂ) + z)

/-- DEFINITIONS/DM.lean.md lines 191-193 (verbatim). -/
def dmAlpha (v : PiPairL2) (n : ℤ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * NlsGge.ThirdConsultation.KST.a
    (dmKstPotential v) n (dmSpectralPoint n z)

/-- DEFINITIONS/DM.lean.md lines 195-197 (verbatim). -/
def dmBetaPlus (v : PiPairL2) (n : ℤ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * NlsGge.ThirdConsultation.KST.b
    (dmKstPotential v) n (dmSpectralPoint n z)

/-- DEFINITIONS/DM.lean.md lines 199-201 (verbatim). -/
def dmBetaMinus (v : PiPairL2) (n : ℤ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * NlsGge.ThirdConsultation.KST.c
    (dmKstPotential v) n (dmSpectralPoint n z)

/-- Pro round 7-8 section 5 (DM-008), body verbatim; `frame`, `correction`, `H`, `spectralStrip` are qualified (lexical). -/
def dmEffectiveMatrix (v : PiPairL2) (n : ℤ) (z : ℂ)
    (hz : dmSpectralPoint n z ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    Matrix Bool Bool ℂ :=
  fun i j => (Real.pi : ℂ)⁻¹ *
    inner ℂ (NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H)
      (NlsGge.Atomic.KST016.correction (dmKstPotential v) n (dmSpectralPoint n z) hz
        (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H))

open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB032
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB036
open NlsGge.Atomic.LIB038

/-- Pro round 7-8 section 9 (DM-012): unit-interval resolvent, totalized by zero outside the predicate. -/
def dmUnitResolvent (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (z : ℂ) : SourcePairL2 →L[ℂ] SourcePairL2 := by
  classical
  exact if h : HasBoundedResolvent (zsRealization φ bc) z
    then Classical.choose h else 0

theorem dmUnitResolvent_mem_domain
    (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (f : SourcePairL2) :
    dmUnitResolvent φ bc z f ∈ (zsRealization φ bc).domain := by
  classical
  unfold dmUnitResolvent
  split_ifs with h
  · exact Classical.choose ((Classical.choose_spec h).1 f)
  · change (0 : SourcePairL2) ∈ zsDomain bc
    exact (zsDomain bc).zero_mem

def dmUnitResolventLift (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (z : ℂ) (f : SourcePairL2) : H1Pair :=
  domainLift
    (⟨dmUnitResolvent φ bc z f,
      dmUnitResolvent_mem_domain φ bc z f⟩ : zsDomain bc)

def dmSpectrum (v : PiPairL2) (bc : ZSBoundaryCondition) : Set ℂ :=
  {«λ» | ¬ HasBoundedResolvent
    (zsRealization (scaledPotential v) bc) ((Real.pi : ℂ) * «λ»)}

def dmSourceResolventUnit (v : PiPairL2) (bc : ZSBoundaryCondition)
    («λ» : ℂ) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  (Real.pi : ℂ) •
    dmUnitResolvent (scaledPotential v) bc ((Real.pi : ℂ) * «λ»)

def dmSourceResolventPi (v : PiPairL2) (bc : ZSBoundaryCondition)
    («λ» : ℂ) : PiPairL2 →L[ℂ] PiPairL2 :=
  unitaryRescalePair.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((dmSourceResolventUnit v bc «λ»).comp
      unitaryRescalePair.toContinuousLinearEquiv.toContinuousLinearMap)

def dmCirclePoint (n : ℤ) (ρ t : ℝ) : ℂ :=
  (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))

def dmProjectionIntegrand
    (v : PiPairL2) (bc : ZSBoundaryCondition) (n : ℤ) (ρ t : ℝ) :
    PiPairL2 →L[ℂ] PiPairL2 :=
  (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))) •
    dmSourceResolventPi v bc (dmCirclePoint n ρ t)

def dmRieszProjection
    (v : PiPairL2) (bc : ZSBoundaryCondition) (n : ℤ) (ρ : ℝ) :
    PiPairL2 →L[ℂ] PiPairL2 :=
  ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    ∫ t in (0 : ℝ)..(2 * Real.pi), dmProjectionIntegrand v bc n ρ t

def dmPeriodicCharacteristic (v : PiPairL2) («λ» : ℂ) : ℂ :=
  NlsGge.GK38.perChar (scaledPhysicalPair v) ((Real.pi : ℂ) * «λ»)

def dmCoveredCoeff (v : PiPairL2) (b : Bool) (ell : ℤ) : ℂ :=
  if ell % 2 = 0 then piCoeff (v b) (ell / 2) else 0

def dmHankelEntry (v : PiPairL2) (n : ℤ) («λ» : ℂ)
    (j k : Bool × Sector n) : ℂ :=
  if j.1 = k.1 then 0 else
    (if j.1 then dmCoveredCoeff v true (-(j.2.val + k.2.val))
     else dmCoveredCoeff v false (j.2.val + k.2.val)) /
      ((«λ» - (j.2.val : ℂ)) * («λ» - (k.2.val : ℂ)))

def dmHankelColumnEnergy (v : PiPairL2) (n : ℤ) («λ» : ℂ) : ℝ≥0∞ :=
  ∑' k : Bool × Sector n,
    (∑' j : Bool × Sector n, ENNReal.ofReal ‖dmHankelEntry v n «λ» j k‖)^2

def dmContinuousCoeff (n : ℤ)
    (F : C(Icc (0 : ℝ) 1, PointPair)) (j : Bool × Sector n) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    Complex.exp
      ((if j.1 then Complex.I else -Complex.I) *
        (j.2.val : ℂ) * (Real.pi : ℂ) * (t : ℂ)) *
      (Set.IccExtend zero_le_one F t) j.1

def dmSandwichValue (v : PiPairL2) (n : ℤ) («λ» : ℂ)
    (f : SourcePairL2) : C(Icc (0 : ℝ) 1, PointPair) :=
  (Real.pi : ℂ) • pairRepresentative
    (dmUnitResolventLift 0 (labelBoundary n) ((Real.pi : ℂ) * «λ»)
      (potentialProduct (scaledPotential v)
        (dmUnitResolventLift 0 (labelBoundary n)
          ((Real.pi : ℂ) * «λ») f)))

def dmSandwichedResolvent (v : PiPairL2) (n : ℤ) («λ» : ℂ) :
    SourcePairL2 →L[ℂ] C(Icc (0 : ℝ) 1, PointPair) := by
  classical
  exact if h : ∃ S : SourcePairL2 →L[ℂ] C(Icc (0 : ℝ) 1, PointPair),
      ∀ f : SourcePairL2, S f = dmSandwichValue v n «λ» f
    then Classical.choose h else 0

/-- Pro round 7-8 section 11 (DM-015): central rectangle of half-width N + 1/2 plus high open discs. -/
def dmLocalizationRegion (N : ℕ) (T : ℝ) : Set ℂ :=
  {z : ℂ | |z.re| ≤ (N : ℝ) + 1/2 ∧ |z.im| ≤ T} ∪
    ⋃ n : ℤ, if N < n.natAbs then
      Metric.ball (n : ℂ) (1/8 : ℝ) else ∅

end
end NlsGge.ThirdConsultation.DM
