                                                         
                                                                                        
                                                                                                                       
                                                                                                  
                                                                                            
                                                                                              
                                                                                                                   
                                                                        
                                                                                                   
                                                                                                        
                                                                                           
import Mathlib
import NlsGge.Atomic.DM.DM001
import NlsGge.Atomic.DM.DM002
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST001

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Atomic.DM003

open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002 NlsGge.Pilot

/-- DEFINITIONS/DM.lean.md line 173 (verbatim). -/
abbrev EvenInt := {k : ℤ // Even k}

/-- DEFINITIONS/DM.lean.md lines 175-176 (verbatim). -/
def liftWeight (Ω : ℤ → ℝ) : EvenInt → ℝ :=
  fun k => Ω (k.1 / 2)

/-- DEFINITIONS/DM.lean.md lines 178-180 (verbatim). -/
def EvenLatticeSubmultiplicative (w : EvenInt → ℝ) : Prop :=
  ∀ j k : EvenInt,
    w ⟨j.1+k.1, j.2.add k.2⟩ ≤ w j * w k

lemma even_half_eq (j : EvenInt) : j.1 = 2 * (j.1 / 2) := by
  obtain ⟨a, ha⟩ := j.2
  omega

lemma evenLattice_iff (Ω : ℤ → ℝ) :
    EvenLatticeSubmultiplicative (liftWeight Ω) ↔
      NlsGge.Atomic.DM046.SubmultiplicativeWeight Ω := by
  constructor
  · intro h k l
    have h2 := h ⟨2 * k, ⟨k, by omega⟩⟩ ⟨2 * l, ⟨l, by omega⟩⟩
    have e1 : (2 * k + 2 * l) / 2 = k + l := by omega
    have e2 : (2 * k) / 2 = k := by omega
    have e3 : (2 * l) / 2 = l := by omega
    simp only [liftWeight, e1, e2, e3] at h2
    exact h2
  · intro h j k
    have ej := even_half_eq j
    have ek := even_half_eq k
    have e : (j.1 + k.1) / 2 = j.1 / 2 + k.1 / 2 := by omega
    simp only [liftWeight]
    rw [e]
    exact h _ _

lemma even_scale_iff (Ω : ℤ → ℝ) (C : ℝ) :
    (∀ k : ℤ, Ω (2 * k) ≤ C * Ω k) ↔
      ∀ k : EvenInt, liftWeight Ω ⟨2 * k.1, k.2.mul_left 2⟩ ≤ C * liftWeight Ω k := by
  constructor
  · intro h k
    have ek := even_half_eq k
    have e : 2 * k.1 / 2 = k.1 := by omega
    simp only [liftWeight]
    rw [e]
    have h2 := h (k.1 / 2)
    rw [← ek] at h2
    exact h2
  · intro h m
    have h2 := h ⟨2 * m, ⟨m, by omega⟩⟩
    have e : 2 * m / 2 = m := by omega
    have e' : 2 * (2 * m) / 2 = 2 * m := by omega
    simp only [liftWeight, e, e'] at h2
    exact h2

theorem even_norm_identity (Ω : ℤ → ℝ) (v : PiPairL2) :
    (∑' k : ℤ, ENNReal.ofReal
      (Ω k^2 * (‖piCoeff (v true) k‖^2 + ‖piCoeff (v false) k‖^2))) =
    (ENNReal.ofReal Real.pi)⁻¹ ^ 2 *
      NlsGge.Atomic.KST001.weightedEvenFourierNormSq
        (fun j => Ω (j/2)) (scaledPhysicalPair v) := by
  have hF : ∀ m : ℤ,
      (physicalFourier (scaledPhysicalPair v).1 m, physicalFourier (scaledPhysicalPair v).2 m) =
        ((Real.pi : ℂ) * piCoeff (v true) m, (Real.pi : ℂ) * piCoeff (v false) m) := by
    intro m
    have h := scaledPotential_fourier v m
    rw [NlsGge.Atomic.KST001.periodOne_pair_even_coeff] at h
    exact h
  have e2 : ∀ m : ℤ, 2 * m / 2 = m := fun m => by omega
  have hn : ∀ x : ℂ, ‖(Real.pi : ℂ) * x‖ = Real.pi * ‖x‖ := fun x => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  unfold NlsGge.Atomic.KST001.weightedEvenFourierNormSq
  simp only [hF]
  simp only [NlsGge.Atomic.KST001.weightedPairMode, e2, hn]
  have hP0 : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  have hPtop : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
  have hL : ∀ m : ℤ,
      ENNReal.ofReal (Ω m ^ 2 * (‖piCoeff (v true) m‖ ^ 2 + ‖piCoeff (v false) m‖ ^ 2)) =
        ENNReal.ofReal (Ω m ^ 2) *
          (ENNReal.ofReal (‖piCoeff (v true) m‖ ^ 2) +
            ENNReal.ofReal (‖piCoeff (v false) m‖ ^ 2)) := by
    intro m
    rw [ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_add (sq_nonneg ‖piCoeff (v true) m‖) (sq_nonneg ‖piCoeff (v false) m‖)]
  have h1 : ∀ x : ℝ, ENNReal.ofReal ((Real.pi * x) ^ 2) =
      (ENNReal.ofReal Real.pi) ^ 2 * ENNReal.ofReal (x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (pow_nonneg Real.pi_pos.le 2)]
    congr 1
    ring
  have hR : ∀ m : ℤ,
      ENNReal.ofReal (Ω m ^ 2) *
          (ENNReal.ofReal ((Real.pi * ‖piCoeff (v true) m‖) ^ 2) +
            ENNReal.ofReal ((Real.pi * ‖piCoeff (v false) m‖) ^ 2)) =
        (ENNReal.ofReal Real.pi) ^ 2 *
          (ENNReal.ofReal (Ω m ^ 2) *
            (ENNReal.ofReal (‖piCoeff (v true) m‖ ^ 2) +
              ENNReal.ofReal (‖piCoeff (v false) m‖ ^ 2))) := by
    intro m
    rw [h1, h1]
    ring
  have hinv : (ENNReal.ofReal Real.pi)⁻¹ ^ 2 * (ENNReal.ofReal Real.pi) ^ 2 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel hP0 hPtop, one_pow]
  rw [tsum_congr hL, tsum_congr hR, ENNReal.tsum_mul_left, ← mul_assoc, hinv, one_mul]

-- DM-003 statement, verbatim from STATEMENTS/DM.md.
theorem evenWeight_transport (Ω : ℤ → ℝ) :
  (EvenLatticeSubmultiplicative (liftWeight Ω) ↔
    NlsGge.Atomic.DM046.SubmultiplicativeWeight Ω) ∧
  (∀ C : ℝ,
    (∀ k : ℤ, Ω (2*k) ≤ C*Ω k) ↔
    ∀ k : EvenInt, liftWeight Ω ⟨2*k.1, k.2.mul_left 2⟩ ≤
      C * liftWeight Ω k) ∧
  ∀ v : PiPairL2,
    (∑' k : ℤ, ENNReal.ofReal
      (Ω k^2 * (‖piCoeff (v true) k‖^2 + ‖piCoeff (v false) k‖^2))) =
    (ENNReal.ofReal Real.pi)⁻¹ ^ 2 *
      NlsGge.Atomic.KST001.weightedEvenFourierNormSq
        (fun j => Ω (j/2)) (scaledPhysicalPair v)
  := ⟨evenLattice_iff Ω, fun C => even_scale_iff Ω C, fun v => even_norm_identity Ω v⟩

#print axioms NlsGge.Atomic.DM003.evenWeight_transport

end NlsGge.Atomic.DM003
