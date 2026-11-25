import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.MRound11Paths
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST016

/-!
# M-026: genuine even remainder and the retained diagonal clause (proof development, AUTHOR; not self-reviewed)

Heads: Pro round 11 (`PRO_DEFINITION_RESPONSE_FP80_11.md` section 7.1, commit c7aa9978), printed verbatim.
Route (Molnar Lemmas 8-9 grouped/parity strategy, as in Pro section 7.2): `hsmall` gives `||T^2|| < 1`; the
`HasSum` of the even and odd path series (geometric majorants) are proved first; channel parity kills the
odd off-diagonal and even diagonal path terms; the off-diagonal clause is the landed
`KST016.reducedBC_fourier_remainders`; the diagonal clause is the odd split of the full series.
No real-type, n != 0 or high-index hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open scoped InnerProduct InnerProductSpace
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004

private theorem diag_odd_gen
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2‖ < 1)
    (i : Bool) :
    ((lam - (n : ℂ) * (Real.pi : ℂ)) -
        NlsGge.ThirdConsultation.MTwoMode.schurEntry φ n lam hlam i i =
      ∑' j : ℕ, NlsGge.ThirdConsultation.MTwoMode.schurPathTerm φ n lam hlam
        (2 * j + 1) i i) ∧
    (∑' j : ℕ, NlsGge.ThirdConsultation.MTwoMode.schurPathTerm φ n lam hlam
        (2 * j + 1) i i =
      inner ℂ (NlsGge.ThirdConsultation.MTwoMode.schurFrame n i : KSTPairL2)
        (NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam
          ((Ring.inverse
            (1 - NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2) :
              NlsGge.ThirdConsultation.MTwoModeSupp.EndH)
            (NlsGge.Atomic.KST012.potentialOnPn
              (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n
              (NlsGge.ThirdConsultation.MTwoMode.schurFrame n i : KSTPairL2))))) :=
  ⟨NlsGge.ThirdConsultation.MTwoModeSupp.schurDiagonal_eq_odd φ n lam hlam hT i,
    (NlsGge.ThirdConsultation.MTwoModeSupp.hasSum_odd_paths φ n lam hlam hT i i).tsum_eq⟩

theorem schur_fourier_remainder
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall :
      ‖NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2‖ ≤
        (1 / 2 : ℝ))
    (plus : Bool) :
    NlsGge.ThirdConsultation.MTwoMode.offDiagonal φ n lam hlam plus -
        NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ plus
          (if plus then 2 * n else -2 * n) =
      NlsGge.ThirdConsultation.MTwoMode.schurEvenRemainder
        φ n lam hlam plus := by
  have hT := NlsGge.ThirdConsultation.MTwoModeSupp.sq_norm_lt_one φ n lam hlam hsmall
  obtain ⟨_, _, hB, hC⟩ := NlsGge.Atomic.KST016.reducedBC_fourier_remainders
    (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam hT
  cases plus
  · change NlsGge.Atomic.KST016.reducedC
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam -
      NlsGge.Atomic.KST016.coveredCoeff
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) true (-2 * n) =
      NlsGge.Atomic.KST016.remainderC
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam
    rw [hC]
    ring
  · change NlsGge.Atomic.KST016.reducedB
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam -
      NlsGge.Atomic.KST016.coveredCoeff
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) false (2 * n) =
      NlsGge.Atomic.KST016.remainderB
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam
    rw [hB]
    ring

theorem schur_diagonal_odd_formula
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall :
      ‖NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2‖ ≤
        (1 / 2 : ℝ))
    (plus : Bool) :
    let T := NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam
    let e : NlsGge.Atomic.KST003.KSTPairL2 :=
      NlsGge.ThirdConsultation.MTwoMode.schurFrame n
        (if plus then false else true)
    let V := NlsGge.Atomic.KST012.potentialOnPn
      (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n
    (if plus then
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam
      else
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam) =
        NlsGge.ThirdConsultation.MTwoMode.schurOddRemainder
          φ n lam hlam plus ∧
      NlsGge.ThirdConsultation.MTwoMode.schurOddRemainder
          φ n lam hlam plus =
        inner ℂ e (T ((Ring.inverse (1 - T ^ 2) :
          NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ] NlsGge.Atomic.KST003.KSTPairL2) (V e))) := by
  intro T e V
  have hT := NlsGge.ThirdConsultation.MTwoModeSupp.sq_norm_lt_one φ n lam hlam hsmall
  cases plus
  · exact diag_odd_gen φ n lam hlam hT true
  · exact diag_odd_gen φ n lam hlam hT false

theorem schur_even_remainder_inverse_formula
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall :
      ‖NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2‖ ≤
        (1 / 2 : ℝ))
    (plus : Bool) :
    let T := NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam
    let i : Bool := if plus then false else true
    let er : NlsGge.Atomic.KST003.KSTPairL2 :=
      NlsGge.ThirdConsultation.MTwoMode.schurFrame n i
    let ec : NlsGge.Atomic.KST003.KSTPairL2 :=
      NlsGge.ThirdConsultation.MTwoMode.schurFrame n (!i)
    let V := NlsGge.Atomic.KST012.potentialOnPn
      (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n
    NlsGge.ThirdConsultation.MTwoMode.schurEvenRemainder
        φ n lam hlam plus =
      inner ℂ er ((T ^ 2) ((Ring.inverse (1 - T ^ 2) :
          NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ] NlsGge.Atomic.KST003.KSTPairL2) (V ec))) := by
  intro T i er ec V
  have hT := NlsGge.ThirdConsultation.MTwoModeSupp.sq_norm_lt_one φ n lam hlam hsmall
  cases plus
  · exact (NlsGge.ThirdConsultation.MTwoModeSupp.hasSum_even_paths φ n lam hlam hT true false).tsum_eq
  · exact (NlsGge.ThirdConsultation.MTwoModeSupp.hasSum_even_paths φ n lam hlam hT false true).tsum_eq

end NlsGge.ThirdConsultation.M

end
