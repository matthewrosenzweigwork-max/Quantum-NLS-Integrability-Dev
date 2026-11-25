import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.MW2Series
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST014
import NlsGge.Atomic.KST.KST016

/-!
# MW2Diag: norm-free equality of the two Schur diagonals (proof development, AUTHOR; not self-reviewed)

Pro round 11 section 7.3 (W2) for M-025.  A copy of the landed `M025.schur_diagonals_equal` proof (grouped-series strategy of
Molnar Lemma 8) in which `hsmall` is replaced by `Summable (fun j => ||(T^2)^j||)` and the Neumann providers by the
`MW2Series` norm-free lemmas.  The landed KST014 grouped diagonal equality, `private` in the worker mirror, is the
Prop-valued argument `Stage14NStmt` (verbatim type of `KST014.stage14N_grouped_finite_diagonal_eq`).
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeW

open scoped InnerProduct InnerProductSpace
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004

/-- Verbatim type of `NlsGge.Atomic.KST014.stage14N_grouped_finite_diagonal_eq`. -/
def Stage14NStmt : Prop :=
  ∀ (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n) (k : ℕ),
    let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
    inner ℂ (kstPnLower n)
      (((1 + T) * (T ^ 2) ^ k : KSTPairL2 →L[ℂ] KSTPairL2)
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) =
    inner ℂ (kstPnUpper n)
      (((1 + T) * (T ^ 2) ^ k : KSTPairL2 →L[ℂ] KSTPairL2)
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n)))

theorem schur_diagonals_equal_core_w (h14N : Stage14NStmt)
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ =>
      ‖(NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2) ^ j‖) :
    NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam =
      NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam := by
  classical
  let p : NlsGge.Atomic.KST002.PhysicalPairLp :=
    NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator p n lam hlam
  have hsq : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖ := hT
  obtain ⟨_hunit, hinv, _hr, _hl⟩ :=
    inverse_one_sub_of_sq_summable T hsq
  have hs : HasSum (fun k : ℕ => (1 + T) * (T ^ 2) ^ k) (Ring.inverse (1 - T)) := by
    have h0 : HasSum (fun k : ℕ => (T ^ 2) ^ k) (Ring.inverse (1 - T ^ 2)) :=
      (hasSum_geom_inverse_of_summable (T ^ 2) hsq).2
    simpa only [← hinv] using h0.mul_left (1 + T)
  let Ll : (KSTPairL2 →L[ℂ] KSTPairL2) →L[ℂ] ℂ :=
    (innerSL ℂ (kstPnLower n)).comp
      (ContinuousLinearMap.apply ℂ KSTPairL2
        (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnLower n)))
  let Lu : (KSTPairL2 →L[ℂ] KSTPairL2) →L[ℂ] ℂ :=
    (innerSL ℂ (kstPnUpper n)).comp
      (ContinuousLinearMap.apply ℂ KSTPairL2
        (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnUpper n)))
  have hl : HasSum (fun k : ℕ => Ll ((1 + T) * (T ^ 2) ^ k))
      (Ll (Ring.inverse (1 - T))) := Ll.hasSum hs
  have hu : HasSum (fun k : ℕ => Lu ((1 + T) * (T ^ 2) ^ k))
      (Lu (Ring.inverse (1 - T))) := Lu.hasSum hs
  have hpoint : ∀ k : ℕ, Ll ((1 + T) * (T ^ 2) ^ k) = Lu ((1 + T) * (T ^ 2) ^ k) := by
    intro k
    exact h14N p n lam hlam k
  have hEq : Ll (Ring.inverse (1 - T)) = Lu (Ring.inverse (1 - T)) :=
    hl.unique (hu.congr_fun hpoint)
  have hEq' : inner ℂ (kstPnLower n)
      (Ring.inverse (1 - T) (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnLower n))) =
    inner ℂ (kstPnUpper n)
      (Ring.inverse (1 - T) (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnUpper n))) := hEq
  have ho := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
    simpa [kstPnFrame] using ho false false
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
    simpa [kstPnFrame] using ho true true
  have hPl : ∀ f : KSTPairL2,
      inner ℂ (kstPnLower n) (spectralPn n f) = inner ℂ (kstPnLower n) f :=
    fun f => NlsGge.Atomic.KST016.inner_frame_Pn n false f
  have hPu : ∀ f : KSTPairL2,
      inner ℂ (kstPnUpper n) (spectralPn n f) = inner ℂ (kstPnUpper n) f :=
    fun f => NlsGge.Atomic.KST016.inner_frame_Pn n true f
  have hL : inner ℂ
      (NlsGge.ThirdConsultation.MTwoMode.schurFrame n false : KSTPairL2)
      (NlsGge.Atomic.KST013.reducedS p n lam hlam
        (NlsGge.ThirdConsultation.MTwoMode.schurFrame n false) : KSTPairL2) =
      (lam - (n : ℂ) * (Real.pi : ℂ)) -
        inner ℂ (kstPnLower n)
          (Ring.inverse (1 - T) (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnLower n))) := by
    change inner ℂ (kstPnLower n)
      ((lam - (n : ℂ) * (Real.pi : ℂ)) • kstPnLower n -
        spectralPn n (Ring.inverse (1 - T)
          (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnLower n)))) = _
    rw [inner_sub_right, inner_smul_right, hPl, hll, mul_one]
  have hU : inner ℂ
      (NlsGge.ThirdConsultation.MTwoMode.schurFrame n true : KSTPairL2)
      (NlsGge.Atomic.KST013.reducedS p n lam hlam
        (NlsGge.ThirdConsultation.MTwoMode.schurFrame n true) : KSTPairL2) =
      (lam - (n : ℂ) * (Real.pi : ℂ)) -
        inner ℂ (kstPnUpper n)
          (Ring.inverse (1 - T) (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnUpper n))) := by
    change inner ℂ (kstPnUpper n)
      ((lam - (n : ℂ) * (Real.pi : ℂ)) • kstPnUpper n -
        spectralPn n (Ring.inverse (1 - T)
          (NlsGge.Atomic.KST012.potentialOnPn p n (kstPnUpper n)))) = _
    rw [inner_sub_right, inner_smul_right, hPu, huu, mul_one]
  change (lam - (n : ℂ) * (Real.pi : ℂ)) -
      inner ℂ
        (NlsGge.ThirdConsultation.MTwoMode.schurFrame n false : KSTPairL2)
        (NlsGge.Atomic.KST013.reducedS p n lam hlam
          (NlsGge.ThirdConsultation.MTwoMode.schurFrame n false) : KSTPairL2) =
    (lam - (n : ℂ) * (Real.pi : ℂ)) -
      inner ℂ
        (NlsGge.ThirdConsultation.MTwoMode.schurFrame n true : KSTPairL2)
        (NlsGge.Atomic.KST013.reducedS p n lam hlam
          (NlsGge.ThirdConsultation.MTwoMode.schurFrame n true) : KSTPairL2)
  rw [hL, hU, hEq']

end NlsGge.ThirdConsultation.MTwoModeW

end
