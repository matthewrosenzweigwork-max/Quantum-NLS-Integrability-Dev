import Mathlib
import NlsGge.Atomic.M.M026
import NlsGge.ThirdConsultation.M.M023Analytic
import NlsGge.ThirdConsultation.M.MSchurBound

/-!
# M-027 analytic companion: `schur_diagonal_analytic_extension` (proof development, AUTHOR; not self-reviewed)

Head: Pro round 13 (`PRO_DEFINITION_RESPONSE_FP80_13.md`) section 8, "Source reasoning and analyticity obligation",
printed verbatim.

Route (Pro: Neumann series of analytic terms; inversion margin from the contraction q <= 1/2).  The weighted transported
operator `Tw (lam, a)` on the weighted carrier `SourceCode w n` is defined for every `lam` (via the bounded
sequence `gC n lam` on the enlarged region), is analytic at every point of the closed strip (M023Analytic), and the
Neumann operator `Tw * evenNeumann Tw` is analytic there as well (`analyticAt_evenNeumann`).  Composing with the
continuous linear functional `X |-> <resonant coefficient of X x0>` (x0 = weighted code of `V e_i`) gives the
extension `a : C -> C`; no off-strip value is chosen by hand.  On the strip the Neumann series is identified with the
odd path series of the ambient operator by `Tw_represents`, and then with the Schur diagonal by the landed M-026
formula `schur_diagonal_odd_formula_weighted`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M027A

open NlsGge.ThirdConsultation.MTwoMode NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
open NlsGge.ThirdConsultation.MTwoModeB

theorem rep_pow (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (a : PotentialCode w) (ha : RepresentsPotential w a φ)
    (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (x0 : SourceCode w n) (f0 : NlsGge.Atomic.KST003.KSTPairL2)
    (h0 : RepresentsSource w n x0 f0) (r : ℕ) :
    RepresentsSource w n (((Tw w hw n (lam, a)) ^ r) x0) (((ambientT φ n lam hlam) ^ r) f0) := by
  induction r with
  | zero => simpa using h0
  | succ r ih =>
    have h := Tw_represents w hw n (lam, a) φ _ _ hlam ha ih
    rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
    exact h

theorem weight_ne (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (n : ℤ)
    (b : Bool) (k : ℤ) : (shiftWeight w n b k : ℂ) ≠ 0 := by
  have : 0 < shiftWeight w n b k := by
    unfold shiftWeight
    split_ifs <;> exact weight_pos w hw _
  exact_mod_cast this.ne'

theorem analytic_general (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n)
    (i : Bool) (jj : Bool × ℤ)
    (hjj : ∀ g : NlsGge.Atomic.KST003.KSTPairL2,
      inner ℂ (schurFrame n i : NlsGge.Atomic.KST003.KSTPairL2) g = coefficientPair g jj.1 jj.2)
    (hE : shiftedPairEnergy w n false (coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n i : NlsGge.Atomic.KST003.KSTPairL2))) ≠ ⊤) :
    ∃ a : ℂ → ℂ,
      AnalyticOnNhd ℂ a (NlsGge.Atomic.KST004.spectralStrip n) ∧
      ∀ (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n),
        HasSum (fun j : ℕ => schurPathTerm φ n lam hlam (2 * j + 1) i i) (a lam) := by
  obtain ⟨b1, _, b3, b4, _, b6⟩ := weighted_code_bridges w hw n
  obtain ⟨a, ha, -⟩ := b1 φ hφ
  obtain ⟨-, hNa⟩ := b3 a φ ha
  have hth : 8 * ‖a‖ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n := by rw [← hNa]; exact hthreshold
  set f0 := NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
    (schurFrame n i : NlsGge.Atomic.KST003.KSTPairL2) with hf0
  obtain ⟨x0, hx0, -⟩ := b4 f0 hE
  let L : (SourceCode w n →L[ℂ] SourceCode w n) →L[ℂ] ℂ :=
    ((shiftWeight w n jj.1 jj.2 : ℂ)⁻¹) •
      ((lp.evalCLM ℂ (fun _ : Bool × ℤ => ℂ) 2 jj).comp
        (ContinuousLinearMap.apply ℂ (SourceCode w n) x0))
  have hLapp : ∀ X : SourceCode w n →L[ℂ] SourceCode w n,
      L X = ((shiftWeight w n jj.1 jj.2 : ℂ)⁻¹) * (X x0 jj) := fun X => rfl
  refine ⟨fun lam => L (Tw w hw n (lam, a) * evenNeumann (Tw w hw n (lam, a))), ?_, ?_⟩
  · intro lam0 hlam0
    have hp := analyticAt_evenNeumann w hw n (lam0, a) hlam0 hth
    have hT := analyticAt_Tw w hw n (lam0, a) hlam0
    have hF : AnalyticAt ℂ (fun q : ℂ × PotentialCode w =>
        Tw w hw n q * evenNeumann (Tw w hw n q)) (lam0, a) := hT.mul hp.1
    have hg : AnalyticAt ℂ (fun lam : ℂ => (lam, a)) lam0 :=
      AnalyticAt.prod (f := fun lam : ℂ => lam) (g := fun _ : ℂ => a) analyticAt_id analyticAt_const
    have hFg := AnalyticAt.comp (g := fun q : ℂ × PotentialCode w =>
        Tw w hw n q * evenNeumann (Tw w hw n q)) (f := fun lam : ℂ => (lam, a)) hF hg
    exact (L.analyticAt _).comp hFg
  · intro lam hlam
    obtain ⟨-, hsum, -⟩ := Tw_neumann w hw n (lam, a) hlam hth
    have hS := hsum.mul_left (Tw w hw n (lam, a))
    have hL := L.hasSum hS
    have hterm : ∀ j : ℕ, L (Tw w hw n (lam, a) * (Tw w hw n (lam, a) * Tw w hw n (lam, a)) ^ j) =
        schurPathTerm φ n lam hlam (2 * j + 1) i i := by
      intro j
      have e : Tw w hw n (lam, a) * (Tw w hw n (lam, a) * Tw w hw n (lam, a)) ^ j =
          (Tw w hw n (lam, a)) ^ (2 * j + 1) := by
        rw [NlsGge.ThirdConsultation.MTwoModeSupp.pow_two_mul_add_one, sq]
      rw [e, hLapp]
      have h2 : (((Tw w hw n (lam, a)) ^ (2 * j + 1)) x0) jj =
          (shiftWeight w n jj.1 jj.2 : ℂ) *
            coefficientPair (((ambientT φ n lam hlam) ^ (2 * j + 1)) f0) jj.1 jj.2 :=
        rep_pow w hw φ n a ha lam hlam x0 f0 hx0 (2 * j + 1) jj.1 jj.2
      rw [h2, ← mul_assoc, inv_mul_cancel₀ (weight_ne w hw n jj.1 jj.2), one_mul]
      exact (hjj _).symm
    have hfun : (fun j : ℕ => L (Tw w hw n (lam, a) *
        (Tw w hw n (lam, a) * Tw w hw n (lam, a)) ^ j)) =
        fun j : ℕ => schurPathTerm φ n lam hlam (2 * j + 1) i i := funext hterm
    rw [hfun] at hL
    exact hL

end NlsGge.ThirdConsultation.M027A

namespace NlsGge.ThirdConsultation.M

theorem schur_diagonal_analytic_extension
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    ∃ a : ℂ → ℂ,
      AnalyticOnNhd ℂ a (NlsGge.Atomic.KST004.spectralStrip n) ∧
      ∀ (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n),
        a lam = if plus then
          NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam
        else
          NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam := by
  have key : ∃ a : ℂ → ℂ,
      AnalyticOnNhd ℂ a (NlsGge.Atomic.KST004.spectralStrip n) ∧
      ∀ (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n),
        a lam = NlsGge.ThirdConsultation.MTwoMode.schurOddRemainder φ n lam hlam plus := by
    cases plus
    · obtain ⟨a, ha, hs⟩ := NlsGge.ThirdConsultation.M027A.analytic_general w hw φ hφ n hthreshold
        true (true, -n) (fun g => NlsGge.ThirdConsultation.MTwoModeB.inner_frame_true n g)
        (by
          rw [NlsGge.ThirdConsultation.MTwoModeB.shifted_V_upper]
          exact NlsGge.ThirdConsultation.MTwoModeB.compEnergy_ne_top w φ hφ true)
      exact ⟨a, ha, fun lam hlam => ((hs lam hlam).tsum_eq).symm⟩
    · obtain ⟨a, ha, hs⟩ := NlsGge.ThirdConsultation.M027A.analytic_general w hw φ hφ n hthreshold
        false (false, n) (fun g => NlsGge.ThirdConsultation.MTwoModeB.inner_frame_false n g)
        (by
          rw [NlsGge.ThirdConsultation.MTwoModeB.shifted_V_lower]
          exact NlsGge.ThirdConsultation.MTwoModeB.compEnergy_ne_top w φ hφ false)
      exact ⟨a, ha, fun lam hlam => ((hs lam hlam).tsum_eq).symm⟩
  obtain ⟨a, ha, hs⟩ := key
  refine ⟨a, ha, fun lam hlam => ?_⟩
  rw [hs lam hlam]
  exact (schur_diagonal_odd_formula_weighted w hw φ hφ n lam hlam hthreshold plus).1.symm

end NlsGge.ThirdConsultation.M

end
