import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.DM.DM009
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Real

/- KST-051 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST051.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-051"
   (gpt6pro_followup10; identical in followups 1-10; no Pro round entry touches KST-051).
   Route: the Psi_eps real-form intertwining already landed for KST-033 (KST033Real.psiE_localCorrection,
   DM009 PsiMap_inner/PsiMap_lower/PsiMap_upper) applied to the (lower, upper) entry of the correction gives
   b w = eps * star (c (star w)); at the real diagonal zero (KST033Real.diagonalZero_star) this is
   b sigma = eps * star (c sigma); take norms and divide.  Same Psi route as KST-033 (not the source's
   KST-015 inner-product statement); no new mathematical argument, KST-050 is not used by this head.
   The weight/ball/threshold hypotheses are only used to obtain star sigma = sigma. -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003

namespace NlsGge.ThirdConsultation.KST

/-- Off-diagonal real-form identity for every `ε = ±1`, every `n` and every `w` (no threshold):
`b φ n w = ε * star (c φ n (star w))`. -/
theorem kst051_b_eq (φ : Potential) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) :
    b φ n w = (ε : ℂ) * star (c φ n (star w)) := by
  have h1 := NlsGge.DM009Psi.PsiMap_inner ε hε (kstPnLower n)
    (NlsGge.Atomic.KST016.localCorrection n (center n) (center_mem_strip n) (w, φ) (kstPnUpper n))
  rw [NlsGge.DM009Psi.PsiMap_lower,
    NlsGge.ThirdConsultation.KST.KST033R.psiE_localCorrection φ ε hε h n w (kstPnUpper n),
    NlsGge.DM009Psi.PsiMap_upper, map_smul, inner_smul_right] at h1
  have e1 : inner ℂ (kstPnUpper n)
      (NlsGge.Atomic.KST016.localCorrection n (center n) (center_mem_strip n) (star w, φ)
        (kstPnLower n)) = c φ n (star w) := rfl
  have e2 : inner ℂ (kstPnLower n)
      (NlsGge.Atomic.KST016.localCorrection n (center n) (center_mem_strip n) (w, φ)
        (kstPnUpper n)) = b φ n w := rfl
  rw [e1, e2] at h1
  have h2 := congrArg star h1
  rw [star_star, star_mul', Complex.star_def, Complex.conj_ofReal] at h2
  rw [← h2]
  simp [Complex.star_def]

theorem kst051 (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : UnboundedWeight w) (φ : Potential)
    (hφ : φ ∈ physicalComponentBall w (2*M)) (ε : ℝ)
    (hreal : RealForm ε (periodicPair φ))
    (n : ℤ) (hn : diagonalThreshold w M ≤ n.natAbs) :
  let σ := diagonalZero n φ
  star σ = σ ∧ b φ n σ = (ε : ℂ)*star (c φ n σ) ∧
  ‖b φ n σ‖ = ‖c φ n σ‖ ∧
  (b φ n σ ≠ 0 → ‖c φ n σ / b φ n σ‖ = 1) := by
  intro σ
  obtain ⟨hε, hfalse⟩ := hreal
  have hstar : star σ = σ :=
    NlsGge.ThirdConsultation.KST.KST033R.diagonalZero_star w M hM hw φ hφ n hn ε hε hfalse
  have hb : b φ n σ = (ε : ℂ) * star (c φ n σ) := by
    have := kst051_b_eq φ ε hε hfalse n σ
    rwa [hstar] at this
  have hnorm : ‖b φ n σ‖ = ‖c φ n σ‖ := by
    rw [hb, norm_mul, norm_star]
    rcases hε with h | h <;> simp [h]
  refine ⟨hstar, hb, hnorm, fun hne => ?_⟩
  rw [norm_div, ← hnorm]
  exact div_self (norm_ne_zero_iff.2 hne)

end NlsGge.ThirdConsultation.KST
end
