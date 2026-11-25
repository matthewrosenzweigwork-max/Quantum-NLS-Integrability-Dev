import Mathlib
import NlsGge.Atomic.DM.DM009
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.Atomic.KST.KST032

/- KST033Real PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST033Real.lean.
   SUPPORTING module (no packet increment).  Real-form half of KST-033 (Lemma 5.1(ii)): for ε = ±1 and
   φ false = ε • star (φ true) the reduced diagonal coefficient satisfies a φ n (star w) = star (a φ n w), hence the
   diagonal zero is real.  Route: the conjugate-linear map Psi_ε = DM009Psi.PsiMap ε (landed, ε general), re-run for
   general ε the ε = 1 intertwining chain of DM009 (psi1_compMult ... psi1_localCorrection), and combine with the
   landed unconditional diagonal identity NlsGge.DM009Diag.diag_identity (DM-009).  See KST033_ROUTE.md. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory NlsGge.Schur NlsGge.Analysis NlsGge.Pilot
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST006 NlsGge.Atomic.KST007 NlsGge.Atomic.KST012
open NlsGge.DM009Psi
open NlsGge.Atomic.KST016 (localQ localCorrection localFreeFactor qParameter_apply
  potentialParameter_apply compMult_component)
open scoped InnerProductSpace

namespace NlsGge.ThirdConsultation.KST.KST033R

theorem psiE_norm (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (x : KSTPairL2) : ‖PsiMap ε x‖ = ‖x‖ := by
  have h1 := PsiMap_inner ε hε x x
  have e : ∀ y : KSTPairL2, inner ℂ y y = ((‖y‖ : ℝ) : ℂ) ^ 2 :=
    fun y => inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y
  have h2 : ((‖PsiMap ε x‖ : ℝ) : ℂ) ^ 2 = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
    rw [← e (PsiMap ε x), ← e x, h1, e x]
    simp
  have h3 : ‖PsiMap ε x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

theorem psiE_continuous (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : Continuous (PsiMap ε) := by
  refine Isometry.continuous (Isometry.of_dist_eq fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← PsiMap_sub ε, psiE_norm ε hε]

theorem psiE_sq (ε : ℝ) (x : KSTPairL2) : PsiMap ε (PsiMap ε x) = (ε : ℂ) • x := by
  apply PiLp.ext
  intro b
  cases b
  · rw [PsiMap_false, PsiMap_true, star_star, PiLp.smul_apply]
  · rw [PsiMap_true, PsiMap_false, starS_smul, starS_star, star_epsilon, PiLp.smul_apply]

/-- Psi_ε as a `ConjBij` (DM009 S1), with two-sided inverse `ε • Psi_ε`. -/
def psiEBij (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : NlsGge.DM009Transport.ConjBij KSTPairL2 where
  f := PsiMap ε
  g := fun x => (ε : ℂ) • PsiMap ε x
  f_add := PsiMap_add ε
  f_smul := PsiMap_smul ε
  g_add := fun x y => by
    show (ε : ℂ) • PsiMap ε (x + y) = (ε : ℂ) • PsiMap ε x + (ε : ℂ) • PsiMap ε y
    rw [PsiMap_add, smul_add]
  g_smul := fun c x => by
    show (ε : ℂ) • PsiMap ε (c • x) = star c • ((ε : ℂ) • PsiMap ε x)
    rw [PsiMap_smul, smul_comm]
  f_cont := psiE_continuous ε hε
  g_cont := (psiE_continuous ε hε).const_smul (ε : ℂ)
  fg := fun x => by
    show PsiMap ε ((ε : ℂ) • PsiMap ε x) = x
    rw [PsiMap_smul, star_epsilon, psiE_sq, smul_smul, epsilon_sq ε hε, one_smul]
  gf := fun x => by
    show (ε : ℂ) • PsiMap ε (PsiMap ε x) = x
    rw [psiE_sq, smul_smul, epsilon_sq ε hε, one_smul]

/-- Psi_ε intertwines the complementary multiplier, the parameter being conjugated. -/
theorem psiE_compMult (ε : ℝ) (n : ℤ) (z z' : ℂ) (hz : z ∈ spectralStrip n)
    (hz' : z' ∈ spectralStrip n) (hzz : star z = z') (f : KSTPairL2) :
    PsiMap ε (complementaryMultiplier n z hz f) =
      complementaryMultiplier n z' hz' (PsiMap ε f) := by
  apply PiLp.ext
  intro b
  cases b
  · simp only [PsiMap_false, compMult_component]
    apply scalar_ext
    intro l
    rw [spectralCoeff_smul, spectralCoeff_star, coeff_scalarCM n z hz true,
      coeff_scalarCM n z' hz' false, spectralCoeff_smul, spectralCoeff_star]
    have e : sourceModeIndex true (-l) = sourceModeIndex false l := by
      simp [NlsGge.Atomic.KST004.sourceModeIndex]
    rw [e, star_mul', star_compl, hzz]
    ring
  · simp only [PsiMap_true, compMult_component]
    apply scalar_ext
    intro l
    rw [spectralCoeff_star, coeff_scalarCM n z hz false, coeff_scalarCM n z' hz' true,
      spectralCoeff_star]
    have e : sourceModeIndex false (-l) = sourceModeIndex true l := by
      simp [NlsGge.Atomic.KST004.sourceModeIndex]
    rw [e, star_mul', star_compl, hzz]
    first | done | ring

theorem psiE_freeB (ε : ℝ) (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (hreal : star z₀ = z₀)
    (w : ℂ) (x : KSTPairL2) :
    freeB n z₀ hz₀ (star w) (PsiMap ε x) = PsiMap ε (freeB n z₀ hz₀ w x) := by
  unfold freeB
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, PsiMap_smul,
    psiE_compMult ε n z₀ z₀ hz₀ hz₀ hreal x, star_sub, hreal]

theorem psiE_freeInv (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (z₀ : ℂ)
    (hz₀ : z₀ ∈ spectralStrip n) (hreal : star z₀ = z₀) (w : ℂ) (x : KSTPairL2) :
    PsiMap ε (Ring.inverse (1 - freeB n z₀ hz₀ w) x) =
      Ring.inverse (1 - freeB n z₀ hz₀ (star w)) (PsiMap ε x) :=
  (NlsGge.DM009Transport.transport_inverse (psiEBij ε hε) (freeB n z₀ hz₀ w)
    (freeB n z₀ hz₀ (star w)) (fun y => psiE_freeB ε n z₀ hz₀ hreal w y) x).symm

theorem psiE_qOperator (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ)
    (z z' : ℂ) (hz : z ∈ spectralStrip n) (hz' : z' ∈ spectralStrip n) (hzz : star z = z')
    (f : KSTPairL2) :
    PsiMap ε (qOperator φ n z hz f) = qOperator φ n z' hz' (PsiMap ε f) := by
  subst hzz
  exact PsiMap_Q φ ε hε h n z hz hz' f

theorem psiE_localQ (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) (x : KSTPairL2) :
    PsiMap ε (localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) x) =
      localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ) (PsiMap ε x) := by
  unfold localQ
  simp only [ContinuousLinearMap.mul_apply, qParameter_apply]
  rw [localFreeFactor_eq_sub, localFreeFactor_eq_sub,
    psiE_qOperator φ ε hε h n _ _ (NlsGge.ThirdConsultation.KST.center_mem_strip n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (center_star n),
    psiE_freeInv ε hε n _ (NlsGge.ThirdConsultation.KST.center_mem_strip n) (center_star n)]

theorem psiE_localQ_inv (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) (y : KSTPairL2) :
    PsiMap ε (Ring.inverse (1 - localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ)) y) =
      Ring.inverse (1 - localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ)) (PsiMap ε y) :=
  (NlsGge.DM009Transport.transport_inverse (psiEBij ε hε)
    (localQ n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ))
    (localQ n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ))
    (fun u => (psiE_localQ φ ε hε h n w u).symm) y).symm

theorem psiE_potentialParameter (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (x : KSTPairL2) :
    PsiMap ε (NlsGge.Atomic.KST016.potentialParameter n φ x) =
      NlsGge.Atomic.KST016.potentialParameter n φ (PsiMap ε x) :=
  PsiMap_potential φ ε hε h n x

theorem psiE_localCorrection (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) (x : KSTPairL2) :
    PsiMap ε (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) x) =
      localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ) (PsiMap ε x) := by
  unfold localCorrection
  simp only [ContinuousLinearMap.mul_apply]
  rw [PsiMap_Pn ε hε, psiE_localQ_inv φ ε hε h n w, psiE_potentialParameter φ ε hε h n x]

/-- Psi identity (general ε): `a φ n w = star (diagU φ n (star w))`, for every `w`. -/
theorem a_conj_identity_eps (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.a φ n w = star (diagU φ n (star w)) := by
  have h1 := PsiMap_inner ε hε (kstPnLower n)
    (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnLower n))
  rw [psiE_localCorrection φ ε hε h n w (kstPnLower n), PsiMap_lower] at h1
  rw [a_formula, diagU, h1, star_star]

/-- Real-form symmetry of the reduced diagonal coefficient, for ε = ±1, every `n` and every `w`. -/
theorem a_star_of_realForm (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.a φ n (star w) =
      star (NlsGge.ThirdConsultation.KST.a φ n w) := by
  have h1 := a_conj_identity_eps φ ε hε h n (star w)
  rw [star_star] at h1
  rw [h1]
  exact congrArg star (NlsGge.DM009Diag.diag_identity n φ w)

/-- The diagonal zero of a real-form potential is real (uniqueness in the closed `π/48` disc). -/
theorem diagonalZero_star (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : NlsGge.ThirdConsultation.KST.UnboundedWeight w) (φ : PhysicalPairLp)
    (hφ : φ ∈ NlsGge.ThirdConsultation.KST.physicalComponentBall w (2*M))
    (n : ℤ) (hn : NlsGge.ThirdConsultation.KST.diagonalThreshold w M ≤ n.natAbs)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (h : φ false = (ε : ℂ) • star (φ true)) :
    star (NlsGge.ThirdConsultation.KST.diagonalZero n φ) =
      NlsGge.ThirdConsultation.KST.diagonalZero n φ := by
  obtain ⟨-, -, hmem, hfix, huniq⟩ :=
    NlsGge.ThirdConsultation.KST.kst032 w M hM hw φ hφ n hn
  set σ := NlsGge.ThirdConsultation.KST.diagonalZero n φ with hσ
  have hcen : star (NlsGge.ThirdConsultation.KST.center n) = NlsGge.ThirdConsultation.KST.center n :=
    center_star n
  have hmem' : star σ ∈ Metric.closedBall (NlsGge.ThirdConsultation.KST.center n) (Real.pi/48) := by
    have h1 : ‖σ - NlsGge.ThirdConsultation.KST.center n‖ ≤ Real.pi / 48 := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.1 hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : star σ - NlsGge.ThirdConsultation.KST.center n =
        star (σ - NlsGge.ThirdConsultation.KST.center n) := by
      rw [star_sub, hcen]
    rw [e, norm_star]
    exact h1
  have hfix' : star σ =
      NlsGge.ThirdConsultation.KST.center n + NlsGge.ThirdConsultation.KST.a φ n (star σ) := by
    rw [a_star_of_realForm φ ε hε h n σ]
    calc star σ = star (NlsGge.ThirdConsultation.KST.center n +
          NlsGge.ThirdConsultation.KST.a φ n σ) := congrArg star hfix
      _ = _ := by rw [star_add, hcen]
  exact huniq (star σ) hmem' hfix'

end NlsGge.ThirdConsultation.KST.KST033R
end
