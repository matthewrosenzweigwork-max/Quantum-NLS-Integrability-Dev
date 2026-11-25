import Mathlib
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST032
import NlsGge.Atomic.KST.KST035
import NlsGge.Atomic.KST.KST037
import NlsGge.Atomic.KST.KST038
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST039Host
import NlsGge.ThirdConsultation.KST.KST040Host
import NlsGge.ThirdConsultation.KST.KST040Support

/- KST-040 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST040.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-040"
   (identical in gpt6pro_followup1..10; no Pro round 5-12 entry touches KST-040).  No repair of the head.
   Route (source Proposition 5.1/(68), "conjugate-swap involution and uniqueness in the same source ball"):
   (1) the coefficient involution of a weighted pair is again a weighted pair of the same componentwise norms
   (the weight is even), so `weightedInvolution` realises it and preserves the componentwise ball;
   (2) the physical potentials satisfy psi true = eps * star (phi false), psi false = eps * star (phi true), hence the
   KST040Support symmetry (a, b, c and the diagonal zero transform by conjugate swap) gives
   adaptedCoefficients N psi = coefficientInvolution eps (adaptedCoefficients N phi), and by KST-035
   F (I x) = I (F x) on the ball; (3) `RealForm eps (wp y)` iff `I y = y`; (4) F injective on the ball (KST-038)
   gives RealForm (wp (F x)) iff RealForm (wp x); (5) adaptedInverse picks a preimage in the ball, so inverse
   preservation follows from (4). -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

namespace KST040W

section Weighted

variable (ω : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]

theorem weighted_ext {x y : Weighted ω} (h : weightedCoeffs ω x = weightedCoeffs ω y) : x = y := by
  apply PiLp.ext
  intro ch
  apply Subtype.ext
  funext m
  exact congrFun (congrFun h ch) m

theorem norm_eps (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : ‖(ε : ℂ)‖ = 1 := by
  rcases hε with rfl | rfl <;> simp

theorem periodOneWeight_neg (hev : ∀ k, ω (-k) = ω k) (m : ℤ) :
    periodOneWeight ω (-m) = periodOneWeight ω m := by
  show ω (2 * -m) = ω (2 * m)
  rw [show 2 * -m = -(2 * m) by ring, hev]

theorem exists_involution (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (x : Weighted ω) :
    ∃ y : Weighted ω, weightedCoeffs ω y = coefficientInvolution ε (weightedCoeffs ω x) ∧
      ∀ ch, ‖y ch‖ = ‖x (!ch)‖ := by
  set r : RawPair := coefficientInvolution ε (weightedCoeffs ω x) with hr
  have hsum : ∀ ch : Bool, HasSum
      (fun m : ℤ => (fun k => periodOneWeight ω k ^ 2) m * ‖r ch m‖ ^ 2) (‖x (!ch)‖ ^ 2) := by
    intro ch
    have h := weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) (x (!ch))
    have h2 := (Equiv.hasSum_iff (Equiv.neg ℤ)).2 h
    have e : (fun m : ℤ => (fun k => periodOneWeight ω k ^ 2) m * ‖r ch m‖ ^ 2) =
        ((fun n : ℤ => (fun k => periodOneWeight ω k ^ 2) n * ‖(x (!ch) : ℤ → ℂ) n‖ ^ 2) ∘
          (Equiv.neg ℤ)) := by
      funext m
      simp only [Function.comp, Equiv.neg_apply, hr, coefficientInvolution, weightedCoeffs,
        norm_mul, norm_star, norm_eps ε hε, one_mul, periodOneWeight_neg ω hev]
    rw [e]
    exact h2
  have hmem : ∀ ch, Memℓp (weightedCoordinates (fun k => periodOneWeight ω k ^ 2) (r ch)) 2 :=
    fun ch => (weightedCoordinates_mem_l2_iff _ (fun n => by positivity) (r ch)).2 (hsum ch).summable
  let y : Weighted ω := WithLp.toLp 2 (fun ch =>
    (⟨r ch, hmem ch⟩ : weightedSubmodule (fun k => periodOneWeight ω k ^ 2)))
  have hy : weightedCoeffs ω y = r := by
    funext ch m; rfl
  refine ⟨y, hy, fun ch => ?_⟩
  have h1 := weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) (y ch)
  have h1' : HasSum (fun m : ℤ => (fun k => periodOneWeight ω k ^ 2) m * ‖r ch m‖ ^ 2) (‖y ch‖ ^ 2) := h1
  have h3 := h1'.unique (hsum ch)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

theorem weightedInvolution_eq {ε : ℝ} {x y : Weighted ω}
    (hy : weightedCoeffs ω y = coefficientInvolution ε (weightedCoeffs ω x)) :
    weightedInvolution ω ε x = y := by
  classical
  have hex : ∃ z : Weighted ω, weightedCoeffs ω z = coefficientInvolution ε (weightedCoeffs ω x) :=
    ⟨y, hy⟩
  have h : weightedCoeffs ω (weightedInvolution ω ε x) =
      coefficientInvolution ε (weightedCoeffs ω x) := by
    show weightedCoeffs ω (if h : ∃ z : Weighted ω, weightedCoeffs ω z =
        coefficientInvolution ε (weightedCoeffs ω x) then Classical.choose h else 0) = _
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact weighted_ext ω (h.trans hy.symm)

theorem involution_coeffs (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (x : Weighted ω) :
    weightedCoeffs ω (weightedInvolution ω ε x) = coefficientInvolution ε (weightedCoeffs ω x) := by
  obtain ⟨y, hy, -⟩ := exists_involution ω hev ε hε x
  rw [weightedInvolution_eq ω hy]
  exact hy

theorem involution_norm (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (x : Weighted ω) (ch : Bool) :
    ‖(weightedInvolution ω ε x) ch‖ = ‖x (!ch)‖ := by
  obtain ⟨y, hy, hn⟩ := exists_involution ω hev ε hε x
  rw [weightedInvolution_eq ω hy]
  exact hn ch

theorem involution_mem_ball (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (R : ℝ) (x : Weighted ω) (hx : x ∈ componentBall ω R) :
    weightedInvolution ω ε x ∈ componentBall ω R := by
  intro ch
  rw [involution_norm ω hev ε hε x ch]
  exact hx (!ch)

variable (hω : ∀ k, 1 ≤ ω k)

theorem wp_involution (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (x : Weighted ω) :
    weightedPotential ω hω (weightedInvolution ω ε x) true =
        (ε : ℂ) • star (weightedPotential ω hω x false) ∧
    weightedPotential ω hω (weightedInvolution ω ε x) false =
        (ε : ℂ) • star (weightedPotential ω hω x true) := by
  have hc := involution_coeffs ω hev ε hε x
  constructor
  · apply NlsGge.ThirdConsultation.KST.KST033S.physical_ext
    intro m
    rw [NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω,
      NlsGge.ThirdConsultation.KST.KST033S.physicalFourier_smul,
      NlsGge.Schur.physicalFourier_star38,
      NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω]
    exact congrFun (congrFun hc true) m
  · apply NlsGge.ThirdConsultation.KST.KST033S.physical_ext
    intro m
    rw [NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω,
      NlsGge.ThirdConsultation.KST.KST033S.physicalFourier_smul,
      NlsGge.Schur.physicalFourier_star38,
      NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω]
    exact congrFun (congrFun hc false) m

theorem realForm_iff (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (y : Weighted ω) :
    RealForm ε (periodicPair (weightedPotential ω hω y)) ↔ weightedInvolution ω ε y = y := by
  have hεε : (ε : ℂ) * (ε : ℂ) = 1 := by rcases hε with rfl | rfl <;> simp
  have hc := involution_coeffs ω hev ε hε y
  constructor
  · rintro ⟨-, hF⟩
    have hF' : weightedPotential ω hω y false = (ε : ℂ) • star (weightedPotential ω hω y true) := hF
    have hfalse : ∀ m : ℤ, (y false : ℤ → ℂ) m = (ε : ℂ) * star ((y true : ℤ → ℂ) (-m)) := by
      intro m
      have := congrArg (fun f : PhysicalL2 => physicalFourier f m) hF'
      simp only at this
      rw [NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω,
        NlsGge.ThirdConsultation.KST.KST033S.physicalFourier_smul,
        NlsGge.Schur.physicalFourier_star38,
        NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω] at this
      exact this
    apply weighted_ext ω
    rw [hc]
    funext ch m
    cases ch
    · simp only [coefficientInvolution, weightedCoeffs, Bool.not_false]
      exact (hfalse m).symm
    · simp only [coefficientInvolution, weightedCoeffs, Bool.not_true]
      have h2 := hfalse (-m)
      rw [h2, star_mul', star_star, show star (ε : ℂ) = (ε : ℂ) by simp, ← mul_assoc, hεε, one_mul, neg_neg]
  · intro hI
    refine ⟨hε, ?_⟩
    show weightedPotential ω hω y false = (ε : ℂ) • star (weightedPotential ω hω y true)
    apply NlsGge.ThirdConsultation.KST.KST033S.physical_ext
    intro m
    rw [NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω,
      NlsGge.ThirdConsultation.KST.KST033S.physicalFourier_smul,
      NlsGge.Schur.physicalFourier_star38,
      NlsGge.ThirdConsultation.KST.KST033S.wp_fourier ω hω]
    have := congrFun (congrFun hc false) m
    rw [hI] at this
    exact this

theorem adaptedCoefficients_conj (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M) (hw : UnboundedWeight w)
    (N : ℕ) (hN : diagonalThreshold w M ≤ N) (φ ψ : Potential) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : ψ true = (ε : ℂ) • star (φ false)) (hF : ψ false = (ε : ℂ) • star (φ true))
    (hφ : φ ∈ physicalComponentBall w (2*M)) (hψ : ψ ∈ physicalComponentBall w (2*M)) :
    adaptedCoefficients N ψ = coefficientInvolution ε (adaptedCoefficients N φ) := by
  have hrT : ∀ m : ℤ, rawFourier ψ true m = (ε : ℂ) * star (rawFourier φ false (-m)) := by
    intro m
    unfold rawFourier
    rw [hT, NlsGge.ThirdConsultation.KST.KST033S.physicalFourier_smul,
      NlsGge.Schur.physicalFourier_star38]
  have hrF : ∀ m : ℤ, rawFourier ψ false m = (ε : ℂ) * star (rawFourier φ true (-m)) := by
    intro m
    unfold rawFourier
    rw [hF, NlsGge.ThirdConsultation.KST.KST033S.physicalFourier_smul,
      NlsGge.Schur.physicalFourier_star38]
  funext ch m
  by_cases hm : m.natAbs ≤ N
  · have hm' : (-m).natAbs ≤ N := by simpa using hm
    cases ch
    · simp only [adaptedCoefficients, coefficientInvolution, hm, hm', if_true, Bool.not_false]
      exact hrF m
    · simp only [adaptedCoefficients, coefficientInvolution, hm, hm', if_true, Bool.not_true]
      exact hrT m
  · have hm' : ¬ (-m).natAbs ≤ N := by simpa using hm
    have hth : diagonalThreshold w M ≤ m.natAbs := hN.trans (not_le.1 hm).le
    have hth' : diagonalThreshold w M ≤ (-m).natAbs := hN.trans (not_le.1 hm').le
    cases ch
    · simp only [adaptedCoefficients, coefficientInvolution, hm, hm', if_false, Bool.not_false,
        if_true, Bool.false_eq_true, neg_neg]
      rw [NlsGge.ThirdConsultation.KST.KST040S.b_conj_G φ ψ ε hε hT hF,
        NlsGge.ThirdConsultation.KST.KST040S.diagonalZero_conj w M hM hw φ ψ ε hε hT hF hφ hψ m hth,
        star_star]
    · simp only [adaptedCoefficients, coefficientInvolution, hm, hm', if_false, Bool.not_true,
        if_true, Bool.false_eq_true]
      rw [NlsGge.ThirdConsultation.KST.KST040S.c_conj_G φ ψ ε hε hT hF,
        NlsGge.ThirdConsultation.KST.KST040S.diagonalZero_conj w M hM hw φ ψ ε hε hT hF hφ hψ
          (-m) hth',
        star_star]

end Weighted

end KST040W

theorem kst040 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) (ε : ℝ)
    (hε : ε=1 ∨ ε=-1) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  let F := adaptedFourier ω hω (adaptedThreshold w M)
  let G := adaptedInverse ω hω M (adaptedThreshold w M)
  (∀ x ∈ componentBall ω M,
    weightedCoeffs ω (weightedInvolution ω ε x) =
      coefficientInvolution ε (weightedCoeffs ω x) ∧
    weightedInvolution ω ε x ∈ componentBall ω M ∧
    F (weightedInvolution ω ε x) = weightedInvolution ω ε (F x) ∧
    (RealForm ε (periodicPair (weightedPotential ω hω (F x))) ↔
      RealForm ε (periodicPair (weightedPotential ω hω x)))) ∧
  (∀ y ∈ F '' componentBall ω M,
    RealForm ε (periodicPair (weightedPotential ω hω y)) →
      RealForm ε (periodicPair (weightedPotential ω hω (G y)))) := by
  intro ω hω
  letI := weightFact ω hω
  intro F G
  have hM0 : 0 < M := by linarith
  have hw' : UnboundedWeight w := ⟨⟨hw.one_le, hw.even, hw.radial_mono⟩, hunbounded⟩
  have hev : ∀ k, ω (-k) = ω k := fun k => by
    show productWeight w v (-k) = productWeight w v k
    simp only [productWeight, hw.even, hv.1.2.1]
  have h38 : F 0 = 0 ∧ Set.InjOn F (componentBall ω M) ∧ _ ∧ _ :=
    kst038 w Cw M hM hw hunbounded v hv
  obtain ⟨-, hinj, -, -⟩ := h38
  obtain ⟨-, hcond, hmain⟩ := kst035 w Cw M hM hw hunbounded
  have hNd : diagonalThreshold w M ≤ adaptedThreshold w M := hcond.1
  have hball : ∀ x ∈ componentBall ω (2*M),
      weightedPotential ω hω x ∈ physicalComponentBall w (2*M) :=
    fun x hx => KST031S.ball_productWeight_subset w v hw.one_le hv.1.1 (2*M)
      (KST033S.wp_mem_ball ω hω x (2*M) hx)
  have hsub : ∀ x ∈ componentBall ω M, x ∈ componentBall ω (2*M) :=
    fun x hx ch => (hx ch).trans (by linarith)
  -- F commutes with the involution on the ball
  have hFI : ∀ x ∈ componentBall ω M,
      F (weightedInvolution ω ε x) = weightedInvolution ω ε (F x) := by
    intro x hx
    have hx2 := hsub x hx
    have hIx : weightedInvolution ω ε x ∈ componentBall ω M :=
      KST040W.involution_mem_ball ω hev ε hε M x hx
    have hIx2 := hsub _ hIx
    have hcx := (hmain v hv x hx2).1
    have hcIx := (hmain v hv _ hIx2).1
    obtain ⟨hT, hF⟩ := KST040W.wp_involution ω hω hev ε hε x
    have hconj := KST040W.adaptedCoefficients_conj w M hM hw' (adaptedThreshold w M) hNd
      (weightedPotential ω hω x) (weightedPotential ω hω (weightedInvolution ω ε x)) ε hε hT hF
      (hball x hx2) (hball _ hIx2)
    apply KST040W.weighted_ext ω
    rw [hcIx, hconj, KST040W.involution_coeffs ω hev ε hε (F x), hcx]
  -- real forms are exactly the fixed points of the involution
  have hRF : ∀ y : Weighted ω,
      RealForm ε (periodicPair (weightedPotential ω hω y)) ↔ weightedInvolution ω ε y = y :=
    fun y => KST040W.realForm_iff ω hω hev ε hε y
  have hiff : ∀ x ∈ componentBall ω M,
      (RealForm ε (periodicPair (weightedPotential ω hω (F x))) ↔
        RealForm ε (periodicPair (weightedPotential ω hω x))) := by
    intro x hx
    have hIx : weightedInvolution ω ε x ∈ componentBall ω M :=
      KST040W.involution_mem_ball ω hev ε hε M x hx
    rw [hRF, hRF, ← hFI x hx]
    constructor
    · intro h
      exact hinj hIx hx h
    · intro h
      rw [h]
  refine ⟨fun x hx => ⟨KST040W.involution_coeffs ω hev ε hε x,
    KST040W.involution_mem_ball ω hev ε hε M x hx, hFI x hx, hiff x hx⟩, ?_⟩
  intro y hy hry
  obtain ⟨x, hx, hxy⟩ := hy
  have hG : G y ∈ componentBall ω M ∧ F (G y) = y := by
    have hex : ∃ x' ∈ componentBall ω M, adaptedFourier ω hω (adaptedThreshold w M) x' = y :=
      ⟨x, hx, hxy⟩
    have hGeq : G y = Classical.choose hex := by
      show adaptedInverse ω hω M (adaptedThreshold w M) y = _
      unfold adaptedInverse
      rw [dif_pos hex]
    rw [hGeq]
    exact Classical.choose_spec hex
  obtain ⟨hGm, hGy⟩ := hG
  have := (hiff (G y) hGm).1
  rw [hGy] at this
  exact this hry

end NlsGge.ThirdConsultation.KST
end
