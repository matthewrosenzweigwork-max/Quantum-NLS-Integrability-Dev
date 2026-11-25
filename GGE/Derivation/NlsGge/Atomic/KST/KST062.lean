import Mathlib
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST035
import NlsGge.Atomic.KST.KST039
import NlsGge.Atomic.KST.KST040
import NlsGge.Atomic.KST.KST061
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST039Host
import NlsGge.ThirdConsultation.KST.KST040Host
import NlsGge.ThirdConsultation.KST.KST061Host
import NlsGge.ThirdConsultation.KST.KST062Host

/- KST-062 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST062.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-062"
   (identical in gpt6pro_followup9/10; no Pro round 11-12 entry touches KST-062).  No repair of the head.
   Route (source Corollary 1.1 density step; packet skeleton): F x lies in the open set F '' U (KST-039).  The exact
   symmetric truncations of F x converge to F x in Weighted omega (finite-mode projections), hence eventually lie in
   F '' U; the inverse G is applied only there, with F (G yJ) = yJ and G continuous at F x (analytic on F '' U), so
   G yJ -> G (F x) = x.  Truncation commutes with the real-form involution (coefficient level, |-m| = |m|), F x is
   real by KST-040, so yJ is real and G yJ is real by KST-040 (inverse preservation).  The adapted coefficients of
   G yJ are those of F (G yJ) = yJ (KST-035), which vanish for |m| > J > N, so KST-061 gives finitely many gaps.
   Supports: KST062Host (truncateCoefficients, truncateWeighted). -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

namespace KST062W

section Truncation

variable (ω : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]

theorem mem_symmetricModes_iff (J : ℕ) (m : ℤ) : m ∈ symmetricModes J ↔ m.natAbs ≤ J := by
  simp only [symmetricModes, Finset.mem_Icc]
  omega

/-- The componentwise finite-mode projection, as an element of `Weighted ω`. -/
def projLift (J : ℕ) (x : Weighted ω) : Weighted ω :=
  WithLp.toLp 2 (fun ch => weightedProjection (fun k => periodOneWeight ω k ^ 2) (symmetricModes J) (x ch))

theorem projLift_coeffs (J : ℕ) (x : Weighted ω) :
    weightedCoeffs ω (projLift ω J x) = truncateCoefficients J (weightedCoeffs ω x) := by
  funext ch m
  show ((weightedProjection (fun k => periodOneWeight ω k ^ 2) (symmetricModes J) (x ch) :
    WeightedHilbert (fun k => periodOneWeight ω k ^ 2)) : ℤ → ℂ) m = _
  rw [weightedProjection_apply]
  unfold truncateCoefficients weightedCoeffs
  by_cases h : m.natAbs ≤ J
  · rw [if_pos ((mem_symmetricModes_iff J m).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((mem_symmetricModes_iff J m).1 h')), if_neg h]

theorem truncateWeighted_coeffs (J : ℕ) (x : Weighted ω) :
    weightedCoeffs ω (truncateWeighted ω J x) = truncateCoefficients J (weightedCoeffs ω x) := by
  classical
  have hex : ∃ z : Weighted ω, weightedCoeffs ω z = truncateCoefficients J (weightedCoeffs ω x) :=
    ⟨projLift ω J x, projLift_coeffs ω J x⟩
  show weightedCoeffs ω (if h : ∃ z : Weighted ω, weightedCoeffs ω z =
      truncateCoefficients J (weightedCoeffs ω x) then Classical.choose h else 0) = _
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem truncateWeighted_eq_projLift (J : ℕ) (x : Weighted ω) :
    truncateWeighted ω J x = projLift ω J x :=
  KST040W.weighted_ext ω ((truncateWeighted_coeffs ω J x).trans (projLift_coeffs ω J x).symm)

theorem truncateWeighted_tendsto (x : Weighted ω) :
    Tendsto (fun J : ℕ => truncateWeighted ω J x) atTop (𝓝 x) := by
  have e : (fun J : ℕ => truncateWeighted ω J x) = fun J : ℕ => projLift ω J x :=
    funext fun J => truncateWeighted_eq_projLift ω J x
  rw [e]
  have h : Tendsto (fun J : ℕ => fun ch : Bool =>
      weightedProjection (fun k => periodOneWeight ω k ^ 2) (symmetricModes J) (x ch))
      atTop (𝓝 (fun ch : Bool => x ch)) :=
    tendsto_pi_nhds.2 fun ch => weightedProjection_tendsto _ (x ch)
  exact ((PiLp.continuous_toLp 2 (fun _ : Bool => WeightedHilbert (fun k => periodOneWeight ω k ^ 2))).tendsto
    _).comp h

theorem coefficientInvolution_truncate (ε : ℝ) (J : ℕ) (r : RawPair) :
    coefficientInvolution ε (truncateCoefficients J r) =
      truncateCoefficients J (coefficientInvolution ε r) := by
  funext ch m
  unfold coefficientInvolution truncateCoefficients
  have : (-m).natAbs = m.natAbs := Int.natAbs_neg m
  by_cases h : m.natAbs ≤ J
  · rw [if_pos (by rw [this]; exact h), if_pos h]
  · rw [if_neg (by rw [this]; exact h), if_neg h]
    simp

theorem truncate_involution_fixed (hev : ∀ k, ω (-k) = ω k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (J : ℕ) (x : Weighted ω) (hx : weightedInvolution ω ε x = x) :
    weightedInvolution ω ε (truncateWeighted ω J x) = truncateWeighted ω J x := by
  apply KST040W.weighted_ext ω
  rw [KST040W.involution_coeffs ω hev ε hε, truncateWeighted_coeffs,
    coefficientInvolution_truncate]
  congr 1
  rw [← KST040W.involution_coeffs ω hev ε hε x, hx]

end Truncation

end KST062W

theorem kst062 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) (ε : ℝ)
    (hε : ε=1 ∨ ε=-1) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  let N := adaptedThreshold w M
  let F := adaptedFourier ω hω N
  let G := adaptedInverse ω hω M N
  ∀ x ∈ componentOpenBall ω M,
    RealForm ε (periodicPair (weightedPotential ω hω x)) →
    (∃ J₀ : ℕ, N < J₀ ∧ ∀ J : ℕ, J₀ ≤ J →
      let yJ := truncateWeighted ω J (F x)
      weightedCoeffs ω yJ = truncateCoefficients J (weightedCoeffs ω (F x)) ∧
      yJ ∈ F '' componentOpenBall ω M ∧ G yJ ∈ componentOpenBall ω M ∧
      F (G yJ) = yJ ∧
      RealForm ε (periodicPair (weightedPotential ω hω (G yJ))) ∧
      pairFiniteGap (periodicPair (weightedPotential ω hω (G yJ)))) ∧
    Tendsto (fun J : ℕ => G (truncateWeighted ω J (F x))) atTop (𝓝 x) := by
  intro ω hω
  letI := weightFact ω hω
  intro N F G
  intro x hxU hxreal
  have hev : ∀ k, ω (-k) = ω k := fun k => by
    show productWeight w v (-k) = productWeight w v k
    simp only [productWeight, hw.even, hv.1.2.1]
  have h39 := kst039 w Cw M hM hw hunbounded v hv
  have hopen : IsOpen (F '' componentOpenBall ω M) := h39.2.1
  have hana : AnalyticOnNhd ℂ G (F '' componentOpenBall ω M) := h39.2.2.1
  have hleft : ∀ z ∈ componentOpenBall ω M, G (F z) = z := h39.2.2.2.1
  have hright : ∀ y ∈ F '' componentOpenBall ω M,
      G y ∈ componentOpenBall ω M ∧ F (G y) = y := h39.2.2.2.2
  obtain ⟨h40a, h40b⟩ := kst040 w Cw M hM hw hunbounded v hv ε hε
  have hmain35 := (kst035 w Cw M hM hw hunbounded).2.2 v hv
  have hsubU : ∀ z ∈ componentOpenBall ω M, z ∈ componentBall ω M := fun z hz ch => (hz ch).le
  have hxball : x ∈ componentBall ω M := hsubU x hxU
  -- F x is a real form, hence a fixed point of the involution
  have hFxreal : RealForm ε (periodicPair (weightedPotential ω hω (F x))) :=
    (h40a x hxball).2.2.2.2 hxreal
  have hFxfix : weightedInvolution ω ε (F x) = F x :=
    (KST040W.realForm_iff ω hω hev ε hε (F x)).1 hFxreal
  have hFxmem : F x ∈ F '' componentOpenBall ω M := ⟨x, hxU, rfl⟩
  have hT : Tendsto (fun J : ℕ => truncateWeighted ω J (F x)) atTop (𝓝 (F x)) :=
    KST062W.truncateWeighted_tendsto ω (F x)
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 (hT.eventually (hopen.mem_nhds hFxmem))
  refine ⟨⟨max J₁ (N + 1), lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _),
    fun J hJ => ?_⟩, ?_⟩
  · intro yJ
    have hJ1 : J₁ ≤ J := (le_max_left _ _).trans hJ
    have hJN : N < J := lt_of_lt_of_le (Nat.lt_succ_self N) ((le_max_right _ _).trans hJ)
    have hyJmem : yJ ∈ F '' componentOpenBall ω M := hJ₁ J hJ1
    obtain ⟨hGU, hFG⟩ := hright yJ hyJmem
    have hco : weightedCoeffs ω yJ = truncateCoefficients J (weightedCoeffs ω (F x)) :=
      KST062W.truncateWeighted_coeffs ω J (F x)
    have hyJfix : weightedInvolution ω ε yJ = yJ :=
      KST062W.truncate_involution_fixed ω hev ε hε J (F x) hFxfix
    have hyJreal : RealForm ε (periodicPair (weightedPotential ω hω yJ)) :=
      (KST040W.realForm_iff ω hω hev ε hε yJ).2 hyJfix
    have hyJball : yJ ∈ F '' componentBall ω M := by
      obtain ⟨z, hz, hzy⟩ := hyJmem
      exact ⟨z, hsubU z hz, hzy⟩
    have hGreal : RealForm ε (periodicPair (weightedPotential ω hω (G yJ))) :=
      h40b yJ hyJball hyJreal
    have hGball : G yJ ∈ componentBall ω M := hsubU _ hGU
    have hGball2 : G yJ ∈ componentBall ω (2*M) := fun ch => (hGball ch).trans (by linarith)
    have hphi : weightedPotential ω hω (G yJ) ∈ physicalComponentBall w M :=
      KST031S.ball_productWeight_subset w v hw.one_le hv.1.1 M
        (KST033S.wp_mem_ball ω hω (G yJ) M hGball)
    have hcoefG : weightedCoeffs ω (F (G yJ)) =
        adaptedCoefficients N (weightedPotential ω hω (G yJ)) :=
      (hmain35 (G yJ) hGball2).1
    rw [hFG] at hcoefG
    have hsupport : FiniteFourierSupport J (adaptedCoefficients N (weightedPotential ω hω (G yJ))) := by
      intro ch m hm
      rw [← hcoefG, hco]
      unfold truncateCoefficients
      rw [if_neg (not_le.2 hm)]
    have hgap := (kst061 w Cw M hM hw hunbounded (weightedPotential ω hω (G yJ)) hphi ε hGreal
      J hJN hsupport).2
    exact ⟨hco, hyJmem, hGU, hFG, hGreal, hgap⟩
  · have hGc : ContinuousAt G (F x) := (hana (F x) hFxmem).continuousAt
    have h := hGc.tendsto.comp hT
    rw [hleft x hxU] at h
    exact h

end NlsGge.ThirdConsultation.KST
end
