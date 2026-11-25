import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.NLS38.LaxConsequences38
import NlsGge.NLS38.ClassicalSolution38
import NlsGge.Birkhoff.S04FiniteGapInvariance38

/-! # Regularity and first variation for the actual finite-gap NLS flow

These are intermediate lemmas for the native flow-rotation route. The Birkhoff
map and NLS flow are the existing concrete maps, with the reflected Fourier
convention of `fourierSeq38`. No rotation or Hamiltonian-transport input is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38

/-- Every physical field whose actual Birkhoff coordinates have finite support
belongs to every integer physical Sobolev space, including level zero. -/
theorem finiteSupport_physicalSobolev_all38 (u : PhysicalL2)
    (hfin : {n : ℤ | (B0).Φ u n ≠ 0}.Finite) :
    ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u) := by
  intro m
  have hz := finiteSupport_mem_seqSobolev38 (m : ℝ) ((B0).Φ u) hfin
  have h := (B0).sobolev_Φinv m ((B0).Φ u) hz
  rw [(B0).Φinv_Φ u] at h
  exact h

/-- For any physical H³ initial field, every actual Birkhoff coordinate has
constant squared norm under the actual NLS flow, at every real time. -/
theorem actualPhi_normSq_nlsFlow38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 3 (physicalFourier u)) (t : ℝ) (n : ℤ) :
    ‖(B0).Φ (nlsFlowL2 t u) n‖ ^ 2 = ‖(B0).Φ u n‖ ^ 2 := by
  rw [(B0).sq_norm_Φ_eq_action_L2, (B0).sq_norm_Φ_eq_action_L2]
  exact actualGapActionAllE02_38_nlsFlow u hu t n

/-- For every physical field with finite actual Birkhoff support, that support
is exactly preserved by the actual NLS flow for every real time. -/
theorem actualPhi_support_nlsFlow38 (u : PhysicalL2)
    (hfin : {n : ℤ | (B0).Φ u n ≠ 0}.Finite) (t : ℝ) :
    {n : ℤ | (B0).Φ (nlsFlowL2 t u) n ≠ 0} = {n : ℤ | (B0).Φ u n ≠ 0} := by
  have hu := finiteSupport_physicalSobolev_all38 u hfin 3
  have heq := actualPhi_normSq_nlsFlow38 u hu t
  ext n
  have hnorm : ‖(B0).Φ (nlsFlowL2 t u) n‖ = ‖(B0).Φ u n‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (heq n)
  constructor
  · intro h hz
    apply h
    apply norm_eq_zero.mp
    rw [hnorm, hz, norm_zero]
  · intro h hz
    apply h
    apply norm_eq_zero.mp
    rw [← hnorm, hz, norm_zero]

/-- An h³ sequence datum has an h¹-carrier NLS trajectory and an h¹-carrier
velocity at every real time. Their underlying sequences are the actual flow
and its uncut NLS right-hand side, respectively. -/
theorem nlsFlowSeq_hasDerivAt_H1_38 (x : ℤ → ℂ)
    (hx : x ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    ∃ γ D : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ),
      (∀ t, carrierCoe38 _ (γ t) = nlsFlowSeq t x) ∧
      (∀ t, HasDerivAt γ (D t) t) ∧
      (∀ t, carrierCoe38 _ (D t) = rhsSeq (nlsFlowSeq t x)) := by
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    seqSobolev38_mono (by norm_num) hx
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx1
  have hR : 0 < Bx x + 2 := by linarith [Bx_nonneg38 x]
  have hc : IsCutSol (Bx x + 2) (fun t => nlsFlowSeq t x) :=
    nlsSol_isCutSol38 hs (by rw [h0]; linarith)
  obtain ⟨γ, hγ, hd⟩ := cutSol_C1_h1_aux hR hc (by rw [h0]; exact hx)
  choose D hD hDc using hd
  refine ⟨γ, D, hγ, hD, fun t => ?_⟩
  rw [hDc t, flow_cutoff_eq_one38 hx1 t]
  simp only [Complex.ofReal_one, one_mul]
  rfl

/-- For every physical H³ datum, its actual Birkhoff trajectory is represented
by a differentiable curve in the h¹ carrier, with equality at every real time. -/
theorem actualPhi_nlsFlow_differentiable_H1_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 3 (physicalFourier u)) :
    ∃ z : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ),
      (∀ t, carrierCoe38 _ (z t) = (B0).Φ (nlsFlowL2 t u)) ∧ Differentiable ℝ z := by
  have hx3 : fourierSeq38 u ∈ seqSobolev38 ((3 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff _ u).2 hu
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) :=
    (fourierSeq38_mem_iff _ u).1 (seqSobolev38_mono (by norm_num) hx3)
  obtain ⟨γ, D, hγ, hD, -⟩ := nlsFlowSeq_hasDerivAt_H1_38 (fourierSeq38 u) hx3
  refine ⟨fun t => (B0).TC 1 (γ t), fun t => ?_, ?_⟩
  · rw [BirkhoffTop38.TC_coe, hγ t, ← fourierSeq38_nlsFlowL2 hu1 t]
    rfl
  · have hT : Differentiable ℝ ((B0).TC 1) := fun x =>
      (NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.analyticOnNhd_TC 1 x
        (Set.mem_univ x)).differentiableAt
    exact hT.comp (fun t => (hD t).differentiableAt)

/-- Along any h¹-carrier curve differentiable at a real time, the derivative
of the NLS Hamiltonian is the sum of the kinetic and quartic first variations,
with the exact factor two and the existing dispersion and cubic nonlinearity. -/
theorem hasDerivAt_ham_curve38 (γ : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ))
    (D : SobolevCarrier38 ((1 : ℕ) : ℝ)) (t : ℝ) (h : HasDerivAt γ D t) :
    HasDerivAt (fun s => ham (carrierCoe38 _ (γ s)))
      (2 * (∑' n : ℤ, ((disp n : ℝ) : ℂ) *
        (starRingEnd ℂ (carrierCoe38 _ (γ t) n) * carrierCoe38 _ D n)).re +
       2 * (∑' n : ℤ, starRingEnd ℂ (nonlin (carrierCoe38 _ (γ t)) n) *
        carrierCoe38 _ D n).re) t := by
  exact (hasDerivAt_kin h).add (hasDerivAt_quart h)

/-- The finite-plane Hamiltonian HΛ is the literal physical Q₂ energy of the
actual inverse Birkhoff field whose coordinates are `w` on `Λ` and zero elsewhere.
It uses the full NLS Hamiltonian, without a cutoff or a factor of one half. -/
def HΛ (Λ : Finset ℤ) (w : Λ → ℂ) : ℝ :=
  ham (physicalFourier ((B0).finiteGapField38 Λ w))

end LiebLiniger.FixedPeriod.EXT
