import Mathlib
import Armstrong.Work.CartesianTerminalRootSpec
import NlsGge.GK38.TauGamma
import NlsGge.Atomic.G4.G4029
import NlsGge.Atomic.G4.G4030

/- G4-031 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4031.lean.
   Head `G4031`: design STATEMENTS/G4.md G4-031 section, verbatim (byte-identical in followup1..10 STATEMENTS; no Pro round entry or
   BINDING_INDEX touches G4-031; no lexical repair: the head has no `lambda` binder, `lamPlus`/`lamMinus` are the landed GK38 names).
   Route (G4031_ROUTE.md): the landed `cartesianZExtended` is the continued formula (2(tau-mu)+2aT) exp(-a T oc) with T = terminalRoot,
   oc = ownCorrection at mu. (1) prefactor bound: Armstrong.Work.CartesianTerminalRootSpec.gk16_terminal_prefactors_norm38 (X-006 closure,
   already imported by landed KSN002) + gamma2 = (lamPlus - lamMinus)^2; (2) T^2 = L^2 = (mu-lamMinus)(mu-lamPlus) where L =
   localRootAtDirichlet (gk16_terminal_root_sq38 and slitRoot_sq of landed G4029), so T = +-L; (3) regularEtaIntegral + constantEtaCorrection
   = L * oc, so the exponential is exp(s (reg+const)), s = +-1, bounded by landed G4-030. No analytic anchor used. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4031Aux

/-- The local root at the Dirichlet point squares to `(mu - lamMinus)(mu - lamPlus)`. -/
theorem localRoot_sq (n : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) :
    (localRootAtDirichlet n φ) ^ 2 =
      (muSeq φ n - lamMinus φ n) * (muSeq φ n - lamPlus φ n) := by
  have hτ := tauN_value38 φ hgk n
  unfold localRootAtDirichlet
  by_cases h : lamPlus φ n = lamMinus φ n
  · rw [dif_pos h, hτ, h]
    ring
  · rw [dif_neg h]
    have hg : lamPlus φ n - lamMinus φ n ≠ 0 := sub_ne_zero.2 h
    rw [mul_pow, G4029Aux.slitRoot_sq, hτ]
    field_simp
    ring

/-- The terminal root is `+-` the local root at the Dirichlet point. -/
theorem terminalRoot_eq_pm (n : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) :
    terminalRoot n φ = localRootAtDirichlet n φ ∨
      terminalRoot n φ = -localRootAtDirichlet n φ := by
  have hT : (terminalRoot n φ) ^ 2 =
      (muSeq φ n - lamMinus φ n) * (muSeq φ n - lamPlus φ n) :=
    gk16_terminal_root_sq38 n φ hgk
  have hL := localRoot_sq n φ hgk
  exact sq_eq_sq_iff_eq_or_eq_neg.1 (hT.trans hL.symm)

/-- Unified form of the continued Cartesian exponential for `a = +-1`. -/
theorem cartesianZ_unified (n a : ℤ) (ha : a = 1 ∨ a = -1) (φ : PotPair) :
    cartesianZExtended n a φ =
      (2 * (tauN φ n - muSeq φ n) + 2 * (a : ℂ) * terminalRoot n φ) *
        Complex.exp (-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))) := by
  rcases ha with rfl | rfl
  · simp [cartesianZExtended]
  · have : ¬ ((-1 : ℤ) = 1) := by norm_num
    simp [cartesianZExtended, this, sub_eq_add_neg]

/-- Norm of the algebraic prefactor, in the gap and displacement scales. -/
theorem prefactor_norm (n a : ℤ) (ha : a = 1 ∨ a = -1) (φ : PotPair) (hgk : φ ∈ gkW) :
    ‖2 * (tauN φ n - muSeq φ n) + 2 * (a : ℂ) * terminalRoot n φ‖ ≤
      4 * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
  have hpf := gk16_terminal_prefactors_norm38 n φ hgk
  have hsq : Real.sqrt ‖gamma2 φ n‖ = ‖lamPlus φ n - lamMinus φ n‖ := by
    rw [gamma2_value38 φ hgk n, norm_pow]
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hsq] at hpf
  have hg := norm_nonneg (lamPlus φ n - lamMinus φ n)
  rcases ha with rfl | rfl
  · have h1 := hpf.1
    have e : 2 * (tauN φ n - muSeq φ n) + 2 * (((1 : ℤ) : ℂ)) * terminalRoot n φ =
        2 * (tauN φ n - muSeq φ n) + 2 * gk16TerminalRoot38 n φ := by
      simp [terminalRoot, gk16TerminalRoot38]
    rw [e]
    linarith
  · have h1 := hpf.2
    have e : 2 * (tauN φ n - muSeq φ n) + 2 * (((-1 : ℤ) : ℂ)) * terminalRoot n φ =
        2 * (tauN φ n - muSeq φ n) - 2 * gk16TerminalRoot38 n φ := by
      simp [terminalRoot, gk16TerminalRoot38]
      ring
    rw [e]
    linarith

end G4031Aux

theorem G4031 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧
  ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ V, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
    ‖cartesianZExtended n a φ‖ ≤
      C * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
  obtain ⟨V, hVn, hVS, C0, hC0, hbd⟩ := G4030 φ₀ hφ₀
  refine ⟨V, hVn, hVS, 4 * C0, by positivity, fun φ hφ n a ha => ?_⟩
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W (hVS hφ))
  set L := localRootAtDirichlet n φ with hLdef
  set oc := ownCorrection n φ (muSeq φ n) with hoc
  have hX : regularEtaIntegral n φ + constantEtaCorrection n φ = L * oc := by
    unfold regularEtaIntegral
    ring
  -- the exponent is `s * (reg + const)` for some `s = +-1`
  have hexp : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      -((a : ℂ) * terminalRoot n φ * oc) =
        (s : ℂ) * (regularEtaIntegral n φ + constantEtaCorrection n φ) := by
    rw [hX]
    rcases G4031Aux.terminalRoot_eq_pm n φ hgk with hT | hT <;> rcases ha with rfl | rfl
    · exact ⟨-1, Or.inr rfl, by rw [hT]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [hT]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [hT]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [hT]; push_cast; ring⟩
  obtain ⟨s, hs, hsE⟩ := hexp
  have hE := hbd φ hφ n s hs
  rw [G4031Aux.cartesianZ_unified n a ha φ, norm_mul, ← hoc, hsE]
  have hP := G4031Aux.prefactor_norm n a ha φ hgk
  have hP0 := norm_nonneg (2 * (tauN φ n - muSeq φ n) + 2 * (a : ℂ) * terminalRoot n φ)
  calc ‖2 * (tauN φ n - muSeq φ n) + 2 * (a : ℂ) * terminalRoot n φ‖ *
        ‖Complex.exp ((s : ℂ) * (regularEtaIntegral n φ + constantEtaCorrection n φ))‖
      ≤ (4 * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖)) * C0 :=
        mul_le_mul hP hE (norm_nonneg _) (by positivity)
    _ = 4 * C0 * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by ring

end
end NlsGge.GKDefinitionDesign
