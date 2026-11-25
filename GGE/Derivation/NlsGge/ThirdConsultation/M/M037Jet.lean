import NlsGge.Atomic.M.M005
import NlsGge.ThirdConsultation.M.M037Bridge
import NlsGge.ThirdConsultation.M.Round5b

/- proof development M037Jet (SUPPORTING for the M-037 head; AUTHOR; not reviewed).
   Jet-level facts for the M-037 interpolation, built only from landed inputs:
   * conjugate and sup-norm bounds of the continuous jets (M005 sobolevJetContinuous);
   * the constant choice for periodic_GN (Round5b, M-036), one constant per derivative index;
   * the Hölder pair bound ∫ |F_a||F_b| ≤ ‖∂^{k_a}u‖ ‖∂^{k_b}u‖ using the landed L² bridge (constant 1).
   Totalization: all integrals are of continuous functions on the probability space; no series. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.HierarchyRiccati.Core
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.M.M037Jet

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The Boolean component `true` is the complex conjugate of `false` (M005 jet convention). -/
theorem sobolevJetContinuous_true_eq_star (m k : ℕ) (hk : k + 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    NlsGge.ThirdConsultation.M.sobolevJetContinuous m (true, k) u =
      star (NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u) := by
  unfold NlsGge.ThirdConsultation.M.sobolevJetContinuous
  rw [dif_pos (show (true, k).2 + 1 ≤ m from hk), dif_pos (show (false, k).2 + 1 ≤ m from hk)]
  all_goals rfl

/-- Pointwise norms of the two Boolean components agree. -/
theorem norm_jet_true_eq (m k : ℕ) (hk : k + 1 ≤ m) (u : NlsGge.ThirdConsultation.M.SobolevR m)
    (x : PhysicalCircle) :
    ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (true, k) u x‖ =
      ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u x‖ := by
  rw [sobolevJetContinuous_true_eq_star m k hk u]
  simp

/-- The false component is the M005 lower-jet continuous representative. -/
theorem sobolevJetContinuous_false_eq (m k : ℕ) (hk : k + 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u =
      riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m k hk
        (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates m u) := by
  unfold NlsGge.ThirdConsultation.M.sobolevJetContinuous
  rw [dif_pos (show (false, k).2 + 1 ≤ m from hk)]
  all_goals rfl

/-- Every pointwise value of a jet is bounded by the order-k sup norm `derivativeSupNorm`. -/
theorem norm_jet_le_sup (m : ℕ) (b : Bool) (k : ℕ) (hk : k + 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) (x : PhysicalCircle) :
    ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b, k) u x‖ ≤
      NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm k u := by
  have hS : NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm k u =
      ‖riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m k hk
        (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates m u)‖ := by
    unfold NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm
    rw [dif_pos hk]
    rfl
  rw [hS]
  cases b with
  | false =>
    rw [← sobolevJetContinuous_false_eq m k hk u]
    exact ContinuousMap.norm_coe_le_norm _ x
  | true =>
    rw [norm_jet_true_eq m k hk u x, ← sobolevJetContinuous_false_eq m k hk u]
    exact ContinuousMap.norm_coe_le_norm _ x

/-- The lowered Sobolev cast of the periodic_GN statement agrees with the M005 cast. -/
theorem lowerCast_eq (m k : ℕ) (hk : k ≤ m) (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    NlsGge.ThirdConsultation.MRiccati.lowerSobolevCast k m u =
      NlsGge.ThirdConsultation.M.lowerSobolevCast k m hk u := by
  unfold NlsGge.ThirdConsultation.MRiccati.lowerSobolevCast
  rw [dif_pos hk]

/-- One constant per derivative index: the sup and L² bounds of periodic_GN (M-036) for index k < m,
   with a constant C k ≥ 0 that does not depend on u. -/
theorem gn_const (m : ℕ) (hm : 0 < m) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ k, k < m →
      (∀ u : NlsGge.ThirdConsultation.M.SobolevR m,
        NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm k u ≤
          C k * ‖u‖ ^ (((k : ℝ) + (1/2 : ℝ)) / (m : ℝ)) *
            ‖NlsGge.ThirdConsultation.M.physicalOfSobolev u‖ ^
              (1 - ((k : ℝ) + (1/2 : ℝ)) / (m : ℝ))) ∧
      (∀ u : NlsGge.ThirdConsultation.M.SobolevR m,
        ‖physicalSobolevDerivative38 k
            (NlsGge.ThirdConsultation.MRiccati.lowerSobolevCast k m u)‖ ≤
          C k * ‖u‖ ^ ((k : ℝ) / (m : ℝ)) *
            ‖NlsGge.ThirdConsultation.M.physicalOfSobolev u‖ ^ (1 - (k : ℝ) / (m : ℝ))) := by
  have h : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ (k < m →
      (∀ u : NlsGge.ThirdConsultation.M.SobolevR m,
        NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm k u ≤
          c * ‖u‖ ^ (((k : ℝ) + (1/2 : ℝ)) / (m : ℝ)) *
            ‖NlsGge.ThirdConsultation.M.physicalOfSobolev u‖ ^
              (1 - ((k : ℝ) + (1/2 : ℝ)) / (m : ℝ))) ∧
      (∀ u : NlsGge.ThirdConsultation.M.SobolevR m,
        ‖physicalSobolevDerivative38 k
            (NlsGge.ThirdConsultation.MRiccati.lowerSobolevCast k m u)‖ ≤
          c * ‖u‖ ^ ((k : ℝ) / (m : ℝ)) *
            ‖NlsGge.ThirdConsultation.M.physicalOfSobolev u‖ ^ (1 - (k : ℝ) / (m : ℝ)))) := by
    intro k
    by_cases hk : k < m
    · obtain ⟨c, hc, hb⟩ := NlsGge.ThirdConsultation.M.periodic_GN m k hm hk
      exact ⟨c, hc.le, fun _ => ⟨fun u => (hb u).1, fun u => (hb u).2 k hk.le⟩⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hk⟩
  choose C hC0 hCb using h
  exact ⟨C, hC0, fun k hk => hCb k hk⟩

/-- Hölder pair bound for two jets of order ≤ m-1, using the landed L² bridge (constant 1). -/
theorem jet_pair_integral_le (m : ℕ) (b₁ b₂ : Bool) (k₁ k₂ : ℕ) (h₁ : k₁ + 1 ≤ m) (h₂ : k₂ + 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    ∫ x : PhysicalCircle,
        ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b₁, k₁) u x‖ *
          ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b₂, k₂) u x‖ ∂spatialMeasure ≤
      ‖physicalSobolevDerivative38 k₁
          (NlsGge.ThirdConsultation.M.lowerSobolevCast k₁ m (by omega) u)‖ *
        ‖physicalSobolevDerivative38 k₂
          (NlsGge.ThirdConsultation.M.lowerSobolevCast k₂ m (by omega) u)‖ := by
  have hmem : ∀ (b : Bool) (k : ℕ),
      MemLp (fun x : PhysicalCircle => NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b, k) u x)
        (ENNReal.ofReal 2) spatialMeasure := by
    intro b k
    exact MemLp.of_bound
      (NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b, k) u).continuous.aestronglyMeasurable
      ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b, k) u‖
      (ae_of_all _ fun x => ContinuousMap.norm_coe_le_norm _ x)
  have key := integral_mul_norm_le_Lp_mul_Lq (μ := spatialMeasure) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (hmem b₁ k₁) (hmem b₂ k₂)
  simp only [Real.rpow_two] at key
  rw [NlsGge.ThirdConsultation.M.M037Bridge.sobolevJetContinuous_sq_integral m k₁ h₁ b₁ u,
    NlsGge.ThirdConsultation.M.M037Bridge.sobolevJetContinuous_sq_integral m k₂ h₂ b₂ u] at key
  simp only [← Real.sqrt_eq_rpow] at key
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at key
  exact key

end NlsGge.ThirdConsultation.M.M037Jet
