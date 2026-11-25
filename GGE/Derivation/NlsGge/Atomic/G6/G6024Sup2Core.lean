import Mathlib
import NlsGge.Atomic.G6.G6024Sup1Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff
import NlsGge.Atomic.KSN.KSN018Host

/- G6024 SUP2 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6024Sup2Core.lean, namespace NlsGge.ThirdConsultation.G6024S.
   SUPPORT (no packet increment) for G6-024: the raw carrier equality (earned before any analytic statement, as Pro r15
   Q6 requires) and the positive-level real analyticity of birkhoffSobolev m, from:
   * hmemB = exact type of the landed birkhoffSobolev_mem (SobolevBirkhoffCompat);
   * hSR = exact type of the landed KSN001Aux.scalarBirkhoff_realSlice (physicalBirkhoff u n = scalarBirkhoff true n (realSlice u));
   * hK19 = the first two conjuncts of the KSN-019 head body at N = m (complex analyticity of complexSmoothing on
     complexDomain, membership, coordinates).
   Identity: with z = F u (Fourier equivalence) and v = physicalSobolevEmbed m u,
     pairPotential m (toPair m z) = realSlice v,   physicalBirkhoff v n = smoothingCoefficient m (toPair z) true n + z_n,
     birkhoffSobolev m u = F u + fromPair m (complexSmoothing m (toPair m (F u))).
   Analyticity: complexSmoothing is ℂ-analytic at the real point toPair (F u) ∈ complexDomain (V_real), restricted to ℝ
   (AnalyticAt.restrictScalars) and composed with the real continuous linear maps. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSN

namespace NlsGge.ThirdConsultation.G6024S
noncomputable section

theorem fourierSeq38_eq (v : PhysicalL2) (n : ℤ) : fourierSeq38 v n = -physicalFourier v (-n) := by
  unfold fourierSeq38
  rw [reflectedFourierL2_apply]
  rfl

theorem pf_eq (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) (k : ℤ) :
    physicalFourier (physicalSobolevEmbed m u) k =
      -carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-k) := by
  rw [← physicalSobolevEmbed_fourier, fourierSeq38_eq, neg_neg, neg_neg]

theorem raw_toPair (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) (b : Bool) (k : ℤ) :
    rawCoefficient (m : ℝ) (toPair m z) b k =
      (if b then -carrierCoe38 (m : ℝ) z (-k) else -star (carrierCoe38 (m : ℝ) z k)) := by
  unfold rawCoefficient
  rw [toPair_apply]
  unfold pairFun
  have h : ((scaleWeight (m : ℝ) k : ℝ) : ℂ) ≠ 0 := by
    have : 0 < scaleWeight (m : ℝ) k := by
      rw [sw_eq]; exact pow_pos (lt_of_lt_of_le one_pos (bracket_one_le _)) _
    exact_mod_cast this.ne'
  field_simp

theorem pairPotential_toPair (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    pairPotential (m : ℝ) (Nat.cast_nonneg m) (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u)) =
      realSlice (physicalSobolevEmbed m u) := by
  rw [realSlice_apply]
  unfold pairPotential
  refine Prod.ext ?_ ?_
  · show physicalFourierL2.symm _ = _
    rw [LinearIsometryEquiv.symm_apply_eq]
    ext k
    rw [physicalFourierL2_apply]
    show rawCoefficient (m : ℝ) _ true k = _
    rw [raw_toPair, pf_eq]
    rfl
  · show physicalFourierL2.symm _ = _
    rw [LinearIsometryEquiv.symm_apply_eq]
    ext k
    rw [physicalFourierL2_apply]
    show rawCoefficient (m : ℝ) _ false k = _
    rw [raw_toPair, NlsGge.ThirdConsultation.KSN.sup4_physicalFourier_star, pf_eq, neg_neg]
    simp

theorem toPair_mem_complexDomain (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u) ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m) := by
  show pairPotential (m : ℝ) (Nat.cast_nonneg m) _ ∈ sourceBetaW
  rw [pairPotential_toPair]
  exact sourceFamily.V_real ⟨_, rfl⟩

/-- Raw carrier equality: physicalBirkhoff = Fourier + smoothing (true component). -/
theorem birkhoff_coord (m : ℕ) (u : PhysicalSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n) (n : ℤ) :
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) n =
      carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) n +
        smoothingCoefficient m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u)) true n := by
  rw [← hSR, ← pairPotential_toPair]
  unfold smoothingCoefficient
  simp only [↓reduceIte]
  rw [raw_toPair]
  simp only [↓reduceIte, neg_neg]
  ring

theorem birkhoffSobolev_eq (m : ℕ)
    (hmemB : ∀ u : PhysicalSobolev38 (m : ℝ),
      (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hmem : ∀ x ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m),
      Memℓp (storedSequence ((m : ℝ) + 1) (smoothingCoefficient m x)) 2)
    (u : PhysicalSobolev38 (m : ℝ)) :
    birkhoffSobolev m u = physicalSobolevFourierEquiv38 (m : ℝ) u +
      fromPair m (complexSmoothing m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))) := by
  have hx := toPair_mem_complexDomain m u
  apply carrierExt38
  funext n
  rw [carrierCoe38_add, fromPair_coe]
  unfold birkhoffSobolev
  simp only []
  rw [dif_pos (hmemB u), carrierCoe38_mk, birkhoff_coord m u hSR n]
  congr 1
  have hcs : complexSmoothing m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u)) =
      ⟨storedSequence ((m : ℝ) + 1) (smoothingCoefficient m _), hmem _ hx⟩ := by
    unfold complexSmoothing sequenceLift
    rw [dif_pos (hmem _ hx)]
  have hw : ((scaleWeight ((m + 1 : ℕ) : ℝ) n : ℝ) : ℂ) ≠ 0 := by
    have : 0 < scaleWeight ((m + 1 : ℕ) : ℝ) n := by
      rw [sw_eq]; exact pow_pos (lt_of_lt_of_le one_pos (bracket_one_le _)) _
    exact_mod_cast this.ne'
  rw [hcs]
  show _ = storedSequence ((m : ℝ) + 1) (smoothingCoefficient m _) (true, n) / _
  unfold storedSequence
  rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring]
  field_simp

/-- Positive-level real analyticity of birkhoffSobolev m. -/
theorem birkhoffSobolev_analytic_of (m : ℕ)
    (hmemB : ∀ u : PhysicalSobolev38 (m : ℝ),
      (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hA : AnalyticOnNhd ℂ (complexSmoothing m) (complexDomain (m : ℝ) (Nat.cast_nonneg m)))
    (hmem : ∀ x ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m),
      Memℓp (storedSequence ((m : ℝ) + 1) (smoothingCoefficient m x)) 2) :
    AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ := by
  intro u _
  have heq : birkhoffSobolev m = fun u => physicalSobolevFourierEquiv38 (m : ℝ) u +
      fromPair m (complexSmoothing m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))) :=
    funext (birkhoffSobolev_eq m hmemB hSR hmem)
  rw [heq]
  have hF : AnalyticAt ℝ (fun u => physicalSobolevFourierEquiv38 (m : ℝ) u) u :=
    (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt u
  have hT : AnalyticAt ℝ (fun u => toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u)) u :=
    ((toPair m).comp (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap).analyticAt u
  have hC : AnalyticAt ℝ (complexSmoothing m) (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u)) :=
    (hA _ (toPair_mem_complexDomain m u)).restrictScalars
  have hP : AnalyticAt ℝ (fun y => fromPair m y)
      (complexSmoothing m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))) :=
    (fromPair m).analyticAt _
  have hCT : AnalyticAt ℝ (fun u => complexSmoothing m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))) u :=
    AnalyticAt.comp (g := complexSmoothing m)
      (f := fun u => toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u)) hC hT
  exact hF.add (AnalyticAt.comp (g := fun y => fromPair m y)
    (f := fun u => complexSmoothing m (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))) hP hCT)

end
end NlsGge.ThirdConsultation.G6024S
