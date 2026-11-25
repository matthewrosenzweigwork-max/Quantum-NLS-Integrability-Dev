import Mathlib
import NlsGge.Birkhoff.S04Moments38e
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Birkhoff.F05Identity38

/- I030CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/ThirdConsultation/I/I030Core.lean, namespace NlsGge.ThirdConsultation.I030Aux.
   Lane-checked conditional core for I-030 (pattern of I029Core.i029_of): the three I-030 clauses for an arbitrary
   BirkhoffTop38 B with BirkhoffMolnar38 B and any measure μ with B.muW38 c.val = μ.  The glue I030 instantiates
   B := PDE.actualBirkhoffTop38, hM := PDE.actualBirkhoffMolnar38, μ := physicalLaw (weight c.val) via
   actual_ensemble_eq_I (actualMuW = physicalLaw; actualMuW is definitionally actualBirkhoffTop38.muW38).
   Clause 1: landed chargeSobolev_poly_bound38 (j+2) j, with ‖ofCarrier38 (physC38 (j+1) u)‖ = ‖physH38 (j+1) u‖
     (norm_physC38_eq_physH38) = ‖physFS38 (j+1) u‖ (norm_reflC38); constant A+1 > 0, degree 2(j+2)+2.
   Clause 2 (Pro r17 Q3: real exponents kept; natural producer via f^q ≤ 1 + f^p, p = ⌈q⌉₊): landed
     integrable_muW38_charge_pow at p, Integrable.mono' with measurability earned first (continuous_chargeSobolev38).
   Clause 3: ONE smooth representative for all j: landed ae_muW38_allSobolev + exists_smooth_rep38, then
     chargeSobolev38_smooth (j+2) j for that same U (the body of landed ae_muW38_chargeFn_eq, repeated with U fixed
     across j so no per-j choice is compared).
   One file-local IsProbabilityMeasure spatialMeasure instance, identical to landed S04Moments38e l.22.
   No definition is missing.  Own imports: Mathlib, Birkhoff/S04Moments38e, H03Diagonal38b, F05Identity38. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.HierarchyRiccati.Core

/-- Same file-local instance as landed S04Moments38e l.22 / ChargeJensenSobolev38 l.30 (needed by
`ContinuousMap.toLp 2 spatialMeasure` in the clause-3 source identification). -/
local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.ThirdConsultation.I030Aux

/-- `f ^ q ≤ 1 + f ^ ⌈q⌉₊` for `f ≥ 0`, `q ≥ 0`. -/
theorem rpow_le_one_add_pow_ceil (f q : ℝ) (hf : 0 ≤ f) (hq : 0 ≤ q) :
    f ^ q ≤ 1 + f ^ (⌈q⌉₊ : ℕ) := by
  rcases le_total f 1 with h1 | h1
  · have : f ^ q ≤ 1 := Real.rpow_le_one hf h1 hq
    have h2 : 0 ≤ f ^ (⌈q⌉₊ : ℕ) := pow_nonneg hf _
    linarith
  · have : f ^ q ≤ f ^ ((⌈q⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil q)
    rw [Real.rpow_natCast] at this
    linarith

/-- ‖physFS38 r u‖ = ‖physH38 r u‖ (reflection is an isometry). -/
theorem norm_physFS38_eq (r : ℕ) (u : PhysicalL2) : ‖physFS38 r u‖ = ‖physH38 r u‖ := by
  unfold physFS38
  exact norm_reflC38 _ _

theorem i030_of (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (B : BirkhoffTop38) (hM : BirkhoffMolnar38 B) (μ : Measure PhysicalL2) (hμ : B.muW38 c.val = μ) :
    (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ u : PhysicalL2, SobolevSquareSummable ((j + 1 : ℕ) : ℝ) (physicalFourier u) →
        |chargeFn38 (j + 2) j u| ≤ C * (1 + ‖physFS38 (j + 1) u‖) ^ d) ∧
    (∀ (j : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun u : PhysicalL2 => |chargeFn38 (j + 2) j u| ^ q) μ) ∧
    (∀ᵐ u ∂μ,
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u ∧
        ∀ j : ℕ, chargeFn38 (j + 2) j u = localCharge38 U j) := by
  obtain ⟨hlower, -, hc⟩ := c.property
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (hc j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (hc j).2
  subst hμ
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1: deterministic polynomial growth
    intro j
    obtain ⟨A, hA0, hAb⟩ := chargeSobolev_poly_bound38 (j + 2) j (by omega)
    refine ⟨A + 1, by linarith, 2 * (j + 2) + 2, fun u _ => ?_⟩
    have h1 := hAb (ofCarrier38 ((j + 2 - 1 : ℕ) : ℝ) (physC38 (j + 2 - 1) u))
    have ht : ‖ofCarrier38 ((j + 2 - 1 : ℕ) : ℝ) (physC38 (j + 2 - 1) u)‖ = ‖physFS38 (j + 1) u‖ :=
      (norm_physC38_eq_physH38 (j + 1) u).trans (norm_physFS38_eq (j + 1) u).symm
    rw [ht] at h1
    have hp : 0 ≤ (1 + ‖physFS38 (j + 1) u‖) ^ (2 * (j + 2) + 2) := by positivity
    calc |chargeFn38 (j + 2) j u| ≤ A * (1 + ‖physFS38 (j + 1) u‖) ^ (2 * (j + 2) + 2) := h1
      _ ≤ (A + 1) * (1 + ‖physFS38 (j + 1) u‖) ^ (2 * (j + 2) + 2) := by nlinarith
  · -- clause 2: all real moments, from the natural moment at ⌈q⌉₊
    intro j q hq
    have := B.isProbabilityMeasure_muW38 lower upper c.val hlower hbound hupper
    let _ : MeasurableSpace (SobolevCarrier38 ((j + 2 - 1 : ℕ) : ℝ)) := borel _
    have : BorelSpace (SobolevCarrier38 ((j + 2 - 1 : ℕ) : ℝ)) := ⟨rfl⟩
    let _ : MeasurableSpace (SobolevHilbert ((j + 2 - 1 : ℕ) : ℝ)) := borel _
    have : BorelSpace (SobolevHilbert ((j + 2 - 1 : ℕ) : ℝ)) := ⟨rfl⟩
    have hmeas : Measurable (fun u : PhysicalL2 => |chargeFn38 (j + 2) j u| ^ q) := by
      have h1 : Measurable (fun u : PhysicalL2 => chargeFn38 (j + 2) j u) :=
        (continuous_chargeSobolev38 (j + 2) j (by omega)).measurable.comp
          ((continuous_ofCarrier38 _).measurable.comp (measurable_physC38 (j + 2 - 1)))
      exact h1.abs.pow_const q
    have hp := B.integrable_muW38_charge_pow lower upper c.val hlower hbound hupper hM (j + 2) j
      (by omega) ⌈q⌉₊
    refine ((integrable_const (1 : ℝ)).add hp).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact rpow_le_one_add_pow_ceil _ q (abs_nonneg _) hq
  · -- clause 3: one smooth representative identifies every charge
    filter_upwards [B.ae_muW38_allSobolev lower upper c.val hlower hbound hupper] with u hu
    obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 u hu
    refine ⟨U, hU, hper, hUu, fun j => ?_⟩
    have hmem : (fun n => physicalFourier u n) ∈ seqSobolev38 (((j + 2 - 1 : ℕ) : ℝ)) :=
      (mem_seqSobolev38_iff _ _).2 (hu (j + 2 - 1))
    set x : SobolevHilbert ((j + 2 - 1 : ℕ) : ℝ) :=
      ofCarrier38 ((j + 2 - 1 : ℕ) : ℝ) (physC38 (j + 2 - 1) u) with hx
    have hsource : ∀ n : ℤ,
        (show WeightedHilbert (sobolevModeWeight ((j + 2 - 1 : ℕ) : ℝ)) from x) n =
          physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper)) n := by
      intro n
      have e : (ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper) : PhysicalL2) = u :=
        hUu
      rw [e]
      have : x = carrierMk38 ((j + 2 - 1 : ℕ) : ℝ) _ hmem := by
        rw [hx]; exact physC38_of_mem (j + 2 - 1) u hmem
      rw [this]
      rfl
    exact chargeSobolev38_smooth (j + 2) j (by omega) (by omega) U hU hper x hsource

end NlsGge.ThirdConsultation.I030Aux
