import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Birkhoff.S04Invariance38
import NlsGge.NLS38.LaxConsequences38
import NlsGge.NLS38.FlowMeasure38

/-! # D3: S04.07 and S04.08 for the actual NLS flow `nlsFlowL2`
(GWP plan `campaign/GWP_PLAN.md` §6.3 and §7 Part D, piece D3)

This file instantiates the abstract lemmas D1 `finiteGap_invariant_aux` and D2 `muW_invariant_aux`
at the actual solution map `S := nlsFlowL2` of `i u_t = -u_xx + 2|u|² u` (v2 `eq:nls`).  By design
risk R4, `S` is never arbitrary in a statement presented as S04.

The only hypothesis beyond `B : BirkhoffTop38` is the flow input
`hFl : BirkhoffNLSFlowInput38 B nlsFlowL2` (field `rotation`).  Inputs used:
* from `B`: `Φ`, `Φinv` (`Φinv_Φ`, `sobolev_Φinv`), `muW38`, `nu38`, `ae_muW38_allSobolev`,
  `isProbabilityMeasure_muW38`, `isProbabilityMeasure_nu38`, through D1/D2;
* from `hFl`: `rotation` (through D1 `finiteGap_invariant_aux`).
Everything else is Phi-free GWP and Lax: `measurable_nlsFlowL2` (C2b), `energyW38_nlsFlow` (B4),
`physH38_nlsFlowL2`, `nlsFlowL2_mem` (A10), `nlsFlowC`, `continuous_nlsFlowC_uncurry` (A9).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 NlsGge.NLS38
open scoped ENNReal BoundedContinuousFunction

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

omit hlower hbound hupper in
/-- Finite-gap fields (finite support of `Φ u`) lie in `H³`, by `B.sobolev_Φinv` and
`finiteSupport_mem_seqSobolev38`. -/
theorem finiteGap_mem_H3_38 (u : PhysicalL2) (hfin : {n : ℤ | B.Φ u n ≠ 0}.Finite) :
    SobolevSquareSummable 3 (physicalFourier u) := by
  have hz : B.Φ u ∈ seqSobolev38 ((3 : ℕ) : ℝ) := finiteSupport_mem_seqSobolev38 _ _ hfin
  have h := B.sobolev_Φinv 3 (B.Φ u) hz
  rw [B.Φinv_Φ u, Nat.cast_ofNat] at h
  exact h

/-- **S04.07** (v2 l.445-446): the actual NLS flow `nlsFlowL2 t` preserves every finite-gap law
`ν_Λ`.  Conditional on `B` and on the flow input `hFl` at `S := nlsFlowL2`. -/
theorem S04_07_nlsFlow_invariant_nu (hFl : BirkhoffNLSFlowInput38 B nlsFlowL2) (Λ : Finset ℤ)
    (t : ℝ) : (B.nu38 c Λ).map (nlsFlowL2 t) = B.nu38 c Λ :=
  finiteGap_invariant_aux B lower upper c hlower hbound hupper nlsFlowL2 measurable_nlsFlowL2 hFl
    (fun t u hfin => energyW38_nlsFlow c u (B.finiteGap_mem_H3_38 u hfin) t) Λ t

/-- **S04.08** (v2 l.447-453): the actual NLS flow `nlsFlowL2 t` preserves `μ_W` on `PhysicalL2`. -/
theorem S04_08_nlsFlow_invariant_muW (hFl : BirkhoffNLSFlowInput38 B nlsFlowL2) (t : ℝ) :
    (B.muW38 c).map (nlsFlowL2 t) = B.muW38 c :=
  B.muW_invariant_aux lower upper c hlower hbound hupper nlsFlowL2 measurable_nlsFlowL2
    (fun t => nlsFlowC 1 le_rfl t) (fun t => continuous_nlsFlowC_one38 t)
    (fun t _ hu => physH38_nlsFlowL2 1 le_rfl hu t)
    (fun t u hu => (fourierSeq38_mem_iff _ _).2
      (nlsFlowL2_mem 1 le_rfl ((fourierSeq38_mem_iff _ u).1 hu) t))
    (fun t Λ => B.S04_07_nlsFlow_invariant_nu lower upper c hlower hbound hupper hFl Λ t) t

/-- The junk branch of `nlsFlowL2` (fields outside `H¹`) is `μ_W`-null. -/
theorem muW38_junk_null38 :
    B.muW38 c {u : PhysicalL2 | fourierSeq38 u ∉ seqSobolev38 ((1 : ℕ) : ℝ)} = 0 := by
  refine ae_iff.1 ?_
  filter_upwards [B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu
  exact (fourierSeq38_mem_iff _ u).2 (hu 1)

/-- Same, in the form of the test of the `dite` defining `nlsFlowL2`. -/
theorem muW38_junk_null_physical38 :
    B.muW38 c {u : PhysicalL2 | ¬ SobolevSquareSummable 1 (physicalFourier u)} = 0 := by
  refine ae_iff.1 ?_
  filter_upwards [B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu
  have := hu 1
  rw [Nat.cast_one] at this
  exact this

/-- **S04.08, every `m ≥ 1`** (review note N5): the carrier law `(physH38 m)_# μ_W` on `h^m` is
invariant under the continuous flow `nlsFlowC m`. -/
theorem S04_08_nlsFlow_invariant_muW_Hm (hFl : BirkhoffNLSFlowInput38 B nlsFlowL2) (m : ℕ)
    (hm : 1 ≤ m) (t : ℝ)
    [MeasurableSpace (SobolevCarrier38 (m : ℝ))] [BorelSpace (SobolevCarrier38 (m : ℝ))] :
    ((B.muW38 c).map (physH38 m)).map (nlsFlowC m hm t) = (B.muW38 c).map (physH38 m) := by
  have hcont : Continuous (nlsFlowC m hm t) :=
    (continuous_nlsFlowC_uncurry m hm).comp (continuous_const.prodMk continuous_id)
  have hF : Measurable (nlsFlowC m hm t) := hcont.measurable
  have hP : Measurable (physH38 m) := measurable_physH38 m
  have hae : (nlsFlowC m hm t ∘ physH38 m) =ᵐ[B.muW38 c] (physH38 m ∘ nlsFlowL2 t) := by
    filter_upwards [B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu
    exact (physH38_nlsFlowL2 m hm ((fourierSeq38_mem_iff _ u).2 (hu m)) t).symm
  have hmeas : Measurable (nlsFlowL2 t) := measurable_nlsFlowL2 t
  rw [Measure.map_map hF hP, Measure.map_congr hae, ← Measure.map_map hP hmeas,
    B.S04_08_nlsFlow_invariant_muW lower upper c hlower hbound hupper hFl t]

/-- **S04.08 in integral form, every `m ≥ 1`** (v2 l.447-453): for bounded continuous `F` on `H^m`,
`∫ F(S_t u) dμ_W = ∫ F(u) dμ_W`, with `S_t` the continuous carrier flow `nlsFlowC m`. -/
theorem S04_08_nlsFlow_integral_Hm (hFl : BirkhoffNLSFlowInput38 B nlsFlowL2) (m : ℕ)
    (hm : 1 ≤ m) (t : ℝ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ) :
    ∫ u, F (nlsFlowC m hm t (physH38 m u)) ∂(B.muW38 c) = ∫ u, F (physH38 m u) ∂(B.muW38 c) := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  have hcont : Continuous (nlsFlowC m hm t) :=
    (continuous_nlsFlowC_uncurry m hm).comp (continuous_const.prodMk continuous_id)
  have hP : Measurable (physH38 m) := measurable_physH38 m
  have hFm : AEStronglyMeasurable (fun x : SobolevCarrier38 (m : ℝ) => F x)
      ((B.muW38 c).map (physH38 m)) := F.continuous.aestronglyMeasurable
  have hFm' : AEStronglyMeasurable (fun x : SobolevCarrier38 (m : ℝ) => F x)
      (((B.muW38 c).map (physH38 m)).map (nlsFlowC m hm t)) := F.continuous.aestronglyMeasurable
  have h1 : ∫ u, F (nlsFlowC m hm t (physH38 m u)) ∂(B.muW38 c) =
      ∫ x, F (nlsFlowC m hm t x) ∂((B.muW38 c).map (physH38 m)) :=
    (integral_map hP.aemeasurable (F.continuous.comp hcont).aestronglyMeasurable).symm
  have h2 : ∫ x, F (nlsFlowC m hm t x) ∂((B.muW38 c).map (physH38 m)) =
      ∫ x, F x ∂(((B.muW38 c).map (physH38 m)).map (nlsFlowC m hm t)) :=
    (integral_map hcont.measurable.aemeasurable hFm').symm
  have h3 : ∫ u, F (physH38 m u) ∂(B.muW38 c) = ∫ x, F x ∂((B.muW38 c).map (physH38 m)) :=
    (integral_map hP.aemeasurable hFm).symm
  rw [h1, h2, h3, B.S04_08_nlsFlow_invariant_muW_Hm lower upper c hlower hbound hupper hFl m hm t]

/-! ### Non-vacuity probes

`Measure.map` of a non-measurable map is the zero measure.  The statements above are not vacuous:
`nlsFlowL2 t` is measurable (`measurable_nlsFlowL2`), so the pushforwards are probability
measures, in particular nonzero.  Also, `hFl` is compatible with the GWP map: its `t = 0` slice is
true for every `Ω`, because `nlsFlowL2 0 = id` (`nlsFlowL2_zero`), and its consequence on the
action moduli is the conservation of `|Φ u n|`, the same conservation as Lax isospectrality. -/

theorem isProbabilityMeasure_map_muW_nlsFlow38 (t : ℝ) :
    IsProbabilityMeasure ((B.muW38 c).map (nlsFlowL2 t)) :=
  have := B.isProbabilityMeasure_muW38 lower upper c hlower hbound hupper
  isProbabilityMeasure_map_nlsFlowL2_38 _ t

theorem isProbabilityMeasure_map_nu_nlsFlow38 (Λ : Finset ℤ) (t : ℝ) :
    IsProbabilityMeasure ((B.nu38 c Λ).map (nlsFlowL2 t)) :=
  have := B.isProbabilityMeasure_nu38 lower upper c hlower hbound hupper Λ
  isProbabilityMeasure_map_nlsFlowL2_38 _ t

theorem map_muW_nlsFlow_ne_zero38 (t : ℝ) : (B.muW38 c).map (nlsFlowL2 t) ≠ 0 :=
  have := B.isProbabilityMeasure_map_muW_nlsFlow38 lower upper c hlower hbound hupper t
  IsProbabilityMeasure.ne_zero _

theorem map_nu_nlsFlow_ne_zero38 (Λ : Finset ℤ) (t : ℝ) : (B.nu38 c Λ).map (nlsFlowL2 t) ≠ 0 :=
  have := B.isProbabilityMeasure_map_nu_nlsFlow38 lower upper c hlower hbound hupper Λ t
  IsProbabilityMeasure.ne_zero _

omit hlower hbound hupper in
/-- The `t = 0` slice of the rotation law of `hFl` holds for `nlsFlowL2` and every `Ω`. -/
theorem rotation_zero_nlsFlow38 (Ω : ℤ → (ℤ → ℝ) → ℝ) (u : PhysicalL2) (n : ℤ) :
    B.Φ (nlsFlowL2 0 u) n =
      Complex.exp (-(((0 * Ω n (fun k => ‖B.Φ u k‖ ^ 2) : ℝ) : ℂ) * Complex.I)) * B.Φ u n := by
  simp [nlsFlowL2_zero]

omit hlower hbound hupper in
/-- Under `hFl`, the moduli `|Φ u n|` of finite-gap data are conserved by `nlsFlowL2`
(consistent with Lax isospectrality; no contradiction with GWP). -/
theorem norm_Φ_nlsFlow38 (hFl : BirkhoffNLSFlowInput38 B nlsFlowL2) (u : PhysicalL2)
    (hfin : {n : ℤ | B.Φ u n ≠ 0}.Finite) (t : ℝ) (n : ℤ) :
    ‖B.Φ (nlsFlowL2 t u) n‖ = ‖B.Φ u n‖ := by
  obtain ⟨Ω, _, hΩ⟩ := hFl.rotation
  rw [hΩ u hfin t n, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
  simp

end BirkhoffTop38

end NlsGge.Birkhoff
