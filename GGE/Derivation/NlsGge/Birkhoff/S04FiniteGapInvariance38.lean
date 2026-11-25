import NlsGge.Birkhoff.S04Moments38
import NlsGge.NLS38.TorusTwist38

/-! # D1 (abstract part): finite-gap invariance of `ν_Λ` under an abstract `S`
(GWP plan `campaign/GWP_PLAN.md` §5.4 and §7 Part D, piece D1)

**This file is ABSTRACT in the flow `S`.**  `S : ℝ → PhysicalL2 → PhysicalL2` is an arbitrary
parameter.  By design risk R4 (`campaign/BIRKHOFF_LAYER_DESIGN.md` §2.4), `BirkhoffNLSFlowInput38 B S`
is NEVER instantiated here, and no declaration of this file is an S04 statement: S04.07 is
`S04_07_nlsFlow_invariant_nu` (piece D3), which instantiates `S := nlsFlowL2`.  The names
`finiteGap_invariant_aux`, `finiteGapField_rotation_of` and `finiteGapField_rotation` are internal
lemmas, valid for every `S` satisfying their stated hypotheses.

Mathematics.  If `Φ(S_t u)_n = e^{-i t Ω_n(I)} Φ(u)_n` for finite-gap `u` (`I = |Φ u|²`), then on
`u = Φ⁻¹(z)`, `z ∈ ℂ^Λ`, the flow is `S_t u = Φ⁻¹(τ_t z)` with the twist
`τ_t z = (e^{-i t Ω_n(|z|²)} z_n)_{n∈Λ}`.  The twist preserves Lebesgue measure on `ℂ^Λ`
(`NlsGge.NLS38.map_withDensity_twist`, piece C1) and the density `e^{-𝓔_W(Φ⁻¹ z)}` of `ν̂_Λ`
(hypothesis `henergy`, supplied by Lax isospectrality in the concrete case), so `(τ_t)_# ν̂_Λ = ν̂_Λ`
and `(S_t)_# ν_Λ = ν_Λ`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38
open scoped ENNReal

/-! ### Finite support of `extZero38` and Birkhoff coordinates of finite-gap fields -/

theorem finite_support_extZero38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    {n : ℤ | extZero38 Λ w n ≠ 0}.Finite :=
  Λ.finite_toSet.subset (fun n hn => by
    by_contra h
    exact hn (extZero38_apply_of_not_mem w h))

theorem extZero38_mem_zero (Λ : Finset ℤ) (w : Λ → ℂ) : extZero38 Λ w ∈ seqSobolev38 0 :=
  finiteSupport_mem_seqSobolev38 0 _ (finite_support_extZero38 Λ w)

theorem norm_extZero38_rotate (Λ : Finset ℤ) (z : Λ → ℂ) (θ : Λ → ℝ) (k : ℤ) :
    ‖extZero38 Λ (fun i => Complex.exp (θ i * Complex.I) * z i) k‖ = ‖extZero38 Λ z k‖ := by
  by_cases hk : k ∈ Λ
  · rw [extZero38_apply_of_mem _ hk, extZero38_apply_of_mem _ hk, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  · rw [extZero38_apply_of_not_mem _ hk, extZero38_apply_of_not_mem _ hk]

/-- The angle field of the twist: `κ_t(w)_i = -t Ω_i(|extZero w|²)`. -/
def kappaΛ38 (Ω : ℤ → (ℤ → ℝ) → ℝ) (Λ : Finset ℤ) (t : ℝ) (w : Λ → ℂ) (i : Λ) : ℝ :=
  -t * Ω i.1 (fun k => ‖extZero38 Λ w k‖ ^ 2)

theorem measurable_kappaΛ38 (Ω : ℤ → (ℤ → ℝ) → ℝ) (hΩ : ∀ n, Measurable (Ω n)) (Λ : Finset ℤ)
    (t : ℝ) : Measurable (kappaΛ38 Ω Λ t) := by
  refine measurable_pi_iff.2 (fun i => ?_)
  refine measurable_const.mul ((hΩ i.1).comp (measurable_pi_iff.2 (fun k => ?_)))
  exact (((measurable_pi_apply k).comp (measurable_extZero38 Λ)).norm).pow_const 2

theorem kappaΛ38_rotate (Ω : ℤ → (ℤ → ℝ) → ℝ) (Λ : Finset ℤ) (t : ℝ) (z : Λ → ℂ) (θ : Λ → ℝ) :
    kappaΛ38 Ω Λ t (fun i => Complex.exp (θ i * Complex.I) * z i) = kappaΛ38 Ω Λ t z := by
  funext i
  simp only [kappaΛ38, norm_extZero38_rotate]

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- The Birkhoff coordinates of the finite-gap field `Φ⁻¹(z)` are `z` (extended by zero). -/
theorem Φ_finiteGapField38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    B.Φ (B.finiteGapField38 Λ w) = extZero38 Λ w :=
  B.Φ_cleanΦinv _ (extZero38_mem_zero Λ w)

theorem finite_support_Φ_finiteGapField38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    {n : ℤ | B.Φ (B.finiteGapField38 Λ w) n ≠ 0}.Finite := by
  rw [B.Φ_finiteGapField38]; exact finite_support_extZero38 Λ w

/-- `Φ⁻¹` recovers the field from its (clean) Birkhoff coordinates. -/
theorem cleanΦinv_Φ38 (v : PhysicalL2) : B.cleanΦinv (B.Φ v) = v := by
  rw [B.cleanΦinv_of_mem _ (B.Φ_mem_zero v)]
  exact B.Φinv_Φ v

/-- The density of `ν̂_Λ` with respect to Lebesgue measure is measurable. -/
theorem measurable_nuHatDens38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) :
    Measurable (fun w : Λ → ℂ => ENNReal.ofReal (B.densΛ38 c Λ w / B.ZcalΛ38 c Λ)) := by
  have h : (fun w : Λ → ℂ => ENNReal.ofReal (B.densΛ38 c Λ w / B.ZcalΛ38 c Λ)) = fun w =>
      ENNReal.ofReal (((∏ i : Λ, Real.pi / rateΛ38 c Λ i) *
        (gaussDensΛ38 c Λ w * Real.exp (-(B.Rbar38 c (extZero38 Λ w))))) / B.ZcalΛ38 c Λ) := by
    funext w
    rw [B.densΛ38_eq lower upper c hlower hbound hupper Λ w]
  rw [h]
  have hg : Measurable (gaussDensΛ38 c Λ) := measurable_finiteGaussianPDF (rateΛ38 c Λ)
  exact ((measurable_const.mul (hg.mul (Real.measurable_exp.comp
    (B.measurable_Rext38 lower upper c hlower hbound hupper Λ).neg))).div_const _).ennreal_ofReal

end BirkhoffTop38

open BirkhoffTop38

section Rotation

variable (B : BirkhoffTop38)

/-- **Abstract rotation lemma** (INTERNAL, not S04): if `S` rotates the Birkhoff coordinates of every
finite-gap field with a fixed family `Ω` (the content of `BirkhoffNLSFlowInput38.rotation`), then on
`finiteGapField38 Λ w` it acts as the twist `τ = twist κ_t` of `ℂ^Λ`. -/
theorem finiteGapField_rotation_of (S : ℝ → PhysicalL2 → PhysicalL2) (Ω : ℤ → (ℤ → ℝ) → ℝ)
    (hΩ : ∀ u : PhysicalL2, {n : ℤ | B.Φ u n ≠ 0}.Finite → ∀ (t : ℝ) (n : ℤ),
      B.Φ (S t u) n =
        Complex.exp (-(((t * Ω n (fun k => ‖B.Φ u k‖ ^ 2) : ℝ) : ℂ) * Complex.I)) * B.Φ u n)
    (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) :
    S t (B.finiteGapField38 Λ w) =
      B.finiteGapField38 Λ (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) w) := by
  have hΦ := B.Φ_finiteGapField38 Λ w
  have hfin := B.finite_support_Φ_finiteGapField38 Λ w
  have key : B.Φ (S t (B.finiteGapField38 Λ w)) =
      extZero38 Λ (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) w) := by
    funext n
    rw [hΩ _ hfin t n, hΦ]
    by_cases hn : n ∈ Λ
    · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn]
      simp only [NlsGge.NLS38.twist, kappaΛ38]
      congr 2
      push_cast
      ring
    · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn, mul_zero]
  calc S t (B.finiteGapField38 Λ w)
      = B.cleanΦinv (B.Φ (S t (B.finiteGapField38 Λ w))) := (B.cleanΦinv_Φ38 _).symm
    _ = _ := by rw [key]; rfl

/-- **Spec statement `finiteGapField_rotation`** (INTERNAL, not S04).  The spec of the plan reads
`∃ τ, S t (finiteGapField38 Λ w) = finiteGapField38 Λ (τ w) ∧ τ = twist (… Ω …)` with `Ω` unbound;
here `Ω` (obtained from `hFl.rotation`) is bound by an outer existential, uniform in `Λ w t`, and
`τ` is substituted.  `Ω_n` is measurable and `τ = twist (fun w i => -t * Ω i.1 (fun k => ‖extZero38 Λ w k‖^2))`. -/
theorem finiteGapField_rotation (S : ℝ → PhysicalL2 → PhysicalL2)
    (hFl : BirkhoffNLSFlowInput38 B S) :
    ∃ Ω : ℤ → (ℤ → ℝ) → ℝ, (∀ n, Measurable (Ω n)) ∧
      ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ),
        S t (B.finiteGapField38 Λ w) =
          B.finiteGapField38 Λ (NlsGge.NLS38.twist
            (fun (w : Λ → ℂ) (i : Λ) => -t * Ω i.1 (fun k => ‖extZero38 Λ w k‖ ^ 2)) w) := by
  obtain ⟨Ω, hΩm, hΩ⟩ := hFl.rotation
  exact ⟨Ω, hΩm, fun Λ w t => finiteGapField_rotation_of B S Ω hΩ Λ w t⟩

end Rotation

/-! ### Invariance of `ν_Λ` -/

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- **Finite-gap invariance, abstract in `S`** (INTERNAL lemma, NOT S04).  Let `S` be any family of
maps of `PhysicalL2`, measurable for each `t`, satisfying the finite-gap rotation law
`hFl : BirkhoffNLSFlowInput38 B S` and preserving `𝓔_W` on finite-gap fields (`henergy`).  Then
`(S t)_# ν_Λ = ν_Λ`.  The concrete S04.07 is the instance `S := nlsFlowL2` in piece D3. -/
theorem finiteGap_invariant_aux (S : ℝ → PhysicalL2 → PhysicalL2) (hmeas : ∀ t, Measurable (S t))
    (hFl : BirkhoffNLSFlowInput38 B S)
    (henergy : ∀ t u, {n : ℤ | B.Φ u n ≠ 0}.Finite → energyW38 c (S t u) = energyW38 c u)
    (Λ : Finset ℤ) (t : ℝ) : (B.nu38 c Λ).map (S t) = B.nu38 c Λ := by
  obtain ⟨Ω, hΩm, hΩ⟩ := hFl.rotation
  have hrot : ∀ w : Λ → ℂ, S t (B.finiteGapField38 Λ w) =
      B.finiteGapField38 Λ (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) w) :=
    fun w => finiteGapField_rotation_of B S Ω hΩ Λ w t
  have hκ := measurable_kappaΛ38 Ω hΩm Λ t
  have hinv := kappaΛ38_rotate Ω Λ t
  have hT : Measurable (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t)) := NlsGge.NLS38.measurable_twist _ hκ
  have hdens : ∀ w, B.densΛ38 c Λ (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) w) = B.densΛ38 c Λ w := by
    intro w
    unfold densΛ38
    rw [← hrot w, henergy t _ (B.finite_support_Φ_finiteGapField38 Λ w)]
  have hnu : (B.nuHat38 c Λ).map (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t)) = B.nuHat38 c Λ := by
    unfold nuHat38
    exact NlsGge.NLS38.map_withDensity_twist (kappaΛ38 Ω Λ t) hκ hinv _
      (B.measurable_nuHatDens38 lower upper c hlower hbound hupper Λ) (fun w => by
        simp only [hdens])
  unfold nu38
  rw [Measure.map_map (hmeas t) (B.measurable_finiteGapField38 Λ)]
  have hcomp : S t ∘ B.finiteGapField38 Λ =
      B.finiteGapField38 Λ ∘ NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) := funext hrot
  rw [hcomp, ← Measure.map_map (B.measurable_finiteGapField38 Λ) hT, hnu]

end NlsGge.Birkhoff
