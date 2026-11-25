import NlsGge.Birkhoff.S03Measure38d
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Ramer.General.RamerInstancesB
import NlsGge.Spectral.F04Lemma38

/-! # F05 (v2 `B:cor:identity`), file a: reflection `𝓕⁻¹`, the objects `γ_m^F`, `R_m(Φ⁻¹ z)`, `Z_m`, `μ_m`

Source: `paper/v2.tex` l.655-678.  Conditional on `B : BirkhoffInput38` (and `O` in later files).

Fourier carriers.  A physical field `u ∈ H^{m-1}(𝕋;ℂ)` is identified with its Fourier coefficient
sequence `(û(n))`, an element of `SobolevHilbert (m-1)`.  `𝓕⁻¹` on coefficient sequences is the
isometric involution `(𝓕⁻¹x)_n = -x_{-n}` (`reflC38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General Filter Topology
open scoped ENNReal

/-! ### The reflection `𝓕⁻¹` on `h^r` -/

/-- `(𝓕⁻¹ x)_n = -x_{-n}` on the carrier `h^r`. -/
def reflC38 (r : ℝ) (x : SobolevCarrier38 r) : SobolevCarrier38 r :=
  carrierMk38 r (reflect38 (carrierCoe38 r x)) (reflect38_mem (carrierCoe38_mem r x))

@[simp] theorem carrierCoe38_reflC38 (r : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (reflC38 r x) n = -carrierCoe38 r x (-n) := rfl

theorem reflC38_reflC38 (r : ℝ) (x : SobolevCarrier38 r) : reflC38 r (reflC38 r x) = x := by
  apply carrierExt38
  funext n
  simp

theorem reflC38_add (r : ℝ) (x y : SobolevCarrier38 r) :
    reflC38 r (x + y) = reflC38 r x + reflC38 r y := by
  apply carrierExt38
  funext n
  show -(carrierCoe38 r x (-n) + carrierCoe38 r y (-n)) = _
  show _ = -(carrierCoe38 r x (-n)) + -(carrierCoe38 r y (-n))
  ring

theorem reflC38_smul (r : ℝ) (c : ℝ) (x : SobolevCarrier38 r) :
    reflC38 r (c • x) = c • reflC38 r x := by
  apply carrierExt38
  funext n
  show -((c : ℂ) * carrierCoe38 r x (-n)) = (c : ℂ) * -carrierCoe38 r x (-n)
  ring

theorem norm_reflC38 (r : ℝ) (x : SobolevCarrier38 r) : ‖reflC38 r x‖ = ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (reflC38 r x)
  have h2 := carrier_hasSum_norm_sq38 r x
  have h3 : HasSum (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2)
      (‖x‖ ^ 2) := h2
  have h4 := (Equiv.neg ℤ).hasSum_iff.2 h3
  have e : (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (reflC38 r x) n‖ ^ 2) =
      (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) ∘ (Equiv.neg ℤ) := by
    funext n
    simp [Function.comp, sobolevModeWeight_neg]
  rw [e] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h4)

/-- `𝓕⁻¹` as a real-linear isometry equivalence of `h^r`. -/
def reflIso38 (r : ℝ) : SobolevCarrier38 r ≃ₗᵢ[ℝ] SobolevCarrier38 r where
  toFun := reflC38 r
  invFun := reflC38 r
  map_add' := reflC38_add r
  map_smul' c x := reflC38_smul r c x
  left_inv := reflC38_reflC38 r
  right_inv := reflC38_reflC38 r
  norm_map' := norm_reflC38 r

theorem continuous_reflC38 (r : ℝ) : Continuous (reflC38 r) := (reflIso38 r).continuous


/-! ### The objects of v2 l.655-669 -/

/-- The Fourier carrier `H^{m-1}` (coefficient sequences with weight `⟨n⟩^{2(m-1)}`). -/
abbrev Hm1 (m : ℕ) : Type := SobolevHilbert ((m - 1 : ℕ) : ℝ)

/-- `R_m(u)` (v2 `B:eq:Rm`), on `H^{m-1}`: the series of gap remainders. -/
def Rm38 (m : ℕ) (β : ℕ → ℝ) (y : Hm1 m) : ℝ :=
  ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 (m - 1)) y) n

/-- `V_m` (v2 `B:eq:Vm`, extended by `B:lem:local`), on `H^{m-1}`. -/
def Vm38 (m : ℕ) (β : ℕ → ℝ) (y : Hm1 m) : ℝ := localRemainderSobolev38 m β (toCarrier38 _ y)

/-- `𝓕⁻¹` on `H^{m-1}` coefficient sequences. -/
def FinvH38 (m : ℕ) (y : Hm1 m) : Hm1 m := ofCarrier38 _ (reflC38 _ (toCarrier38 _ y))

theorem continuous_FinvH38 (m : ℕ) : Continuous (FinvH38 m) :=
  (continuous_ofCarrier38 _).comp ((continuous_reflC38 _).comp (continuous_toCarrier38 _))

theorem coeff_FinvH38 (m : ℕ) (y : Hm1 m) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from FinvH38 m y) n =
      -(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) (-n) := rfl

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-- `Φ⁻¹ z ∈ H^{m-1}` (as Fourier coefficients) for `z ∈ h^{m-1}`: `Φ⁻¹ = 𝓕⁻¹ ∘ T⁻¹`; junk `0`
off `h^{m-1}` (a `γ_m`-null set). -/
def PhiInvX38 (m : ℕ) (z : ℤ → ℂ) : Hm1 m :=
  ofCarrier38 _ (reflC38 _ (B.cleanTinvC (m - 1) z))

theorem measurable_PhiInvX38 (m : ℕ) : Measurable (B.PhiInvX38 m) :=
  ((continuous_ofCarrier38 _).measurable.comp (continuous_reflC38 _).measurable).comp
    (B.measurable_cleanTinvC (m - 1))

end BirkhoffInput38

section Defs

variable (B : BirkhoffInput38) (m : ℕ) (β : ℕ → ℝ)

/-- `Z_m = ∫ e^{-R_m(Φ⁻¹ z)} dγ_m(z)` (v2 `B:eq:mumeasures`). -/
def ZM38 : ℝ := ∫ z, Real.exp (-(Rm38 m β (B.PhiInvX38 m z))) ∂(gammaM38 m β)

/-- `μ̂_m = Z_m⁻¹ e^{-R_m(Φ⁻¹ z)} γ_m`. -/
def muHatM38 : Measure (ℤ → ℂ) :=
  (gammaM38 m β).withDensity
    (fun z => ENNReal.ofReal (Real.exp (-(Rm38 m β (B.PhiInvX38 m z))) / ZM38 B m β))

/-- `μ_m = (Φ⁻¹)_# μ̂_m` as a measure on `H^{m-1}`. -/
def muM38 : Measure (Hm1 m) := (muHatM38 B m β).map (B.PhiInvX38 m)

/-- `γ_m^F = (𝓕⁻¹)_# γ_m`, `γ_m` regarded as a measure on `h^{m-1}` by realization. -/
def gammaFM38 : Measure (Hm1 m) :=
  ((gammaM38 m β).map (gaussianRealization38 m)).map (FinvH38 m)

end Defs

section Basic

variable (B : BirkhoffInput38) {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
include hm hβ

theorem Rm38_nonneg (y : Hm1 m) : 0 ≤ Rm38 m β y :=
  ((F04_spectral_lemma38 m hm β hβ).1 y).2

theorem continuous_Rm38 : Continuous (Rm38 m β) :=
  (F04_spectral_lemma38 m hm β hβ).2.1

theorem continuous_Vm38 : Continuous (Vm38 m β) :=
  (continuous_localRemainderSobolev38 m β).comp (continuous_toCarrier38 _)

end Basic

namespace BirkhoffInput38

section Basic2

variable (B : BirkhoffInput38) {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
include hm hβ

theorem measurable_expNegR38 :
    Measurable (fun z : ℤ → ℂ => Real.exp (-(Rm38 m β (B.PhiInvX38 m z)))) :=
  (Real.measurable_exp.comp ((continuous_Rm38 hm hβ).measurable.comp
    (B.measurable_PhiInvX38 m)).neg)

theorem expNegR38_le_one (z : ℤ → ℂ) :
    Real.exp (-(Rm38 m β (B.PhiInvX38 m z))) ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith [Rm38_nonneg hm hβ (B.PhiInvX38 m z)])

theorem integrable_expNegR38 :
    Integrable (fun z : ℤ → ℂ => Real.exp (-(Rm38 m β (B.PhiInvX38 m z)))) (gammaM38 m β) :=
  Integrable.of_bound (B.measurable_expNegR38 hm hβ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact B.expNegR38_le_one hm hβ z)

/-- **`0 < Z_m ≤ 1`** (v2 l.668). -/
theorem ZM38_pos_le_one : 0 < ZM38 B m β ∧ ZM38 B m β ≤ 1 := by
  refine ⟨integral_exp_pos (f := fun z => -(Rm38 m β (B.PhiInvX38 m z)))
    (B.integrable_expNegR38 hm hβ), ?_⟩
  calc ZM38 B m β ≤ ∫ _z, (1 : ℝ) ∂(gammaM38 m β) :=
        integral_mono (B.integrable_expNegR38 hm hβ) (integrable_const _)
          (fun z => B.expNegR38_le_one hm hβ z)
    _ = 1 := by simp

theorem isProbabilityMeasure_muHatM38 : IsProbabilityMeasure (muHatM38 B m β) := by
  have hZ := (B.ZM38_pos_le_one hm hβ).1
  refine ⟨?_⟩
  rw [muHatM38, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((B.integrable_expNegR38 hm hβ).div_const (ZM38 B m β))
      (Filter.Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hZ.le)]
  rw [integral_div]
  change ENNReal.ofReal (ZM38 B m β / ZM38 B m β) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

theorem isProbabilityMeasure_muM38 : IsProbabilityMeasure (muM38 B m β) := by
  have := B.isProbabilityMeasure_muHatM38 hm hβ
  unfold muM38
  infer_instance

end Basic2

end BirkhoffInput38

end NlsGge.Birkhoff
