import QuantumNLS.Prop021GeneralR132
import Mathlib.Analysis.Analytic.OfScalars

/-! The canonical action of the Weyl displacement on total coherent
vectors of Fock(H). This provides a realization-independent
characterization, with the phase for inner products linear in the
second argument. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024CanonicalWeylR133
open TensorCarrier IntrinsicContact PhysicalTensor
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022BIso
open Prop022BFock1 Prop022BFock2 Prop022GHilbert Prop022BExist
open Ext025B3PhysicalSectors Ext006PhysFockCoord Prop022OVacuum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def expSector (v : H) (n : ℕ) : SymSector ℂ H n :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ • powerH n v

private theorem expSector_norm_sq (v : H) (n : ℕ) :
    ‖expSector v n‖ ^ 2 = (‖v‖ ^ 2) ^ n / (n.factorial : ℝ) := by
  unfold expSector
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change ((Real.sqrt (n.factorial : ℝ))⁻¹ * ‖(htpow n v : HilbertTensorPower ℂ H n)‖) ^ 2 = _
  rw [norm_htpow, mul_pow, inv_pow, Real.sq_sqrt (by positivity), ← pow_mul ‖v‖ n 2,
    ← pow_mul ‖v‖ 2 n, Nat.mul_comm n 2, div_eq_mul_inv, mul_comm]

/-- The unnormalized exponential vector with sectors v^⊗n/√n!. -/
def exponentialVector (v : H) : FockSpace H :=
  ⟨expSector v, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, expSector_norm_sq] using
      Real.summable_pow_div_factorial (‖v‖ ^ 2)⟩

/-- The normalized coherent vector. -/
def coherent (v : H) : FockSpace H :=
  (Real.exp (-‖v‖ ^ 2 / 2) : ℂ) • exponentialVector v

variable [CompleteSpace H]

private theorem expSector_smul (z : ℂ) (v : H) (n : ℕ) :
    expSector (z • v) n = z^n • expSector v n := by
  have hv : powerH n (z • v) = z^n • powerH n v :=
    Subtype.ext (htpow_smul n z v)
  rw [expSector, expSector, hv, smul_comm]

private theorem exponentialVector_total {L : ℝ} [Fact (0 < L)] (J : H →ₗᵢ[ℂ] L2T L)
    (x : FockSpace H) (hx : ∀ v, ⟪x, exponentialVector v⟫_ℂ = 0) : x = 0 := by
  have hc (v : H) (n : ℕ) : ⟪x n, expSector v n⟫_ℂ = 0 := by
    let c : ℕ → ℂ := fun k => ⟪x k, expSector v k⟫_ℂ
    let p := FormalMultilinearSeries.ofScalars ℂ c
    have hs : Summable (fun k => ‖c k‖) := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ (lp.summable_mul ?_ x (exponentialVector v))
      · intro k
        exact norm_inner_le_norm _ _
      · rw [Real.holderConjugate_iff]
        norm_num
    have hr : (1 : ℝ≥0∞) ≤ p.radius := by
      apply p.le_radius_of_summable_norm (r := 1)
      simpa only [p, NNReal.coe_one, one_pow, mul_one, FormalMultilinearSeries.ofScalars_norm] using hs
    have hp := (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le hr)).hasFPowerSeriesAt
    have he (z : ℂ) : p.sum z = 0 := by
      rw [← hx (z • v), lp.inner_eq_tsum]
      have hh (k : ℕ) : ⟪x k, exponentialVector (z • v) k⟫_ℂ = c k • z^k := by
        change ⟪x k, expSector (z • v) k⟫_ℂ = _
        rw [expSector_smul, inner_smul_right, smul_eq_mul, mul_comm]
      simp only [hh]
      exact FormalMultilinearSeries.ofScalars_sum_eq c z
    have hz := hp.eq_zero_of_eventually (Filter.Eventually.of_forall he)
    exact congrFun ((FormalMultilinearSeries.ofScalars_series_eq_zero ℂ (c := c)).mp hz) n
  apply lp.ext
  funext n
  change x n = 0
  apply (symMapI J n).injective
  rw [map_zero]
  apply Prop022ACoherent.powers_total n
  intro g
  change ⟪powerH n g, symI J n (x n)⟫_ℂ = 0
  rw [← inner_symAdj_left, symAdj_power, ← inner_eq_zero_symm]
  have hn := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n.factorial)).ne'
  have hh := hc (Jadj J g) n
  rw [expSector, inner_smul_right, mul_eq_zero] at hh
  exact hh.resolve_left (inv_ne_zero hn)

/-- A continuous linear operator is determined by its action on coherent
vectors, also when the one-particle carrier is finite-dimensional. -/
theorem coherent_ext {L : ℝ} [Fact (0 < L)] (J : H →ₗᵢ[ℂ] L2T L)
    (T U : FockSpace H ≃ₗᵢ[ℂ] FockSpace H)
    (h : ∀ w, T (coherent w) = U (coherent w)) : T = U := by
  have hP : (Submodule.span ℂ (Set.range (coherent (H := H)))).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal'] at hx
    apply exponentialVector_total J x
    intro w
    have hw := hx _ (Submodule.subset_span ⟨w,rfl⟩)
    rw [coherent, inner_smul_right, mul_eq_zero] at hw
    exact hw.resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  let D : FockSpace H →L[ℂ] FockSpace H :=
    T.toLinearIsometry.toContinuousLinearMap - U.toLinearIsometry.toContinuousLinearMap
  have hker : Submodule.span ℂ (Set.range (coherent (H := H))) ≤ LinearMap.ker D.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w,rfl⟩
    change T (coherent w) - U (coherent w) = 0
    rw [h, sub_self]
  have hh := Submodule.topologicalClosure_minimal _ hker D.isClosed_ker
  rw [hP] at hh
  apply LinearIsometryEquiv.ext
  intro x
  have hz : T x - U x = 0 := hh Submodule.mem_top
  exact sub_eq_zero.mp hz

/-- The normalization and the sign of the displacement, expressed
entirely in terms of the source Hilbert space. -/
def WeylAction (W : H → FockSpace H ≃ₗᵢ[ℂ] FockSpace H) : Prop :=
  ∀ v w : H, W v (coherent w) =
    Complex.exp (-Complex.I * (⟪v,w⟫_ℂ).im) • coherent (v+w)

theorem coherent_transport {L : ℝ} [Fact (0 < L)] (J : H →ₗᵢ[ℂ] L2T L) (v : H) :
    fockMapI J (coherent v) = printedWeyl (J v) (vac : Fock L) := by
  apply lp.ext
  funext n
  rw [fockMapI_apply, Prop021CoherentCoreR131.coherent_sector]
  change symI J n ((Real.exp (-‖v‖ ^ 2 / 2) : ℂ) •
    (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ • powerH n v) = _
  rw [map_smul, map_smul, symI_power, smul_smul]
  change _ = ((Real.exp (-‖J v‖ ^ 2 / 2) : ℂ) / (Real.sqrt (n.factorial : ℝ) : ℂ)) •
    powerH n (J v)
  simp only [J.norm_map, div_eq_mul_inv]

/-- The compressed Weyl operator has the intrinsic canonical action on
coherent vectors, fixing its normalization and its phase. -/
theorem compressed_weylAction {L : ℝ} [Fact (0 < L)] (J : H →ₗᵢ[ℂ] L2T L) :
    WeylAction (WJ J) := by
  intro v w
  apply (fockMapI J).injective
  have h : fockMapI J (WJ J v (coherent w)) = printedWeyl (J v) (fockMapI J (coherent w)) :=
    gam_compress _ _ _ _
  rw [h, map_smul, coherent_transport, coherent_transport, map_add,
    Prop021WeylLawR131.printedWeyl_add]
  rw [LinearIsometry.inner_map_map, smul_smul, ← Complex.exp_add, neg_mul, neg_add_cancel,
    Complex.exp_zero, one_smul]

variable [TopologicalSpace.SeparableSpace H]

/-- Existence of the canonical Weyl operator on every separable H. -/
theorem exists_weylAction : ∃ W : H → FockSpace H ≃ₗᵢ[ℂ] FockSpace H, WeylAction W := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  by_cases hH : FiniteDimensional ℂ H
  · obtain ⟨J⟩ := exists_isometry_fin hH 1
    exact ⟨WJ J, compressed_weylAction J⟩
  · obtain ⟨U⟩ := exists_unitary_L2T 1 hH
    exact ⟨WJ U.toLinearIsometry, compressed_weylAction U.toLinearIsometry⟩

/-- The Weyl operator selected by its canonical coherent-vector formula. -/
def weyl : H → FockSpace H ≃ₗᵢ[ℂ] FockSpace H :=
  Classical.choose (exists_weylAction (H := H))

theorem weyl_action : WeylAction (weyl (H := H)) :=
  Classical.choose_spec (exists_weylAction (H := H))

theorem weyl_eq_compressed {L : ℝ} [Fact (0 < L)] (J : H →ₗᵢ[ℂ] L2T L) :
    weyl (H := H) = WJ J := by
  funext v
  apply coherent_ext J
  intro w
  exact (weyl_action v w).trans ((compressed_weylAction J) v w).symm

end QuantumNLS.Prop024CanonicalWeylR133
