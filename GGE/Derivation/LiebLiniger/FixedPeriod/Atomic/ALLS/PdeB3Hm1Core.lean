import NlsGge.Birkhoff.F01Determinant38

/-! # Track B, step B3 (review item R1 / M1): the typed `H⁻¹` toolkit

Statement-independent infrastructure on the existing complete real Hilbert carrier
`SobolevCarrier38 (-1)` (sequences `x` with `Σ ⟨n⟩^{-2} |x n|² < ∞`, `carrierCompleteSpace38`).

* `summable_sobolevModeWeight_neg_one`: `Σ_n ⟨n⟩^{-2} < ∞`; hence every bounded sequence lies in
  `h⁻¹` with norm at most `hm1Const * sup` (`mem_seqSobolev38_neg_one_of_bdd`,
  `norm_carrierMk38_neg_one_le`).
* `carrierCoordCLM r n`: the coordinate `x ↦ x n` as a continuous real-linear functional;
  `carrierCoe38_integral`, `carrierCoe38_intervalIntegral`: the Bochner integral is computed
  coordinatewise (for an integrable integrand).
* `carrierSingle r n`: the continuous real-linear map `c ↦ c e_n`; `projC38_eq_sum`.
* `aestronglyMeasurable_of_carrierCoe`: a carrier-valued map whose coordinates are all
  a.e.-strongly measurable is a.e.-strongly measurable (truncations `P_N` converge everywhere).
* `l1ToHm1 : L¹(𝕋) →L[ℝ] H⁻¹` and `l2ToHm1 : L²(𝕋) →L[ℝ] H⁻¹` with PROVED coefficient
  characterizations (the coordinates are the ordinary physical Fourier coefficients
  `physicalFourier`), operator bounds, injectivity of `l2ToHm1`; `fnToHm1` is the
  function-level form of `l1ToHm1` (value `0` exactly on non-integrable functions), with
  `carrierCoe38_fnToHm1` (coefficients for every integrable function), a.e.-invariance and the
  compatibility `fnToHm1 u = l2ToHm1 u` for `u ∈ L²`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

/-- `Σ_n ⟨n⟩^{-2} < ∞`. -/
theorem summable_sobolevModeWeight_neg_one : Summable (fun n : ℤ => sobolevModeWeight (-1) n) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := 2) (by norm_num)) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hw := sobolevModeWeight_pos (-1) n
  rw [Real.norm_of_nonneg hw.le]
  have h0 : 0 < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
  have hj : 0 ≤ japaneseBracket n := Real.sqrt_nonneg _
  have hsq : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  show japaneseBracket n ^ (2 * (-1 : ℝ)) ≤ |(n : ℝ)| ^ (-(2 : ℝ))
  rw [show (2 * (-1 : ℝ)) = -(2 : ℝ) by norm_num, Real.rpow_neg hj, Real.rpow_neg h0.le,
    Real.rpow_two, Real.rpow_two, hsq]
  exact inv_anti₀ (pow_pos h0 2) (by rw [sq_abs]; linarith)

/-- The constant `(Σ_n ⟨n⟩^{-2})^{1/2}` of the bound `‖x‖_{h⁻¹} ≤ hm1Const · sup |x n|`. -/
def hm1Const : ℝ := Real.sqrt (∑' n : ℤ, sobolevModeWeight (-1) n)

theorem hm1Const_nonneg : 0 ≤ hm1Const := Real.sqrt_nonneg _

/-- Every bounded sequence lies in `h⁻¹`. -/
theorem mem_seqSobolev38_neg_one_of_bdd (x : ℤ → ℂ) (M : ℝ) (hx : ∀ n, ‖x n‖ ≤ M) :
    x ∈ seqSobolev38 (-1) := by
  rw [mem_seqSobolev38_iff]
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sobolevModeWeight_pos (-1) n).le (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hx n) 2)
      (sobolevModeWeight_pos (-1) n).le)
    (summable_sobolevModeWeight_neg_one.mul_right (M ^ 2))

/-- The `h⁻¹` norm of a bounded sequence is at most `hm1Const` times the bound. -/
theorem norm_carrierMk38_neg_one_le (x : ℤ → ℂ) (M : ℝ) (hx : ∀ n, ‖x n‖ ≤ M)
    (h : x ∈ seqSobolev38 (-1)) : ‖carrierMk38 (-1) x h‖ ≤ hm1Const * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hx 0)
  have h1 := carrier_hasSum_norm_sq38 (-1) (carrierMk38 (-1) x h)
  simp only [carrierCoe38_mk] at h1
  have h2 := summable_sobolevModeWeight_neg_one.hasSum.mul_right (M ^ 2)
  have hle : ‖carrierMk38 (-1) x h‖ ^ 2 ≤ (∑' n : ℤ, sobolevModeWeight (-1) n) * M ^ 2 :=
    hasSum_le (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hx n) 2)
      (sobolevModeWeight_pos (-1) n).le) h1 h2
  have hS : 0 ≤ ∑' n : ℤ, sobolevModeWeight (-1) n :=
    tsum_nonneg fun n => (sobolevModeWeight_pos (-1) n).le
  calc ‖carrierMk38 (-1) x h‖ = Real.sqrt (‖carrierMk38 (-1) x h‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∑' n : ℤ, sobolevModeWeight (-1) n) * M ^ 2) := Real.sqrt_le_sqrt hle
    _ = hm1Const * M := by rw [Real.sqrt_mul hS, Real.sqrt_sq hM, hm1Const]

/-! ### Coordinates, single modes, truncation -/

/-- The coordinate `x ↦ x n` as a continuous real-linear functional on `h^r`. -/
def carrierCoordCLM (r : ℝ) (n : ℤ) : SobolevCarrier38 r →L[ℝ] ℂ where
  toFun x := carrierCoe38 r x n
  map_add' _ _ := rfl
  map_smul' c x := by
    show (c : ℂ) * carrierCoe38 r x n = c • carrierCoe38 r x n
    rw [Complex.real_smul]
  cont := continuous_carrierCoe_apply38 r n

@[simp] theorem carrierCoordCLM_apply (r : ℝ) (n : ℤ) (x : SobolevCarrier38 r) :
    carrierCoordCLM r n x = carrierCoe38 r x n := rfl

/-- The Bochner integral in `h^r` is computed coordinatewise. -/
theorem carrierCoe38_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} (r : ℝ)
    {f : α → SobolevCarrier38 r} (hf : Integrable f μ) (n : ℤ) :
    carrierCoe38 r (∫ a, f a ∂μ) n = ∫ a, carrierCoe38 r (f a) n ∂μ :=
  ((carrierCoordCLM r n).integral_comp_comm hf).symm

/-- The oriented interval Bochner integral in `h^r` is computed coordinatewise. -/
theorem carrierCoe38_intervalIntegral (r : ℝ) {f : ℝ → SobolevCarrier38 r} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (n : ℤ) :
    carrierCoe38 r (∫ s in a..b, f s) n = ∫ s in a..b, carrierCoe38 r (f s) n :=
  ((carrierCoordCLM r n).intervalIntegral_comp_comm hf).symm

theorem single_mem_seqSobolev38 (r : ℝ) (n : ℤ) (c : ℂ) :
    (Pi.single n c : ℤ → ℂ) ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff]
  show Summable (fun m : ℤ => Real.rpow (japaneseBracket m) (2 * r) *
    ‖(Pi.single n c : ℤ → ℂ) m‖ ^ 2)
  refine summable_of_ne_finset_zero (s := {n}) (fun m hm => ?_)
  rw [Finset.mem_singleton] at hm
  simp [hm]

/-- `c ↦ c e_n` as a real-linear map into `h^r`. -/
def carrierSingleLin (r : ℝ) (n : ℤ) : ℂ →ₗ[ℝ] SobolevCarrier38 r where
  toFun c := carrierMk38 r (Pi.single n c) (single_mem_seqSobolev38 r n c)
  map_add' a b := carrierExt38 (funext fun m => by
    show (Pi.single n (a + b) : ℤ → ℂ) m = (Pi.single n a : ℤ → ℂ) m + (Pi.single n b : ℤ → ℂ) m
    by_cases h : m = n <;> simp [h])
  map_smul' c a := carrierExt38 (funext fun m => by
    show (Pi.single n (c • a) : ℤ → ℂ) m = (c : ℂ) * (Pi.single n a : ℤ → ℂ) m
    by_cases h : m = n <;> simp [h, Complex.real_smul])

theorem norm_carrierSingleLin_sq (r : ℝ) (n : ℤ) (c : ℂ) :
    ‖carrierSingleLin r n c‖ ^ 2 = sobolevModeWeight r n * ‖c‖ ^ 2 := by
  have h1 := carrier_hasSum_norm_sq38 r (carrierSingleLin r n c)
  have hF : ∀ m, m ≠ n →
      sobolevModeWeight r m * ‖carrierCoe38 r (carrierSingleLin r n c) m‖ ^ 2 = 0 := by
    intro m hm
    show sobolevModeWeight r m * ‖(Pi.single n c : ℤ → ℂ) m‖ ^ 2 = 0
    simp [hm]
  have h2 := hasSum_single (f := fun m : ℤ =>
    sobolevModeWeight r m * ‖carrierCoe38 r (carrierSingleLin r n c) m‖ ^ 2) n hF
  have e : sobolevModeWeight r n * ‖carrierCoe38 r (carrierSingleLin r n c) n‖ ^ 2 =
      sobolevModeWeight r n * ‖c‖ ^ 2 := by
    show sobolevModeWeight r n * ‖(Pi.single n c : ℤ → ℂ) n‖ ^ 2 = _
    simp
  rw [← e]
  exact h1.unique h2

/-- `c ↦ c e_n` as a continuous real-linear map into `h^r`. -/
def carrierSingle (r : ℝ) (n : ℤ) : ℂ →L[ℝ] SobolevCarrier38 r :=
  (carrierSingleLin r n).mkContinuous (Real.sqrt (sobolevModeWeight r n)) (fun c => le_of_eq (by
    rw [← Real.sqrt_sq (norm_nonneg (carrierSingleLin r n c)), norm_carrierSingleLin_sq,
      Real.sqrt_mul (sobolevModeWeight_pos r n).le, Real.sqrt_sq (norm_nonneg c)]))

@[simp] theorem carrierCoe38_carrierSingle (r : ℝ) (n : ℤ) (c : ℂ) :
    carrierCoe38 r (carrierSingle r n c) = Pi.single n c := rfl

/-- The truncation `P_N x` is the finite sum `Σ_{|n| ≤ N} x_n e_n`. -/
theorem projC38_eq_sum (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    projC38 r N x = ∑ n ∈ symmetricModes N, carrierSingle r n (carrierCoe38 r x n) := by
  apply carrierExt38
  funext m
  rw [carrierCoe38_projC38]
  have e : carrierCoe38 r (∑ n ∈ symmetricModes N, carrierSingle r n (carrierCoe38 r x n)) m =
      ∑ n ∈ symmetricModes N, carrierCoe38 r (carrierSingle r n (carrierCoe38 r x n)) m :=
    map_sum (carrierCoordCLM r m) _ _
  rw [e]
  simp only [carrierCoe38_carrierSingle, Pi.single_apply]
  rw [Finset.sum_ite_eq]

/-- Coordinatewise a.e.-strong measurability implies a.e.-strong measurability in `h^r`. -/
theorem aestronglyMeasurable_of_carrierCoe {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (r : ℝ) (f : α → SobolevCarrier38 r)
    (hf : ∀ n, AEStronglyMeasurable (fun a => carrierCoe38 r (f a) n) μ) :
    AEStronglyMeasurable f μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N a => projC38 r N (f a))
    (fun N => ?_) (ae_of_all _ fun a => tendsto_projC38 r (f a))
  simp_rw [projC38_eq_sum]
  exact (symmetricModes N).aestronglyMeasurable_fun_sum fun n _ =>
    (carrierSingle r n).continuous.comp_aestronglyMeasurable (hf n)

/-! ### `L¹ → H⁻¹` and `L² → H⁻¹` -/

/-- `|f̂(n)| ≤ ∫ |f|` (no integrability needed: both sides are the totalized integrals). -/
theorem norm_physicalFourier_le (f : PhysicalCircle → ℂ) (n : ℤ) :
    ‖physicalFourier f n‖ ≤ ∫ x, ‖f x‖ ∂spatialMeasure := by
  unfold physicalFourier fourierCoeff spatialMeasure
  refine (norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_)))
  simp only [norm_smul]
  rw [fourier_apply, Circle.norm_coe, one_mul]

theorem physicalFourier_add_of_integrable {f g : PhysicalCircle → ℂ}
    (hf : Integrable f spatialMeasure) (hg : Integrable g spatialMeasure) :
    physicalFourier (f + g) = physicalFourier f + physicalFourier g :=
  fourierCoeff.add hf hg

theorem physicalFourier_real_smul (c : ℝ) (f : PhysicalCircle → ℂ) (n : ℤ) :
    physicalFourier (c • f) n = (c : ℂ) * physicalFourier f n := by
  have e : (c • f : PhysicalCircle → ℂ) = fun x => (c : ℂ) * f x :=
    funext fun x => by simp [Complex.real_smul]
  unfold physicalFourier
  rw [e, fourierCoeff.const_mul]

theorem physicalFourier_congr_ae {f g : PhysicalCircle → ℂ} (h : f =ᵐ[spatialMeasure] g) :
    physicalFourier f = physicalFourier g :=
  fourierCoeff_congr_ae h

/-- `L¹ → h⁻¹` as a real-linear map (coefficients: the physical Fourier coefficients). -/
def l1ToHm1Lin : Lp ℂ 1 spatialMeasure →ₗ[ℝ] SobolevCarrier38 (-1) where
  toFun f := carrierMk38 (-1) (physicalFourier f)
    (mem_seqSobolev38_neg_one_of_bdd _ _ (fun n => norm_physicalFourier_le f n))
  map_add' f g := carrierExt38 (by
    show physicalFourier (⇑(f + g)) = physicalFourier ⇑f + physicalFourier ⇑g
    rw [physicalFourier_congr_ae (Lp.coeFn_add f g)]
    exact physicalFourier_add_of_integrable (L1.integrable_coeFn f) (L1.integrable_coeFn g))
  map_smul' c f := carrierExt38 (funext fun n => by
    show physicalFourier (⇑(c • f)) n = (c : ℂ) * physicalFourier ⇑f n
    rw [physicalFourier_congr_ae (Lp.coeFn_smul c f), physicalFourier_real_smul])

/-- The genuine continuous real-linear embedding `L¹(𝕋) → H⁻¹`, `‖·‖ ≤ hm1Const ‖·‖₁`. -/
def l1ToHm1 : Lp ℂ 1 spatialMeasure →L[ℝ] SobolevCarrier38 (-1) :=
  l1ToHm1Lin.mkContinuous hm1Const (fun f => by
    rw [L1.norm_eq_integral_norm]
    exact norm_carrierMk38_neg_one_le _ _ (fun n => norm_physicalFourier_le f n) _)

/-- Coefficient characterization of `l1ToHm1`. -/
theorem carrierCoe38_l1ToHm1 (f : Lp ℂ 1 spatialMeasure) :
    carrierCoe38 (-1) (l1ToHm1 f) = physicalFourier f := rfl

theorem norm_l1ToHm1_le (f : Lp ℂ 1 spatialMeasure) : ‖l1ToHm1 f‖ ≤ hm1Const * ‖f‖ := by
  show ‖l1ToHm1Lin f‖ ≤ _
  rw [L1.norm_eq_integral_norm]
  exact norm_carrierMk38_neg_one_le _ _ (fun n => norm_physicalFourier_le f n) _

open scoped Classical in
/-- Function-level form of `l1ToHm1`: the `H⁻¹` element of an integrable function (`0` exactly
when `f` is not integrable; every source use is certified by `carrierCoe38_fnToHm1`). -/
def fnToHm1 (f : PhysicalCircle → ℂ) : SobolevCarrier38 (-1) :=
  if hf : Integrable f spatialMeasure then l1ToHm1 (hf.toL1 f) else 0

/-- Coefficient characterization of `fnToHm1` on every integrable function. -/
theorem carrierCoe38_fnToHm1 {f : PhysicalCircle → ℂ} (hf : Integrable f spatialMeasure) :
    carrierCoe38 (-1) (fnToHm1 f) = physicalFourier f := by
  simp only [fnToHm1, hf, ↓reduceDIte]
  rw [carrierCoe38_l1ToHm1]
  exact physicalFourier_congr_ae hf.coeFn_toL1

theorem fnToHm1_of_not_integrable {f : PhysicalCircle → ℂ}
    (hf : ¬ Integrable f spatialMeasure) : fnToHm1 f = 0 := by
  simp only [fnToHm1, hf, ↓reduceDIte]

/-- `fnToHm1` depends only on the a.e. class. -/
theorem fnToHm1_congr_ae {f g : PhysicalCircle → ℂ} (h : f =ᵐ[spatialMeasure] g) :
    fnToHm1 f = fnToHm1 g := by
  by_cases hf : Integrable f spatialMeasure
  · have hg : Integrable g spatialMeasure := hf.congr h
    exact carrierExt38 (by
      rw [carrierCoe38_fnToHm1 hf, carrierCoe38_fnToHm1 hg, physicalFourier_congr_ae h])
  · have hg : ¬ Integrable g spatialMeasure := fun hg => hf (hg.congr h.symm)
    rw [fnToHm1_of_not_integrable hf, fnToHm1_of_not_integrable hg]

theorem norm_fnToHm1_le (f : PhysicalCircle → ℂ) :
    ‖fnToHm1 f‖ ≤ hm1Const * ∫ x, ‖f x‖ ∂spatialMeasure := by
  by_cases hf : Integrable f spatialMeasure
  · simp only [fnToHm1, hf, ↓reduceDIte]
    refine (norm_l1ToHm1_le _).trans (le_of_eq ?_)
    rw [L1.norm_eq_integral_norm]
    congr 1
    exact integral_congr_ae (hf.coeFn_toL1.mono fun x hx => by simp only [hx])
  · rw [fnToHm1_of_not_integrable hf, norm_zero]
    exact mul_nonneg hm1Const_nonneg (integral_nonneg fun _ => norm_nonneg _)

theorem sobolevModeWeight_neg_one_le_one (n : ℤ) : sobolevModeWeight (-1) n ≤ 1 := by
  have h := sobolevModeWeight_mono (show (-1 : ℝ) ≤ 0 by norm_num) n
  have e : sobolevModeWeight 0 n = 1 := by simp [sobolevModeWeight]
  rwa [e] at h

theorem integrable_of_physicalL2 (u : PhysicalL2) :
    Integrable (u : PhysicalCircle → ℂ) spatialMeasure := by
  have : IsProbabilityMeasure spatialMeasure := by unfold spatialMeasure; infer_instance
  exact (Lp.memLp u).integrable one_le_two

theorem physicalFourier_mem_neg_one (u : PhysicalL2) : physicalFourier u ∈ seqSobolev38 (-1) := by
  rw [mem_seqSobolev38_iff]
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sobolevModeWeight_pos (-1) n).le (sq_nonneg _))
    (fun n => mul_le_of_le_one_left (sq_nonneg _) (sobolevModeWeight_neg_one_le_one n))
    (summable_physicalFourier_sq u)

/-- `L² → h⁻¹` as a real-linear map. -/
def l2ToHm1Lin : PhysicalL2 →ₗ[ℝ] SobolevCarrier38 (-1) where
  toFun u := carrierMk38 (-1) (physicalFourier u) (physicalFourier_mem_neg_one u)
  map_add' u v := carrierExt38 (by
    show physicalFourier (⇑(u + v)) = physicalFourier ⇑u + physicalFourier ⇑v
    rw [physicalFourier_congr_ae (Lp.coeFn_add u v)]
    exact physicalFourier_add_of_integrable (integrable_of_physicalL2 u)
      (integrable_of_physicalL2 v))
  map_smul' c u := carrierExt38 (funext fun n => by
    show physicalFourier (⇑(c • u)) n = (c : ℂ) * physicalFourier ⇑u n
    rw [physicalFourier_congr_ae (Lp.coeFn_smul c u), physicalFourier_real_smul])

theorem norm_l2ToHm1Lin_le (u : PhysicalL2) : ‖l2ToHm1Lin u‖ ≤ 1 * ‖u‖ := by
  rw [one_mul]
  have h1 := carrier_hasSum_norm_sq38 (-1) (l2ToHm1Lin u)
  have h2 := hasSum_physicalFourier_sq u
  have hle : ‖l2ToHm1Lin u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    hasSum_le (fun n => mul_le_of_le_one_left (sq_nonneg _) (sobolevModeWeight_neg_one_le_one n))
      h1 h2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hle

/-- The genuine continuous real-linear embedding `L²(𝕋) → H⁻¹` (norm `≤ 1`). -/
def l2ToHm1 : PhysicalL2 →L[ℝ] SobolevCarrier38 (-1) :=
  l2ToHm1Lin.mkContinuous 1 norm_l2ToHm1Lin_le

/-- Coefficient characterization of `l2ToHm1`. -/
theorem carrierCoe38_l2ToHm1 (u : PhysicalL2) :
    carrierCoe38 (-1) (l2ToHm1 u) = physicalFourier u := rfl

theorem norm_l2ToHm1_le (u : PhysicalL2) : ‖l2ToHm1 u‖ ≤ ‖u‖ := by
  have h := norm_l2ToHm1Lin_le u
  rw [one_mul] at h
  exact h

/-- `l2ToHm1` is injective (an embedding). -/
theorem l2ToHm1_injective : Function.Injective l2ToHm1 := by
  intro u v h
  have hc : physicalFourier u = physicalFourier v := by
    rw [← carrierCoe38_l2ToHm1, ← carrierCoe38_l2ToHm1, h]
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, hc]

/-- Compatibility: on `L²` the function-level map is `l2ToHm1`. -/
theorem fnToHm1_physicalL2 (u : PhysicalL2) : fnToHm1 (u : PhysicalCircle → ℂ) = l2ToHm1 u :=
  carrierExt38 (by rw [carrierCoe38_fnToHm1 (integrable_of_physicalL2 u), carrierCoe38_l2ToHm1])

end LiebLiniger.FixedPeriod.ALLS.PdeB
