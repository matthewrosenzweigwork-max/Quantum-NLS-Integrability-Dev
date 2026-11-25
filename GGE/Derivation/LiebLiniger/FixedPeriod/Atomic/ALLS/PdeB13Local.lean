import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB11Group

/-! # Track B, contracts 17–19 (step 1): the local solution map as a fixed point of `L⁴` operators

For `0 < δ ≤ 1` the short-time objects of `PdeB5` are packaged as maps on `Lp` spaces of the slab
`[0,δ] × 𝕋`:
* `fW δ a ∈ L⁴`: the free spacetime field `e^{it∂ₓ²}a` (additive, `‖fW δ a‖ ≤ C ‖a‖`);
* `dW δ F ∈ L⁴`, `dV δ F ∈ C([0,δ], L²)`: the Duhamel outputs of `F ∈ L^{4/3}` (additive, bounded
  by `K δ^{1/16} ‖F‖`);
* `Ncub δ f ∈ L^{4/3}`: the cubic `2|f|²f` (`‖N f - N g‖ ≤ 3(‖f‖² + ‖g‖²)‖f - g‖`).
`Pic δ a f = fW δ a + dW δ (Ncub δ f)` is a `1/2`-contraction of the closed ball of radius `R` for
`‖a‖ ≤ M` (`LocData`); its fixed point `fp δ R a` represents the flow:
`l2Flow t a = freeL2 t a + dV δ (Ncub δ (fp δ R a)) t` on `[0,δ]` (`l2Flow_eq_local`), proved by
gluing the local solution to flow trajectories and global uniqueness (`duh_unique`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped ENNReal NNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

instance fact_one_le_four_thirds : Fact ((1 : ℝ≥0∞) ≤ 4 / 3) := ⟨one_le_four_thirds⟩

theorem norm_le_of_enorm_le' {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {x : E}
    {y : F} {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : ‖x‖ₑ ≤ c * ‖y‖ₑ) : ‖x‖ ≤ c.toReal * ‖y‖ := by
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hc enorm_ne_top) h
  rwa [ENNReal.toReal_mul, toReal_enorm, toReal_enorm] at h2

/-! ### Duhamel operators -/

theorem continuous_duhPair_fst (δ : ℝ) (F : ℝ × PhysicalCircle → ℂ) :
    Continuous (duhPair δ F).1 := by
  unfold duhPair
  split_ifs with h
  · exact h.choose_spec.cont
  · exact continuous_const

/-- The Duhamel `L²` trajectory of `F ∈ L^{4/3}` on `[0,δ]`. -/
def dV (δ : ℝ) (F : Lp ℂ (4 / 3) (slabMeasure δ)) : C(Set.Icc (0 : ℝ) δ, PhysicalL2) :=
  ⟨fun t => (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 t,
    (continuous_duhPair_fst δ _).comp continuous_subtype_val⟩

theorem dV_apply (δ : ℝ) (F : Lp ℂ (4 / 3) (slabMeasure δ)) (t : Set.Icc (0 : ℝ) δ) :
    dV δ F t = (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 t := rfl

/-- The Duhamel spacetime field of `F ∈ L^{4/3}` as an element of `L⁴([0,δ] × 𝕋)`. -/
def dW (δ : ℝ) (F : Lp ℂ (4 / 3) (slabMeasure δ)) : Lp ℂ 4 (slabMeasure δ) := by
  classical
  exact if h : MemLp (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 4 (slabMeasure δ) then h.toLp _
    else 0

section Duh

variable {δ : ℝ}

theorem duhOut_lp (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    IsDuhOut δ F (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 :=
  duhPair_spec hδ hδ1 (Lp.memLp F)

theorem duh_bounds : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ F : Lp ℂ (4 / 3) (slabMeasure δ),
      (∀ t ∈ Set.Icc 0 δ, ‖(duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 t‖ₑ ≤ K * tf δ * ‖F‖ₑ) ∧
      eLpNorm (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 4 (slabMeasure δ) ≤ K * tf δ * ‖F‖ₑ := by
  obtain ⟨K, hK, h⟩ := duhOut_bound
  refine ⟨K, hK, fun δ hδ hδ1 F => ?_⟩
  have := h δ hδ hδ1 _ _ _ (Lp.memLp F) (duhOut_lp hδ hδ1 F)
  rw [← Lp.enorm_def] at this
  exact this

theorem memLp_duhW (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    MemLp (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 4 (slabMeasure δ) := by
  obtain ⟨K, hK, h⟩ := duh_bounds
  exact (h δ hδ hδ1 F).2.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK.lt_top
    ENNReal.ofReal_lt_top) enorm_lt_top)

theorem dW_coeFn (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    (dW δ F : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 := by
  have h := memLp_duhW hδ hδ1 F
  unfold dW
  simp only [h, ↓reduceDIte]
  exact MemLp.coeFn_toLp h

theorem duhPair_sub (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F G : Lp ℂ (4 / 3) (slabMeasure δ)) :
    (∀ t ∈ Set.Icc 0 δ, (duhPair δ ((F - G : Lp ℂ (4 / 3) (slabMeasure δ)) : ℝ × PhysicalCircle → ℂ)).1 t =
      (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 t - (duhPair δ (G : ℝ × PhysicalCircle → ℂ)).1 t) ∧
    (duhPair δ ((F - G : Lp ℂ (4 / 3) (slabMeasure δ)) : ℝ × PhysicalCircle → ℂ)).2 =ᵐ[slabMeasure δ]
      (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 - (duhPair δ (G : ℝ × PhysicalCircle → ℂ)).2 := by
  have hF := integrable_of_memLp_slab (Lp.memLp F)
  have hG := integrable_of_memLp_slab (Lp.memLp G)
  have h1 := ((duhOut_lp hδ hδ1 F).sub (duhOut_lp hδ hδ1 G) hF hG).congr (hF.sub hG)
    (integrable_of_memLp_slab (Lp.memLp (F - G))) (Lp.coeFn_sub F G).symm
  exact (duhOut_lp hδ hδ1 (F - G)).unique h1

theorem dW_sub (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F G : Lp ℂ (4 / 3) (slabMeasure δ)) :
    dW δ (F - G) = dW δ F - dW δ G := by
  refine Lp.ext ?_
  filter_upwards [dW_coeFn hδ hδ1 (F - G), dW_coeFn hδ hδ1 F, dW_coeFn hδ hδ1 G,
    Lp.coeFn_sub (dW δ F) (dW δ G), (duhPair_sub hδ hδ1 F G).2] with p h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3, h5, Pi.sub_apply]

theorem dV_sub (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F G : Lp ℂ (4 / 3) (slabMeasure δ)) :
    dV δ (F - G) = dV δ F - dV δ G := by
  ext1 t
  rw [ContinuousMap.sub_apply, dV_apply, dV_apply, dV_apply]
  exact (duhPair_sub hδ hδ1 F G).1 t t.2

theorem dW_enorm_le {K : ℝ≥0∞}
    (hK : ∀ F : Lp ℂ (4 / 3) (slabMeasure δ),
      eLpNorm (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 4 (slabMeasure δ) ≤ K * tf δ * ‖F‖ₑ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    ‖dW δ F‖ₑ ≤ K * tf δ * ‖F‖ₑ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (dW_coeFn hδ hδ1 F)]
  exact hK F

end Duh

/-! ### The free field operator -/

/-- `W` is an `L⁴([0,δ] × 𝕋)` spacetime representative of `t ↦ e^{it∂ₓ²}a` on `[0,δ]`. -/
def IsFreeRep (δ : ℝ) (a : PhysicalL2) (W : ℝ × PhysicalCircle → ℂ) : Prop :=
  MemLp W 4 (slabMeasure δ) ∧ ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ)),
    (fun x => W (t, x)) =ᵐ[spatialMeasure] (freeL2 t a : PhysicalCircle → ℂ)

/-- The free field as an element of `L⁴([0,δ] × 𝕋)`. -/
def fW (δ : ℝ) (a : PhysicalL2) : Lp ℂ 4 (slabMeasure δ) := by
  classical
  exact if h : ∃ W, IsFreeRep δ a W then h.choose_spec.1.toLp _ else 0

theorem free_bound : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, δ ≤ 1 → ∀ a : PhysicalL2,
    ∃ W, IsFreeRep δ a W ∧ eLpNorm W 4 (slabMeasure δ) ≤ C * ‖a‖ₑ := by
  obtain ⟨C, hC, hfree⟩ := free_L4
  refine ⟨C, hC, fun δ hδ1 a => ?_⟩
  obtain ⟨W, hWm, hWb, hWs⟩ := hfree a
  have hle := slabMeasure_le_free hδ1
  have hb : eLpNorm W 4 (slabMeasure δ) ≤ C * ‖a‖ₑ := (eLpNorm_mono_measure _ hle).trans hWb
  refine ⟨W, ⟨hb.trans_lt (ENNReal.mul_lt_top hC.lt_top enorm_lt_top),
    ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc (by norm_num) hδ1) hWs⟩, hb⟩

theorem freeRep_ae_eq {δ : ℝ} {a : PhysicalL2} {W W' : ℝ × PhysicalCircle → ℂ}
    (h : IsFreeRep δ a W) (h' : IsFreeRep δ a W') : W =ᵐ[slabMeasure δ] W' := by
  refine ae_eq_of_slices h.1.aestronglyMeasurable h'.1.aestronglyMeasurable ?_
  filter_upwards [h.2, h'.2] with t h1 h2
  exact h1.trans h2.symm

theorem fW_coeFn {δ : ℝ} {a : PhysicalL2} {W : ℝ × PhysicalCircle → ℂ} (hW : IsFreeRep δ a W) :
    (fW δ a : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] W := by
  have hex : ∃ W, IsFreeRep δ a W := ⟨W, hW⟩
  unfold fW
  simp only [hex, ↓reduceDIte]
  exact (MemLp.coeFn_toLp _).trans (freeRep_ae_eq hex.choose_spec hW)

theorem freeRep_sub {δ : ℝ} {a b : PhysicalL2} {W W' : ℝ × PhysicalCircle → ℂ}
    (h : IsFreeRep δ a W) (h' : IsFreeRep δ b W') : IsFreeRep δ (a - b) (W - W') := by
  refine ⟨h.1.sub h'.1, ?_⟩
  filter_upwards [h.2, h'.2] with t h1 h2
  rw [freeL2_sub]
  filter_upwards [h1, h2, Lp.coeFn_sub (freeL2 t a) (freeL2 t b)] with x hx1 hx2 hx3
  rw [hx3]
  simp only [Pi.sub_apply, hx1, hx2]

theorem fW_sub {δ : ℝ} (hδ1 : δ ≤ 1) (a b : PhysicalL2) : fW δ (a - b) = fW δ a - fW δ b := by
  obtain ⟨C, -, hC⟩ := free_bound
  obtain ⟨W, hW, -⟩ := hC δ hδ1 a
  obtain ⟨W', hW', -⟩ := hC δ hδ1 b
  refine Lp.ext ?_
  filter_upwards [fW_coeFn (freeRep_sub hW hW'), fW_coeFn hW, fW_coeFn hW',
    Lp.coeFn_sub (fW δ a) (fW δ b)] with p h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, Pi.sub_apply, h2, h3]

/-! ### The cubic -/

/-- The cubic `2|f|²f` as a map `L⁴ → L^{4/3}` of the slab. -/
def Ncub (δ : ℝ) (f : Lp ℂ 4 (slabMeasure δ)) : Lp ℂ (4 / 3) (slabMeasure δ) :=
  (memLp_cubF f).toLp _

theorem Ncub_coeFn {δ : ℝ} (f : Lp ℂ 4 (slabMeasure δ)) :
    (Ncub δ f : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] cubF f :=
  MemLp.coeFn_toLp _

theorem Ncub_sub_enorm {δ : ℝ} (f g : Lp ℂ 4 (slabMeasure δ)) :
    ‖Ncub δ f - Ncub δ g‖ₑ ≤ 3 * (‖f‖ₑ ^ 2 + ‖g‖ₑ ^ 2) * ‖f - g‖ₑ := by
  have h1 : (Ncub δ f - Ncub δ g : Lp ℂ (4 / 3) (slabMeasure δ)) =ᵐ[slabMeasure δ]
      fun p => cubicNL (f p) - cubicNL (g p) := by
    filter_upwards [Lp.coeFn_sub (Ncub δ f) (Ncub δ g), Ncub_coeFn f, Ncub_coeFn g]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl
  rw [Lp.enorm_def, eLpNorm_congr_ae h1, Lp.enorm_def, Lp.enorm_def, Lp.enorm_def,
    eLpNorm_congr_ae (Lp.coeFn_sub f g)]
  exact eLpNorm_cubic_sub_le (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g)

theorem Ncub_sub_le {δ : ℝ} (f g : Lp ℂ 4 (slabMeasure δ)) :
    ‖Ncub δ f - Ncub δ g‖ ≤ 3 * (‖f‖ ^ 2 + ‖g‖ ^ 2) * ‖f - g‖ := by
  have h := norm_le_of_enorm_le' (c := 3 * (‖f‖ₑ ^ 2 + ‖g‖ₑ ^ 2))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.pow_ne_top enorm_ne_top, ENNReal.pow_ne_top enorm_ne_top⟩)) (Ncub_sub_enorm f g)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.pow_ne_top enorm_ne_top)
    (ENNReal.pow_ne_top enorm_ne_top), ENNReal.toReal_pow, ENNReal.toReal_pow, toReal_enorm,
    toReal_enorm, ENNReal.toReal_ofNat] at h

theorem Ncub_zero {δ : ℝ} : Ncub δ (0 : Lp ℂ 4 (slabMeasure δ)) = 0 := by
  refine Lp.ext ?_
  filter_upwards [Ncub_coeFn (0 : Lp ℂ 4 (slabMeasure δ)), Lp.coeFn_zero ℂ 4 (slabMeasure δ),
    Lp.coeFn_zero ℂ (4 / 3) (slabMeasure δ)] with p h1 h2 h3
  rw [h1, h3]
  simp only [cubF, h2, Pi.zero_apply, cubicNL_zero]

/-! ### Local data and the contraction -/

/-- The Picard map `f ↦ fW a + dW (N f)`. -/
def Pic (δ : ℝ) (a : PhysicalL2) (f : Lp ℂ 4 (slabMeasure δ)) : Lp ℂ 4 (slabMeasure δ) :=
  fW δ a + dW δ (Ncub δ f)

/-- Constants of the local theory for data of norm `≤ M`. -/
structure LocData (M δ R Kd Cf : ℝ) : Prop where
  hδ : 0 < δ
  hδ1 : δ ≤ 1
  hR : 0 < R
  hKd : 0 ≤ Kd
  hCf : 0 ≤ Cf
  hCM : Cf * M ≤ R / 2
  hsmall : 12 * Kd * R ^ 2 ≤ 1
  dW_le : ∀ F : Lp ℂ (4 / 3) (slabMeasure δ), ‖dW δ F‖ ≤ Kd * ‖F‖
  dV_le : ∀ (F : Lp ℂ (4 / 3) (slabMeasure δ)) (t : Set.Icc (0 : ℝ) δ), ‖dV δ F t‖ ≤ Kd * ‖F‖
  fW_le : ∀ a : PhysicalL2, ‖fW δ a‖ ≤ Cf * ‖a‖

theorem small_time (k A : ℝ) (hk : 0 ≤ k) (hA : 0 ≤ A) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ k * δ ^ (1 / 16 : ℝ) * A ≤ 1 := by
  refine ⟨((1 + k * A)⁻¹) ^ 16, by positivity,
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by nlinarith)), ?_⟩
  rw [show (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have h1 : 0 < 1 + k * A := by nlinarith
  rw [mul_comm k, mul_assoc, inv_mul_le_iff₀ h1]
  linarith

theorem locData_exists (M : ℝ) : ∃ δ R Kd Cf : ℝ, LocData M δ R Kd Cf := by
  obtain ⟨K, hK, hKb⟩ := duh_bounds
  obtain ⟨C, hC, hCb⟩ := free_bound
  set Cf := C.toReal
  set R : ℝ := 2 * (Cf * |M| + 1) with hR
  have hCf : 0 ≤ Cf := ENNReal.toReal_nonneg
  have hR0 : 0 < R := by positivity
  obtain ⟨δ, hδ, hδ1, hs⟩ := small_time K.toReal (12 * R ^ 2) ENNReal.toReal_nonneg (by positivity)
  have hKd : (K * tf δ).toReal = K.toReal * δ ^ (1 / 16 : ℝ) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hKt : K * tf δ ≠ ⊤ := ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top
  refine ⟨δ, R, (K * tf δ).toReal, Cf, hδ, hδ1, hR0, ENNReal.toReal_nonneg, hCf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    have : Cf * M ≤ Cf * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hCf
    linarith
  · rw [hKd]; nlinarith
  · intro F
    exact norm_le_of_enorm_le' hKt (dW_enorm_le (fun F => (hKb δ hδ hδ1 F).2) hδ hδ1 F)
  · intro F t
    exact norm_le_of_enorm_le' hKt ((hKb δ hδ hδ1 F).1 t t.2)
  · intro a
    obtain ⟨W, hW, hWb⟩ := hCb δ hδ1 a
    refine norm_le_of_enorm_le' hC ?_
    rw [Lp.enorm_def, eLpNorm_congr_ae (fW_coeFn hW)]
    exact hWb

section Contraction

variable {M δ R Kd Cf : ℝ}

theorem LocData.pic_sub (D : LocData M δ R Kd Cf) (a b : PhysicalL2)
    (f g : Lp ℂ 4 (slabMeasure δ)) :
    ‖Pic δ a f - Pic δ b g‖ ≤ Cf * ‖a - b‖ + Kd * (3 * (‖f‖ ^ 2 + ‖g‖ ^ 2) * ‖f - g‖) := by
  have e : Pic δ a f - Pic δ b g = fW δ (a - b) + dW δ (Ncub δ f - Ncub δ g) := by
    rw [fW_sub D.hδ1, dW_sub D.hδ D.hδ1, Pic, Pic]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (D.fW_le _) ((D.dW_le _).trans ?_))
  exact mul_le_mul_of_nonneg_left (Ncub_sub_le f g) D.hKd

theorem LocData.pic_norm (D : LocData M δ R Kd Cf) (a : PhysicalL2)
    (f : Lp ℂ 4 (slabMeasure δ)) : ‖Pic δ a f‖ ≤ Cf * ‖a‖ + Kd * (3 * ‖f‖ ^ 2 * ‖f‖) := by
  have h := D.pic_sub a 0 f 0
  have e : Pic δ 0 0 = 0 := by
    have h0 := fW_sub D.hδ1 0 0
    have h1 := dW_sub D.hδ D.hδ1 0 0
    rw [sub_zero, sub_self] at h0 h1
    rw [Pic, Ncub_zero, h0, h1, add_zero]
  rw [e, sub_zero, sub_zero, sub_zero, norm_zero] at h
  simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] using h

theorem LocData.contr (D : LocData M δ R Kd Cf) {f g : Lp ℂ 4 (slabMeasure δ)}
    (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) :
    Kd * (3 * (‖f‖ ^ 2 + ‖g‖ ^ 2) * ‖f - g‖) ≤ 2⁻¹ * ‖f - g‖ := by
  have h1 : ‖f‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have h2 : ‖g‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have h3 : Kd * (3 * (‖f‖ ^ 2 + ‖g‖ ^ 2)) ≤ 2⁻¹ := by
    have := D.hsmall
    nlinarith [D.hKd]
  have := mul_le_mul_of_nonneg_right h3 (norm_nonneg (f - g))
  linarith [this, show Kd * (3 * (‖f‖ ^ 2 + ‖g‖ ^ 2) * ‖f - g‖) =
    Kd * (3 * (‖f‖ ^ 2 + ‖g‖ ^ 2)) * ‖f - g‖ by ring]

theorem LocData.fixed_small (D : LocData M δ R Kd Cf) {a : PhysicalL2} (ha : ‖a‖ ≤ M)
    {f : Lp ℂ 4 (slabMeasure δ)} (hf : ‖f‖ ≤ R) (hfix : Pic δ a f = f) : ‖f‖ ≤ 2 / 3 * R := by
  have h := D.pic_norm a f
  rw [hfix] at h
  have h1 : Cf * ‖a‖ ≤ R / 2 := (mul_le_mul_of_nonneg_left ha D.hCf).trans D.hCM
  have h2 : Kd * (3 * ‖f‖ ^ 2 * ‖f‖) ≤ 4⁻¹ * ‖f‖ := by
    have hsq : ‖f‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
    have h3 : Kd * (3 * ‖f‖ ^ 2) ≤ 4⁻¹ := by nlinarith [D.hsmall, D.hKd]
    have := mul_le_mul_of_nonneg_right h3 (norm_nonneg f)
    linarith [this, show Kd * (3 * ‖f‖ ^ 2 * ‖f‖) = Kd * (3 * ‖f‖ ^ 2) * ‖f‖ by ring]
  linarith

theorem LocData.exists_fixed (D : LocData M δ R Kd Cf) {a : PhysicalL2} (ha : ‖a‖ ≤ M) :
    ∃ f : Lp ℂ 4 (slabMeasure δ), ‖f‖ ≤ R ∧ Pic δ a f = f := by
  set s : Set (Lp ℂ 4 (slabMeasure δ)) := Metric.closedBall 0 R with hs
  have hmem : ∀ f, f ∈ s ↔ ‖f‖ ≤ R := fun f => by rw [hs, mem_closedBall_zero_iff]
  have hcomp : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hmaps : Set.MapsTo (Pic δ a) s s := by
    intro f hf
    rw [hmem] at hf ⊢
    refine (D.pic_norm a f).trans ?_
    have h1 : Cf * ‖a‖ ≤ R / 2 := (mul_le_mul_of_nonneg_left ha D.hCf).trans D.hCM
    have hsq : ‖f‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
    have h3 : Kd * (3 * ‖f‖ ^ 2) ≤ 4⁻¹ := by nlinarith [D.hsmall, D.hKd]
    have := mul_le_mul_of_nonneg_right h3 (norm_nonneg f)
    have e2 : Kd * (3 * ‖f‖ ^ 2 * ‖f‖) = Kd * (3 * ‖f‖ ^ 2) * ‖f‖ := by ring
    linarith [D.hR]
  have hlip : LipschitzWith (2⁻¹ : ℝ≥0) (hmaps.restrict (Pic δ a) s s) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    simp only [Set.MapsTo.restrict, Subtype.dist_eq]
    rw [dist_eq_norm, dist_eq_norm]
    have h := D.pic_sub a a f g
    rw [sub_self, norm_zero, mul_zero, zero_add] at h
    refine h.trans ((D.contr ((hmem _).1 f.2) ((hmem _).1 g.2)).trans (le_of_eq ?_))
    simp
  have hcon : ContractingWith (2⁻¹ : ℝ≥0) (hmaps.restrict (Pic δ a) s s) :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num, hlip⟩
  have h0 : (0 : Lp ℂ 4 (slabMeasure δ)) ∈ s := by rw [hmem, norm_zero]; exact D.hR.le
  obtain ⟨f, hf, hfix, -⟩ := ContractingWith.exists_fixedPoint' hcomp hmaps hcon h0 (edist_ne_top _ _)
  exact ⟨f, (hmem f).1 hf, hfix⟩

theorem LocData.fixed_unique (D : LocData M δ R Kd Cf) {a : PhysicalL2}
    {f g : Lp ℂ 4 (slabMeasure δ)} (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) (hfa : Pic δ a f = f)
    (hga : Pic δ a g = g) : f = g := by
  have h := D.pic_sub a a f g
  rw [hfa, hga, sub_self, norm_zero, mul_zero, zero_add] at h
  have h2 := h.trans (D.contr hf hg)
  have : ‖f - g‖ = 0 := by linarith [norm_nonneg (f - g)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end Contraction

/-- The fixed point of the Picard map in the closed ball of radius `R`. -/
def fp (δ R : ℝ) (a : PhysicalL2) : Lp ℂ 4 (slabMeasure δ) := by
  classical
  exact if h : ∃ f : Lp ℂ 4 (slabMeasure δ), ‖f‖ ≤ R ∧ Pic δ a f = f then h.choose else 0

section FixedPoint

variable {M δ R Kd Cf : ℝ}

theorem LocData.fp_spec (D : LocData M δ R Kd Cf) {a : PhysicalL2} (ha : ‖a‖ ≤ M) :
    ‖fp δ R a‖ ≤ R ∧ Pic δ a (fp δ R a) = fp δ R a := by
  have hex := D.exists_fixed ha
  unfold fp
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

theorem LocData.fp_eq (D : LocData M δ R Kd Cf) {a : PhysicalL2} (ha : ‖a‖ ≤ M)
    {f : Lp ℂ 4 (slabMeasure δ)} (hf : ‖f‖ ≤ R) (hfa : Pic δ a f = f) : fp δ R a = f :=
  D.fixed_unique (D.fp_spec ha).1 hf (D.fp_spec ha).2 hfa

theorem LocData.fp_small (D : LocData M δ R Kd Cf) {a : PhysicalL2} (ha : ‖a‖ ≤ M) :
    ‖fp δ R a‖ ≤ 2 / 3 * R :=
  D.fixed_small ha (D.fp_spec ha).1 (D.fp_spec ha).2

theorem LocData.fp_lip (D : LocData M δ R Kd Cf) {a b : PhysicalL2} (ha : ‖a‖ ≤ M)
    (hb : ‖b‖ ≤ M) : ‖fp δ R a - fp δ R b‖ ≤ 2 * Cf * ‖a - b‖ := by
  have h := D.pic_sub a b (fp δ R a) (fp δ R b)
  rw [(D.fp_spec ha).2, (D.fp_spec hb).2] at h
  have h2 := D.contr (D.fp_spec ha).1 (D.fp_spec hb).1
  linarith

end FixedPoint

/-! ### Identification with the flow -/

namespace MassHyp

variable {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}

theorem mono (H : MassHyp u U a b) {c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) : MassHyp u U c d where
  cont := H.cont.mono (Set.Icc_subset_Icc hac hdb)
  memLp := H.memLp.mono_measure
    (Measure.restrict_mono (Set.prod_mono (Set.Icc_subset_Icc hac hdb) le_rfl) le_rfl)
  slice := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc hac hdb) H.slice
  coeff n s hs t ht := H.coeff n s (Set.Icc_subset_Icc hac hdb hs) t (Set.Icc_subset_Icc hac hdb ht)

end MassHyp

theorem isDuhSol_l2Flow (a : PhysicalL2) : IsDuhSol fun t => l2Flow t a := by
  obtain ⟨hc, U, hr, h4, -, hD⟩ := (l2Flow_solution a).1
  exact ⟨hc, U, hr, h4, hD⟩

/-- An interval solution on `[0,δ]` is the flow there. -/
theorem eq_l2Flow_of_massHyp {δ : ℝ} (hδ : 0 < δ) {v : ℝ → PhysicalL2}
    {W : ℝ × PhysicalCircle → ℂ} (H : MassHyp v W 0 δ) (a : PhysicalL2) (hv0 : v 0 = a) :
    ∀ t ∈ Set.Icc 0 δ, v t = l2Flow t a := by
  classical
  obtain ⟨hc, U, hr, h4, -, hD⟩ := (l2Flow_solution a).1
  obtain ⟨hcb, Ub, hrb, h4b, -, hDb⟩ := (l2Flow_solution (v δ)).1
  set z : ℝ → PhysicalL2 := fun t =>
    if t < 0 then l2Flow t a else if t ≤ δ then v t else l2Flow (t + -δ) (v δ) with hz
  set Z : ℝ × PhysicalCircle → ℂ :=
    glueU 0 U (glueU δ W (fun p => Ub (p.1 + -δ, p.2))) with hZ
  have HM : ∀ m : ℕ, MassHyp z Z (-(m * δ)) (m * δ) := by
    intro m
    have hm0 : (0 : ℝ) ≤ m * δ := by positivity
    have P1 : MassHyp z U (-(m * δ)) 0 :=
      (massHyp_of_isDuhSol hc hr h4 hD (-(m * δ)) 0).congr (fun t ht => by
        simp only [hz]
        rcases ht.2.lt_or_eq with hlt | heq
        · rw [ite_t hlt]
        · rw [heq, ite_f (lt_irrefl 0), ite_t hδ.le, hv0, (l2Flow_solution a).2])
        (fun _ _ _ => rfl)
    have P2 : MassHyp z W 0 δ :=
      H.congr (fun t ht => by simp only [hz, ite_f (not_lt.2 ht.1), ite_t ht.2])
        (fun _ _ _ => rfl)
    have P3' := (massHyp_of_isDuhSol hcb hrb h4b hDb 0 (m * δ)).shift (-δ)
    simp only [sub_neg_eq_add, zero_add] at P3'
    have P3 : MassHyp z (fun p => Ub (p.1 + -δ, p.2)) δ (m * δ + δ) :=
      P3'.congr (fun t ht => by
        simp only [hz, ite_f (not_lt.2 (hδ.le.trans ht.1))]
        rcases ht.1.lt_or_eq with hlt | heq
        · rw [ite_f (not_le.2 hlt)]
        · rw [ite_t heq.ge, ← heq, add_neg_cancel, (l2Flow_solution (v δ)).2])
        (fun _ _ _ => rfl)
    have G := P1.glue (P2.glue P3 hδ.le (by linarith)) (by linarith) (by linarith)
    exact G.mono le_rfl (by linarith)
  obtain ⟨hzc, hzr, hz4, hzD⟩ := isDuhSol_of_massHyp hδ HM
  have hz0 : z 0 = l2Flow 0 a := by
    simp only [hz, lt_irrefl, ↓reduceIte, hδ.le, hv0, (l2Flow_solution a).2]
  have heq := duh_unique ⟨hzc, Z, hzr, hz4, hzD⟩ (isDuhSol_l2Flow a) hz0
  intro t ht
  have := congrFun heq t
  simp only [hz, ite_f (not_lt.2 ht.1), ite_t ht.2] at this
  exact this

/-- The local solution built from the fixed point is an interval solution on `[0,δ]`. -/
theorem massHyp_of_local {δ : ℝ} {v : ℝ → PhysicalL2} {W : ℝ × PhysicalCircle → ℂ}
    {u0 : PhysicalL2} (hv : Continuous v) (hW : MemLp W 4 (slabMeasure δ))
    (hsl : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ)),
      (fun x => W (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ))
    (hv0 : v 0 = u0)
    (hD : ∀ t ∈ Set.Icc 0 δ, l2ToHm1 (v t) = freeProp (-1) t (l2ToHm1 u0) + duhH (cubF W) t) :
    MassHyp v W 0 δ := by
  have hW' : MemLp W 4 (slabM 0 δ) := by
    rw [slabMeasure_eq] at hW; exact hW
  refine MassHyp.of_base hv.continuousOn hW' hsl fun n t ht => ?_
  have hF : Integrable (cubF W) (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod
      spatialMeasure) := integrable_cubic_slabM hW'
  refine (coeff_duhamel_iff (u := v) (U := W) n t).1 ?_
  have h := congrArg (fun z => carrierCoe38 (-1) z n) (hD t ht)
  rw [coe38_add, carrierCoe38_duhH hF ht, carrierCoe38_freeProp_l2ToHm1] at h
  rw [hv0]
  exact h

/-- **The flow on `[0,δ]` is given by the fixed point.** -/
theorem LocData.l2Flow_eq {M δ R Kd Cf : ℝ} (D : LocData M δ R Kd Cf) {a : PhysicalL2}
    (ha : ‖a‖ ≤ M) (t : Set.Icc (0 : ℝ) δ) :
    l2Flow t a = freeL2 t a + dV δ (Ncub δ (fp δ R a)) t := by
  obtain ⟨C, -, hCb⟩ := free_bound
  obtain ⟨Wa, hWa, -⟩ := hCb δ D.hδ1 a
  set f := fp δ R a with hfdef
  set F := Ncub δ f with hFdef
  have hout := duhOut_lp D.hδ D.hδ1 F
  set v : ℝ → PhysicalL2 := fun t => freeL2 t a + (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 t
    with hv
  set W : ℝ × PhysicalCircle → ℂ := Wa + (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).2 with hW
  have hWm : MemLp W 4 (slabMeasure δ) := hWa.1.add (memLp_duhW D.hδ D.hδ1 F)
  have hv0 : v 0 = a := by
    have h0 : (duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 0 = 0 := l2ToHm1_injective (by
      rw [hout.ident 0 ⟨le_rfl, D.hδ.le⟩, map_zero]
      simp [duhH])
    simp only [hv, freeL2_zero, h0, add_zero]
  have hsl : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ)),
      (fun x => W (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ) := by
    filter_upwards [hWa.2, ae_restrict_of_ae hout.slice] with t h1 h2
    filter_upwards [h1, h2, Lp.coeFn_add (freeL2 t a) ((duhPair δ (F : ℝ × PhysicalCircle → ℂ)).1 t)]
      with x hx1 hx2 hx3
    simp only [hv, hW]
    rw [hx3, Pi.add_apply, Pi.add_apply, ← hx1, ← hx2]
  have hfW : (f : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] W := by
    have hfix := (D.fp_spec ha).2
    rw [← hfdef] at hfix
    have e : (f : ℝ × PhysicalCircle → ℂ) = (Pic δ a f : ℝ × PhysicalCircle → ℂ) := by rw [hfix]
    rw [e]
    filter_upwards [Lp.coeFn_add (fW δ a) (dW δ (Ncub δ f)), fW_coeFn hWa,
      dW_coeFn D.hδ D.hδ1 (Ncub δ f)] with p h1 h2 h3
    rw [Pic, h1, Pi.add_apply, h2, h3]
    rfl
  have hFW : (F : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] cubF W := by
    filter_upwards [Ncub_coeFn f, hfW] with p h1 h2
    rw [hFdef, h1]
    simp only [cubF, h2]
  have hD : ∀ t ∈ Set.Icc 0 δ,
      l2ToHm1 (v t) = freeProp (-1) t (l2ToHm1 a) + duhH (cubF W) t := by
    intro t ht
    simp only [hv]
    rw [map_add, l2ToHm1_freeL2, hout.ident t ht,
      duhH_congr (integrable_of_memLp_slab (Lp.memLp F))
        (integrable_of_memLp_slab (memLp_cubic hWm)) hFW ht]
    rfl
  have hc : Continuous v := (continuous_freeL2 a).add hout.cont
  have H := massHyp_of_local hc hWm hsl hv0 hD
  rw [← eq_l2Flow_of_massHyp D.hδ H a hv0 t t.2]
  rfl

/-- **Local Lipschitz bound** of the flow on `[0,δ]`. -/
theorem LocData.l2Flow_lip {M δ R Kd Cf : ℝ} (D : LocData M δ R Kd Cf) {a b : PhysicalL2}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (t : Set.Icc (0 : ℝ) δ) :
    ‖l2Flow t a - l2Flow t b‖ ≤ (1 + Cf) * ‖a - b‖ := by
  rw [D.l2Flow_eq ha, D.l2Flow_eq hb]
  have e : freeL2 t a + dV δ (Ncub δ (fp δ R a)) t - (freeL2 t b + dV δ (Ncub δ (fp δ R b)) t) =
      (freeL2 t a - freeL2 t b) + dV δ (Ncub δ (fp δ R a) - Ncub δ (fp δ R b)) t := by
    rw [dV_sub D.hδ D.hδ1, ContinuousMap.sub_apply]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_freeL2_sub]
  have h1 := D.dV_le (Ncub δ (fp δ R a) - Ncub δ (fp δ R b)) t
  have h2 := Ncub_sub_le (fp δ R a) (fp δ R b)
  have h3 := D.contr (D.fp_spec ha).1 (D.fp_spec hb).1
  have h4 := D.fp_lip ha hb
  have h5 : Kd * ‖Ncub δ (fp δ R a) - Ncub δ (fp δ R b)‖ ≤ 2⁻¹ * ‖fp δ R a - fp δ R b‖ :=
    (mul_le_mul_of_nonneg_left h2 D.hKd).trans h3
  nlinarith [norm_nonneg (a - b)]

end LiebLiniger.FixedPeriod.ALLS.PdeB
