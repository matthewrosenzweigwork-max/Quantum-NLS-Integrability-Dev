import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5DuhOut

/-! # Track B, package 2: local existence on `[0,δ]` by contraction in `L⁴([0,δ] × 𝕋)`

For `u₀ ∈ L²`, with `W₀` the free `L⁴` representative of `e^{it∂ₓ²}u₀` (`free_L4`) and the chosen
Duhamel outputs `duhPair`, the Picard map `f ↦ W₀ + Duh(N(f))` acts on the complete space
`Lp ℂ 4 ([0,δ] × 𝕋)`. On the closed ball of radius `R = 2 C ‖u₀‖` it is a `1/2`-contraction as soon
as `12 K δ^{1/16} R² ≤ 1` (`K`: Duhamel constant, `C`: free constant). Mathlib's contraction theorem
on a complete subset gives the fixed point; the solution is `v(t) = e^{it∂ₓ²}u₀ + Duh(t)` with the
actual `H⁻¹` Bochner Duhamel identity on `[0,δ]` and spacetime representative `W₀ + w`.
The lifespan condition depends on `u₀` only through `‖u₀‖` (`lifespan`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped ENNReal NNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

instance fact_one_le_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The cubic of a spacetime function. -/
def cubF (f : ℝ × PhysicalCircle → ℂ) : ℝ × PhysicalCircle → ℂ := fun p => cubicNL (f p)

/-- The time factor `δ^{1/16}`. -/
abbrev tf (δ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (δ ^ (1 / 16 : ℝ))

theorem enorm_Lp_eq {δ : ℝ} (f : Lp ℂ 4 (slabMeasure δ)) :
    ‖f‖ₑ = eLpNorm (f : ℝ × PhysicalCircle → ℂ) 4 (slabMeasure δ) := Lp.enorm_def f

/-- The Picard map on `L⁴([0,δ] × 𝕋)` with free part `W₀`. -/
def picard (δ : ℝ) (W0 : ℝ × PhysicalCircle → ℂ) (f : Lp ℂ 4 (slabMeasure δ)) :
    Lp ℂ 4 (slabMeasure δ) := by
  classical
  exact if h : MemLp (W0 + (duhPair δ (cubF f)).2) 4 (slabMeasure δ) then h.toLp _ else 0

section Picard

variable {K : ℝ≥0∞} {δ : ℝ} {W0 : ℝ × PhysicalCircle → ℂ}

/-- The hypotheses: `K` is a constant for `duhOut_bound`, `0 < δ ≤ 1`, `W₀ ∈ L⁴` of the slab. -/
structure PicardHyp (K : ℝ≥0∞) (δ : ℝ) (W0 : ℝ × PhysicalCircle → ℂ) : Prop where
  hK : K ≠ ⊤
  hbound : ∀ (F : ℝ × PhysicalCircle → ℂ) (v : ℝ → PhysicalL2) (w : ℝ × PhysicalCircle → ℂ),
      MemLp F (4 / 3) (slabMeasure δ) → IsDuhOut δ F v w →
      (∀ t ∈ Set.Icc 0 δ, ‖v t‖ₑ ≤ K * tf δ * eLpNorm F (4 / 3) (slabMeasure δ)) ∧
      eLpNorm w 4 (slabMeasure δ) ≤ K * tf δ * eLpNorm F (4 / 3) (slabMeasure δ)
  hδ : 0 < δ
  hδ1 : δ ≤ 1
  hW0 : MemLp W0 4 (slabMeasure δ)

theorem memLp_cubF (f : Lp ℂ 4 (slabMeasure δ)) : MemLp (cubF f) (4 / 3) (slabMeasure δ) :=
  memLp_cubic (Lp.memLp f)

theorem PicardHyp.out (H : PicardHyp K δ W0) (f : Lp ℂ 4 (slabMeasure δ)) :
    IsDuhOut δ (cubF f) (duhPair δ (cubF f)).1 (duhPair δ (cubF f)).2 :=
  duhPair_spec H.hδ H.hδ1 (memLp_cubF f)

theorem PicardHyp.wd_le (H : PicardHyp K δ W0) (f : Lp ℂ 4 (slabMeasure δ)) :
    eLpNorm (duhPair δ (cubF f)).2 4 (slabMeasure δ) ≤ K * tf δ * (3 * ‖f‖ₑ ^ 3) := by
  refine ((H.hbound _ _ _ (memLp_cubF f) (H.out f)).2).trans ?_
  rw [enorm_Lp_eq]
  exact emL (eLpNorm_cubic_le (Lp.aestronglyMeasurable f))

theorem PicardHyp.memLp (H : PicardHyp K δ W0) (f : Lp ℂ 4 (slabMeasure δ)) :
    MemLp (W0 + (duhPair δ (cubF f)).2) 4 (slabMeasure δ) := by
  have hw : MemLp (duhPair δ (cubF f)).2 4 (slabMeasure δ) :=
    (H.wd_le f).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top H.hK.lt_top ENNReal.ofReal_lt_top)
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top (by rw [enorm_Lp_eq]; exact Lp.memLp f))))
  exact H.hW0.add hw

theorem PicardHyp.coeFn (H : PicardHyp K δ W0) (f : Lp ℂ 4 (slabMeasure δ)) :
    (picard δ W0 f : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] W0 + (duhPair δ (cubF f)).2 := by
  have h := H.memLp f
  unfold picard
  simp only [h, ↓reduceDIte]
  exact MemLp.coeFn_toLp h

theorem PicardHyp.norm_le (H : PicardHyp K δ W0) (f : Lp ℂ 4 (slabMeasure δ)) :
    ‖picard δ W0 f‖ₑ ≤ eLpNorm W0 4 (slabMeasure δ) + K * tf δ * (3 * ‖f‖ₑ ^ 3) := by
  rw [enorm_Lp_eq, eLpNorm_congr_ae (H.coeFn f)]
  exact (eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl (H.wd_le f))

theorem PicardHyp.edist_le (H : PicardHyp K δ W0) (f g : Lp ℂ 4 (slabMeasure δ)) :
    edist (picard δ W0 f) (picard δ W0 g) ≤
      K * tf δ * (3 * (‖f‖ₑ ^ 2 + ‖g‖ₑ ^ 2)) * edist f g := by
  have hFi := integrable_of_memLp_slab (memLp_cubF f)
  have hGi := integrable_of_memLp_slab (memLp_cubF g)
  have hsub := (H.out f).sub (H.out g) hFi hGi
  have hmem : MemLp (cubF f - cubF g) (4 / 3) (slabMeasure δ) := (memLp_cubF f).sub (memLp_cubF g)
  have hb := (H.hbound _ _ _ hmem hsub).2
  rw [Lp.edist_def, eLpNorm_congr_ae ((H.coeFn f).sub (H.coeFn g)), add_sub_add_left_eq_sub]
  refine hb.trans ?_
  rw [mul_assoc (K * tf δ), Lp.edist_def, enorm_Lp_eq, enorm_Lp_eq]
  exact emL (eLpNorm_cubic_sub_le (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g))

end Picard

/-- ENNReal bookkeeping: `12 x ≤ 1 → 6 x ≤ 1/2`. -/
theorem six_le_half {x : ℝ≥0∞} (h : 12 * x ≤ 1) : 6 * x ≤ 2⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le]
  calc 6 * x * 2 = 12 * x := by ring
    _ ≤ 1 := h

/-- **Contraction step**: a fixed point of the Picard map in the ball of radius `R = 2 C‖u₀‖`. -/
theorem picard_fixed {K : ℝ≥0∞} {δ : ℝ} {W0 : ℝ × PhysicalCircle → ℂ} (H : PicardHyp K δ W0)
    {A : ℝ≥0∞} (hA : A ≠ ⊤) (hW0A : eLpNorm W0 4 (slabMeasure δ) ≤ A)
    (hsmall : 12 * (K * tf δ * (2 * A) ^ 2) ≤ 1) :
    ∃ f : Lp ℂ 4 (slabMeasure δ), picard δ W0 f = f ∧ ‖f‖ₑ ≤ 2 * A := by
  set R : ℝ≥0∞ := 2 * A with hR
  have hRt : R ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hA
  set x : ℝ≥0∞ := K * tf δ * R ^ 2 with hx
  have h6 : 6 * x ≤ 2⁻¹ := six_le_half hsmall
  set s : Set (Lp ℂ 4 (slabMeasure δ)) := {f | ‖f‖ₑ ≤ R} with hs
  have hmem : ∀ f, f ∈ s ↔ ‖f‖ₑ ≤ R := fun f => Iff.rfl
  have hcomp : IsComplete s := (isClosed_le continuous_enorm continuous_const).isComplete
  have hmaps : Set.MapsTo (picard δ W0) s s := by
    intro f hf
    rw [hmem] at hf ⊢
    refine (H.norm_le f).trans ?_
    have h3 : K * tf δ * (3 * ‖f‖ₑ ^ 3) ≤ A := by
      calc K * tf δ * (3 * ‖f‖ₑ ^ 3) ≤ K * tf δ * (3 * R ^ 3) := by gcongr
        _ = 3 * x * R := by rw [hx]; ring
        _ ≤ 2⁻¹ * R := by
            gcongr
            calc 3 * x ≤ 6 * x := by gcongr; norm_num
              _ ≤ 2⁻¹ := h6
        _ = A := by
            rw [hR, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, one_mul]
    calc eLpNorm W0 4 (slabMeasure δ) + K * tf δ * (3 * ‖f‖ₑ ^ 3) ≤ A + A := add_le_add hW0A h3
      _ = R := by rw [hR, two_mul]
  have hlip : LipschitzWith (2⁻¹ : ℝ≥0) (hmaps.restrict (picard δ W0) s s) := by
    intro f g
    simp only [Set.MapsTo.restrict, Subtype.edist_eq]
    have hf := (hmem f).1 f.2
    have hg := (hmem g).1 g.2
    refine (H.edist_le f g).trans ?_
    gcongr
    calc K * tf δ * (3 * (‖(f : Lp ℂ 4 (slabMeasure δ))‖ₑ ^ 2 + ‖(g : Lp ℂ 4 (slabMeasure δ))‖ₑ ^ 2))
        ≤ K * tf δ * (3 * (R ^ 2 + R ^ 2)) := by gcongr
      _ = 6 * x := by rw [hx]; ring
      _ ≤ 2⁻¹ := h6
      _ = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := by simp
  have hcon : ContractingWith (2⁻¹ : ℝ≥0) (hmaps.restrict (picard δ W0) s s) :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num, hlip⟩
  have h0 : (0 : Lp ℂ 4 (slabMeasure δ)) ∈ s := by rw [hmem, enorm_zero]; exact zero_le
  have hfin : edist (0 : Lp ℂ 4 (slabMeasure δ)) (picard δ W0 0) ≠ ⊤ := by
    rw [edist_comm, edist_eq_enorm_sub, sub_zero]
    exact ne_top_of_le_ne_top hRt ((hmem _).1 (hmaps h0))
  obtain ⟨f, hf, hfix, -⟩ := ContractingWith.exists_fixedPoint' hcomp hmaps hcon h0 hfin
  exact ⟨f, hfix, (hmem f).1 hf⟩

/-- **Local existence on `[0,δ]`** under the smallness condition `12 K δ^{1/16} (2C‖u₀‖)² ≤ 1`:
a continuous `L²` trajectory with `v 0 = u₀`, an `L⁴([0,δ] × 𝕋)` spacetime representative, and the
actual `H⁻¹` Bochner Duhamel identity on `[0,δ]`. -/
theorem local_solution : ∃ K C : ℝ≥0∞, K ≠ ⊤ ∧ C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ u0 : PhysicalL2, 12 * (K * tf δ * (2 * (C * ‖u0‖ₑ)) ^ 2) ≤ 1 →
    ∃ (v : ℝ → PhysicalL2) (W : ℝ × PhysicalCircle → ℂ),
      Continuous v ∧ v 0 = u0 ∧ MemLp W 4 (slabMeasure δ) ∧
      (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ)),
        (fun x => W (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ)) ∧
      ∀ t ∈ Set.Icc 0 δ, l2ToHm1 (v t) = freeProp (-1) t (l2ToHm1 u0) + duhH (cubF W) t := by
  obtain ⟨K, hK, hbd⟩ := duhOut_bound
  obtain ⟨C, hC, hfree⟩ := free_L4
  refine ⟨K, C, hK, hC, fun δ hδ hδ1 u0 hsmall => ?_⟩
  obtain ⟨W0, -, hW0b, hW0s⟩ := hfree u0
  have hle := slabMeasure_le_free hδ1
  have hW0slab : eLpNorm W0 4 (slabMeasure δ) ≤ C * ‖u0‖ₑ :=
    (eLpNorm_mono_measure _ hle).trans hW0b
  have hW0mem : MemLp W0 4 (slabMeasure δ) :=
    hW0slab.trans_lt (ENNReal.mul_lt_top hC.lt_top enorm_lt_top)
  have H : PicardHyp K δ W0 := ⟨hK, hbd δ hδ hδ1, hδ, hδ1, hW0mem⟩
  obtain ⟨f, hfix, -⟩ := picard_fixed H (ENNReal.mul_ne_top hC enorm_ne_top) hW0slab hsmall
  have hout := H.out f
  have hFmem := memLp_cubF f
  refine ⟨fun t => freeL2 t u0 + (duhPair δ (cubF f)).1 t, W0 + (duhPair δ (cubF f)).2,
    (continuous_freeL2 u0).add hout.cont, ?_, H.memLp f, ?_, ?_⟩
  · have h0 : (duhPair δ (cubF f)).1 0 = 0 := l2ToHm1_injective (by
      rw [hout.ident 0 ⟨le_rfl, hδ.le⟩, map_zero]
      simp [duhH])
    simp only [freeL2_zero, h0, add_zero]
  · have hs1 : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ)),
        (fun x => W0 (t, x)) =ᵐ[spatialMeasure] (freeL2 t u0 : PhysicalCircle → ℂ) :=
      ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc (by norm_num) hδ1) hW0s
    filter_upwards [hs1, ae_restrict_of_ae hout.slice] with t h1 h2
    filter_upwards [h1, h2, Lp.coeFn_add (freeL2 t u0) ((duhPair δ (cubF f)).1 t)]
      with x hx1 hx2 hx3
    rw [hx3, Pi.add_apply, Pi.add_apply, ← hx1, ← hx2]
  · intro t ht
    have hfW : (f : ℝ × PhysicalCircle → ℂ) =ᵐ[slabMeasure δ] W0 + (duhPair δ (cubF f)).2 := by
      have := H.coeFn f
      rw [hfix] at this
      exact this
    have hFW : cubF f =ᵐ[slabMeasure δ] cubF (W0 + (duhPair δ (cubF f)).2) := by
      filter_upwards [hfW] with p hp
      simp only [cubF, hp]
    have hWmem : MemLp (cubF (W0 + (duhPair δ (cubF f)).2)) (4 / 3) (slabMeasure δ) :=
      memLp_cubic (H.memLp f)
    rw [map_add, l2ToHm1_freeL2, hout.ident t ht,
      duhH_congr (integrable_of_memLp_slab hFmem) (integrable_of_memLp_slab hWmem) hFW ht]

/-- **The lifespan depends only on a bound for `‖u₀‖`.** -/
theorem lifespan_exists {K C : ℝ≥0∞} (hK : K ≠ ⊤) (hC : C ≠ ⊤) (M : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ u0 : PhysicalL2, ‖u0‖ ≤ M →
      12 * (K * tf δ * (2 * (C * ‖u0‖ₑ)) ^ 2) ≤ 1 := by
  set Q : ℝ≥0∞ := 12 * (K * (2 * (C * ENNReal.ofReal M)) ^ 2) with hQdef
  have hQ : Q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.mul_ne_top hK
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top))))
  set A : ℝ := Q.toReal with hA
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have h1A : 0 < 1 + A := by linarith
  refine ⟨((1 + A)⁻¹) ^ 16, by positivity,
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith)), fun u0 hu0 => ?_⟩
  have htf : tf (((1 + A)⁻¹) ^ 16) = ENNReal.ofReal ((1 + A)⁻¹) := by
    rw [tf, show (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have hu : ‖u0‖ₑ ≤ ENNReal.ofReal M := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hu0
  calc 12 * (K * tf (((1 + A)⁻¹) ^ 16) * (2 * (C * ‖u0‖ₑ)) ^ 2)
      ≤ 12 * (K * tf (((1 + A)⁻¹) ^ 16) * (2 * (C * ENNReal.ofReal M)) ^ 2) := by gcongr
    _ = tf (((1 + A)⁻¹) ^ 16) * Q := by rw [hQdef]; ring
    _ = ENNReal.ofReal ((1 + A)⁻¹) * ENNReal.ofReal A := by rw [htf, hA, ENNReal.ofReal_toReal hQ]
    _ = ENNReal.ofReal ((1 + A)⁻¹ * A) := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_le_iff₀ h1A, mul_one]
        linarith

end LiebLiniger.FixedPeriod.ALLS.PdeB
