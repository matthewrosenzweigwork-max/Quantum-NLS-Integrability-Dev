import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs
import QuantumNLS.Local020Core
import QuantumNLS.Local020Mul1
import QuantumNLS.Local020Entry
import QuantumNLS.Local020Refl
import QuantumNLS.Local020Scale

/-! LOCAL-020 stage S6a: periodic translation on `L²(0,L;ℂ²)`.

`Ty y x = x + y` if `x + y ≤ L`, else `x + y - L` (rotation of `(0, L]`), measure preserving on `μI L` for `0 ≤ y ≤ L`.
`Wt y f = f ∘ Ty y` is a linear isometric equivalence (inverse `Wt (L - y)`).  For periodic (`σ = 1`) domains it carries the
graph of `𝓛_u` to that of `𝓛_{u ∘ Ty y}` (`inter_trans`), fixes the free doublet at `n = 0`, hence
`B_0(u ∘ T_y) = B_0(u)` (`trans_reduced0`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Topology QuantumNLS.LocalSpectral QuantumNLS.Local020Abs QuantumNLS.Local020Mul1
open scoped ENNReal

namespace QuantumNLS.Local020Trans

variable {L κ : ℝ}

def Ty (L y x : ℝ) : ℝ := if x + y ≤ L then x + y else x + y - L

theorem measurable_Ty (L y : ℝ) : Measurable (Ty L y) := by
  unfold Ty
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

theorem Ty_Ty {x y : ℝ} (hx : (0 : ℝ) < x) (hxL : x ≤ L) : Ty L y (Ty L (L - y) x) = x := by
  unfold Ty
  by_cases h1 : x + (L - y) ≤ L
  · rw [if_pos h1]
    have h2 : ¬ (x + (L - y) + y ≤ L) := by intro h; linarith
    rw [if_neg h2]; ring
  · rw [if_neg h1]
    have h2 : x + (L - y) - L + y ≤ L := by linarith
    rw [if_pos h2]; ring

theorem Ty_mp {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) : MeasurePreserving (Ty L y) (μI L) (μI L) := by
  refine ⟨measurable_Ty L y, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_Ty L y) hA]
  unfold μI
  rw [Measure.restrict_apply (measurable_Ty L y hA), Measure.restrict_apply hA]
  have e1 : Ty L y ⁻¹' A ∩ Ioc 0 L =
      ((fun x => x + y) ⁻¹' (A ∩ Ioc y L)) ∪ ((fun x => x + (y - L)) ⁻¹' (A ∩ Ioc 0 y)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_union, Ty]
    constructor
    · rintro ⟨hxA, hx0, hxL⟩
      by_cases h : x + y ≤ L
      · left; rw [if_pos h] at hxA; exact ⟨hxA, by linarith, h⟩
      · right; rw [if_neg h] at hxA
        have e : x + y - L = x + (y - L) := by ring
        rw [e] at hxA
        exact ⟨hxA, by linarith, by linarith⟩
    · rintro (⟨hxA, h1, h2⟩ | ⟨hxA, h1, h2⟩)
      · refine ⟨?_, by linarith, by linarith⟩
        rw [if_pos h2]; exact hxA
      · have h : ¬ (x + y ≤ L) := by intro h; linarith
        refine ⟨?_, by linarith, by linarith⟩
        rw [if_neg h]
        have e : x + y - L = x + (y - L) := by ring
        rw [e]; exact hxA
  have hm1 : MeasurableSet ((fun x => x + y) ⁻¹' (A ∩ Ioc y L)) :=
    (measurable_add_const y) (hA.inter measurableSet_Ioc)
  have hm2 : MeasurableSet ((fun x => x + (y - L)) ⁻¹' (A ∩ Ioc 0 y)) :=
    (measurable_add_const (y - L)) (hA.inter measurableSet_Ioc)
  have hd : Disjoint ((fun x => x + y) ⁻¹' (A ∩ Ioc y L)) ((fun x => x + (y - L)) ⁻¹' (A ∩ Ioc 0 y)) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    simp only [mem_preimage, mem_inter_iff, mem_Ioc] at h1 h2
    linarith [h1.2.2, h2.2.1]
  rw [e1, measure_union hd hm2, measure_preimage_add_right, measure_preimage_add_right]
  have e2 : A ∩ Ioc 0 L = (A ∩ Ioc y L) ∪ (A ∩ Ioc 0 y) := by
    rw [← Set.inter_union_distrib_left, Set.union_comm, Ioc_union_Ioc_eq_Ioc hy0 hy1]
  rw [e2, measure_union _ (hA.inter measurableSet_Ioc), add_comm]
  rw [Set.disjoint_left]
  intro x h1 h2
  simp only [mem_inter_iff, mem_Ioc] at h1 h2
  linarith [h1.2.1, h2.2.2]

/-- The rotation operator. -/
def WtLI {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) : H2 L →ₗᵢ[ℂ] H2 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (Ty L y) (Ty_mp hy0 hy1)

theorem WtLI_ae {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (f : H2 L) :
    (WtLI hy0 hy1 f : ℝ → E2) =ᵐ[μI L] fun x => (f : ℝ → E2) (Ty L y x) :=
  Lp.coeFn_compMeasurePreserving f (Ty_mp hy0 hy1)

theorem WtLI_inv {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (f : H2 L) :
    WtLI (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) (WtLI hy0 hy1 f) = f := by
  apply Lp.ext
  have hmp := Ty_mp (sub_nonneg.2 hy1) (by linarith : L - y ≤ L)
  filter_upwards [WtLI_ae (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) (WtLI hy0 hy1 f),
    hmp.quasiMeasurePreserving.ae_eq_comp (WtLI_ae hy0 hy1 f),
    (ae_restrict_mem measurableSet_Ioc : ∀ᵐ x ∂(μI L), x ∈ Ioc 0 L)] with x a b c
  rw [a]
  simp only [Function.comp] at b
  rw [b, Ty_Ty c.1 c.2]

def Wt {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) : H2 L ≃ₗᵢ[ℂ] H2 L :=
  LinearIsometryEquiv.ofSurjective (WtLI hy0 hy1)
    (fun g => ⟨WtLI (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) g, by
      have := WtLI_inv (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) g
      simpa [sub_sub_cancel] using this⟩)

theorem Wt_ae {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (f : H2 L) :
    (Wt hy0 hy1 f : ℝ → E2) =ᵐ[μI L] fun x => (f : ℝ → E2) (Ty L y x) := WtLI_ae hy0 hy1 f

section Rep

variable {f : H2 L} {g h : ℝ → E2}

theorem rep_diff (hL : 0 < L) (hrep : IsH1Rep L f g h) {a b : ℝ} (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) :
    g b = g a + ∫ s in a..b, h s := by
  have hi := rep_intervalIntegrable hL.le hrep
  have h0a : IntervalIntegrable h volume 0 a := hi.mono_set (by
    rw [uIcc_of_le hL.le, uIcc_of_le ha.1]; exact Icc_subset_Icc_right ha.2)
  have h0b : IntervalIntegrable h volume 0 b := hi.mono_set (by
    rw [uIcc_of_le hL.le, uIcc_of_le hb.1]; exact Icc_subset_Icc_right hb.2)
  have := intervalIntegral.integral_interval_sub_left h0b h0a
  rw [hrep.2.2 b hb, hrep.2.2 a ha, ← this]
  abel

theorem isH1Rep_trans (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (hrep : IsH1Rep L f g h)
    (hbc : g L = g 0) :
    IsH1Rep L (Wt hy0 hy1 f) (fun x => g (Ty L y x)) (fun x => h (Ty L y x)) := by
  have hmp := Ty_mp hy0 hy1
  refine ⟨?_, hrep.2.1.comp_measurePreserving hmp, ?_⟩
  · filter_upwards [Wt_ae hy0 hy1 f, hmp.quasiMeasurePreserving.ae_eq_comp hrep.1] with x a b
    rw [a]; exact b
  · intro x hx
    have hi := rep_intervalIntegrable hL.le hrep
    have T0 : Ty L y 0 = y := by simp [Ty, hy1]
    have hy : y ∈ Icc 0 L := ⟨hy0, hy1⟩
    simp only
    rw [T0]
    by_cases hxy : x + y ≤ L
    · have hT : Ty L y x = x + y := by simp [Ty, hxy]
      rw [hT, rep_diff hL hrep hy ⟨by linarith [hx.1], hxy⟩]
      have : ∫ s in (0:ℝ)..x, h (Ty L y s) = ∫ s in (0:ℝ)..x, h (s + y) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hx.1] at hs
        simp only [Ty]
        rw [if_pos (by linarith [hs.2])]
      rw [this, intervalIntegral.integral_comp_add_right (fun s => h s) y, zero_add]
    · have hT : Ty L y x = x + y - L := by simp [Ty, hxy]
      rw [hT]
      push_neg at hxy
      have hLy : L - y ∈ Icc (0 : ℝ) x := ⟨by linarith, by linarith⟩
      have hint : IntervalIntegrable (fun s => h (Ty L y s)) volume 0 x := by
        have this : IntegrableOn (fun s => h (Ty L y s)) (Ioc 0 L) volume :=
          (hrep.2.1.comp_measurePreserving hmp).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2
          (this.mono_set (Ioc_subset_Ioc_right hx.2))
      have hi1 : IntervalIntegrable (fun s => h (Ty L y s)) volume 0 (L - y) :=
        hint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hLy.2)
      have hi2 : IntervalIntegrable (fun s => h (Ty L y s)) volume (L - y) x :=
        hint.mono_set (by rw [uIcc_of_le hLy.2, uIcc_of_le hx.1]; exact Icc_subset_Icc hLy.1 le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      have I1 : ∫ s in (0:ℝ)..(L - y), h (Ty L y s) = ∫ s in y..L, h s := by
        have : ∫ s in (0:ℝ)..(L - y), h (Ty L y s) = ∫ s in (0:ℝ)..(L - y), h (s + y) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le (by linarith)] at hs
          simp only [Ty]
          rw [if_pos (by linarith [hs.2])]
        rw [this, intervalIntegral.integral_comp_add_right (fun s => h s) y]
        congr 1 <;> ring
      have I2 : ∫ s in (L - y)..x, h (Ty L y s) = ∫ s in (0:ℝ)..(x + y - L), h s := by
        have : ∫ s in (L - y)..x, h (Ty L y s) = ∫ s in (L - y)..x, h (s + (y - L)) := by
          apply intervalIntegral.integral_congr_ae
          refine Filter.Eventually.of_forall (fun s hs => ?_)
          rw [uIoc_of_le hLy.2] at hs
          simp only [Ty]
          rw [if_neg (by linarith [hs.1])]
          congr 1; ring
        rw [this, intervalIntegral.integral_comp_add_right (fun s => h s) (y - L)]
        congr 1 <;> ring
      rw [I1, I2]
      have hL1 := rep_diff hL hrep hy (⟨hL.le, le_rfl⟩ : L ∈ Icc 0 L)
      have h0 := hrep.2.2 (x + y - L) ⟨by linarith, by linarith [hx.2]⟩
      rw [h0, ← add_assoc, ← hL1, hbc]

end Rep

theorem Wt_apply {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (f : H2 L) : Wt hy0 hy1 f = WtLI hy0 hy1 f := rfl

theorem fwd (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (u : ℝ → ℂ) {f φ : H2 L}
    (h : (f, φ) ∈ LuGraph L κ u 1) :
    (Wt hy0 hy1 f, Wt hy0 hy1 φ) ∈ LuGraph L κ (fun x => u (Ty L y x)) 1 := by
  obtain ⟨g, d, hrep, hbc, hφ⟩ := h
  have hbc' : g L = g 0 := by simpa using hbc
  refine ⟨_, _, isH1Rep_trans hL hy0 hy1 hrep hbc', ?_, ?_⟩
  · simp only [Units.val_one, Int.cast_one, one_smul]
    by_cases hy : y = 0
    · subst hy; simp [Ty, hbc', hL.le]
    · have h1 : Ty L y L = y := by
        have : ¬ (L + y ≤ L) := by intro h; exact hy (le_antisymm (by linarith) hy0)
        simp [Ty, this]
      have h2 : Ty L y 0 = y := by simp [Ty, hy1]
      rw [h1, h2]
  · have hmp := Ty_mp hy0 hy1
    filter_upwards [Wt_ae hy0 hy1 φ, hmp.quasiMeasurePreserving.ae_eq_comp hφ] with x a b
    rw [a]; exact b

theorem inter_trans (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (u : ℝ → ℂ) :
    Inter (LuGraph L κ u 1) (LuGraph L κ (fun x => u (Ty L y x)) 1) (Wt hy0 hy1) 1 0 := by
  refine ⟨one_mul 1, fun f φ => ⟨fun h => ?_, fun h => ?_⟩, fun f φ h => by simpa using h⟩
  · have := fwd hL hy0 hy1 u h
    simpa using this
  · have h1 : (Wt hy0 hy1 f, Wt hy0 hy1 φ) ∈ LuGraph L κ (fun x => u (Ty L y x)) 1 := by simpa using h
    have h2 := fwd hL (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) _ h1
    have hf : Wt (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) (Wt hy0 hy1 f) = f :=
      WtLI_inv hy0 hy1 f
    have hφ : Wt (sub_nonneg.2 hy1) (by linarith : L - y ≤ L) (Wt hy0 hy1 φ) = φ :=
      WtLI_inv hy0 hy1 φ
    rw [hf, hφ] at h2
    have hu : (fun x => (fun x => u (Ty L y x)) (Ty L (L - y) x)) =ᵐ[μI L] u := by
      filter_upwards [(ae_restrict_mem measurableSet_Ioc : ∀ᵐ x ∂(μI L), x ∈ Ioc 0 L)] with x hx
      simp only [Ty_Ty hx.1 hx.2]
    rwa [Local020Scale.LuGraph_congr_ae hu] at h2

theorem pm_zero (L : ℝ) : pm L 0 = 0 := by unfold pm; simp

theorem parity_zero : parity 0 = 1 := by simp [parity]

theorem chiFun_zero (j : Fin 2) (x : ℝ) : chiFun L 0 j x = chiFun L 0 j 0 := by
  have : rate L 0 j = 0 := by unfold rate; rw [pm_zero]; simp
  simp [chiFun, this]

theorem Wt_chi0 (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (j : Fin 2) :
    Wt hy0 hy1 (chi L 0 j) = chi L 0 j := by
  apply Lp.ext
  have hmp := Ty_mp hy0 hy1
  have hb := hmp.quasiMeasurePreserving.ae_eq_comp (memLp_chiFun L 0 j).coeFn_toLp
  filter_upwards [Wt_ae hy0 hy1 (chi L 0 j), hb, (memLp_chiFun L 0 j).coeFn_toLp] with x a b c
  rw [a]
  have b' : (chi L 0 j : ℝ → E2) (Ty L y x) = chiFun L 0 j (Ty L y x) := b
  have c' : (chi L 0 j : ℝ → E2) x = chiFun L 0 j x := c
  rw [b', c', chiFun_zero, chiFun_zero (x := x)]

theorem doublet_rel0 (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) :
    QuantumNLS.Local020Core.DoubletRel (L := L) (Wt hy0 hy1) (LinearIsometryEquiv.refl ℂ E2) 0 0 := by
  unfold QuantumNLS.Local020Core.DoubletRel
  ext v : 1
  simp only [ContinuousLinearMap.comp_apply, ic_apply, LinearIsometryEquiv.coe_refl, id_eq]
  rw [embed_apply, map_add, map_smul, map_smul, Wt_chi0 hL, Wt_chi0 hL]

/-- **S6a.** Periodic translation does not change the reduced matrix at the free index `n = 0`. -/
theorem trans_reduced0 (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (r : ℝ) (u : ℝ → ℂ) :
    (SmallCompression L κ (fun x => u (Ty L y x)) 0 r ↔ SmallCompression L κ u 0 r) ∧
    ∀ (h' : SmallCompression L κ (fun x => u (Ty L y x)) 0 r) (hh : SmallCompression L κ u 0 r),
      reducedMatrix2 L κ (fun x => u (Ty L y x)) 0 r h' = reducedMatrix2 L κ u 0 r hh := by
  have h : Inter (LuGraph L κ u (parity 0)) (LuGraph L κ (fun x => u (Ty L y x)) (parity 0)) (Wt hy0 hy1) 1 0 := by
    rw [parity_zero]; exact inter_trans hL hy0 hy1 u
  have hn : center L 0 = 0 + 1 * center L 0 := by ring
  obtain ⟨hs, hr⟩ := QuantumNLS.Local020Core.reduced_transport (κ := κ) r h (Or.inl rfl) hn
    (doublet_rel0 hL hy0 hy1)
  refine ⟨hs, fun h' hh => ?_⟩
  rw [hr h' hh, pm_zero]
  ext v : 1
  simp [cjE_apply]
  rfl

end QuantumNLS.Local020Trans

#print axioms QuantumNLS.Local020Trans.trans_reduced0
#print axioms QuantumNLS.Local020Trans.inter_trans
