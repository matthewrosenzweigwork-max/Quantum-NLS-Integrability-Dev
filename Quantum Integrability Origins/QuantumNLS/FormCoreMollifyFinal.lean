import Mathlib
import QuantumNLS.FormCoreAssembly
import QuantumNLS.FormCoreMollify

/-!
# R-1602B09D `CC:F03:core`: the mollification step under `CoreHyp`

`mollifyCore`: for `μ = ρ dx` with `CoreHyp ρ`, a bounded measurable `g` vanishing off a compact `S ⊆ {ρ > 0}` with `N_μ(g) < ∞` is approximable by `C_c^∞`.
Printed argument: `ρ ≥ c > 0` on a compact neighborhood `T` of `S`; the unweighted energy of `g` is finite
(pairs in `T²` are bounded by `c⁻² ρ(x)ρ(y)|Dg|²`, pairs `x ∈ S`, `y ∉ T` by `M² · 2/(η² + (x-y)²)`; here `∫ 2/(η²+z²) dz = 2π/η`),
and `N_μ(r) ≤ B ∫ r² + B² E_u(r)` since `ρ ≤ B`; the mollifications `mol n g` converge to `g` in both unweighted norms (`FormCoreMollify`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.FormCore

variable {ρ : ℝ → ℝ}

theorem lintegral_muRho_le (H : CoreHyp ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(muRho ρ) ≤ ENNReal.ofReal B * ∫⁻ x, f x := by
  unfold muRho
  rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x)) volume
    (show Measurable fun x => ENNReal.ofReal (ρ x) from ENNReal.measurable_ofReal.comp H.cont.measurable) hf,
    ← lintegral_const_mul _ hf]
  exact lintegral_mono fun x => by
    show ENNReal.ofReal (ρ x) * f x ≤ _
    gcongr
    exact hB x

theorem formN_le_unweighted (H : CoreHyp ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B) {r : ℝ → ℝ} (hr : Measurable r) :
    formN (muRho ρ) r ≤ ENNReal.ofReal B * L2u r + ENNReal.ofReal B * (ENNReal.ofReal B * Eu r) := by
  unfold formN
  refine add_le_add ?_ ?_
  · exact lintegral_muRho_le H hB (ENNReal.measurable_ofReal.comp (hr.pow_const 2))
  · unfold formE Eu
    haveI := H.fin
    have hFm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (dq r p) :=
      ENNReal.measurable_ofReal.comp (measurable_dq hr)
    rw [lintegral_prod _ hFm.aemeasurable, lintegral_prod _ hFm.aemeasurable]
    have hinner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (dq r (x, y)) ∂(muRho ρ) ≤
        ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (dq r (x, y)) :=
      fun x => lintegral_muRho_le H hB (hFm.comp measurable_prodMk_left)
    have hm2 : Measurable fun x : ℝ => ∫⁻ y, ENNReal.ofReal (dq r (x, y)) :=
      hFm.lintegral_prod_right'
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dq r (x, y)) ∂(muRho ρ) ∂(muRho ρ)
        ≤ ENNReal.ofReal B * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dq r (x, y)) ∂(muRho ρ) := by
          refine lintegral_muRho_le H hB ?_
          exact (hFm.lintegral_prod_right' (ν := muRho ρ))
      _ ≤ ENNReal.ofReal B * (ENNReal.ofReal B * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dq r (x, y))) := by
          gcongr
          calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dq r (x, y)) ∂(muRho ρ)
              ≤ ∫⁻ x, ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (dq r (x, y)) := lintegral_mono hinner
            _ = ENNReal.ofReal B * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dq r (x, y)) := lintegral_const_mul _ hm2

theorem formE_eq_unweighted (H : CoreHyp ρ) {g : ℝ → ℝ} (hg : Measurable g) :
    formE (muRho ρ) g =
      ∫⁻ p, ENNReal.ofReal (ρ p.1 * ρ p.2 * dq g p) ∂(volume.prod volume) := by
  haveI := H.fin
  have hρm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp H.cont.measurable
  have hFm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (dq g p) :=
    ENNReal.measurable_ofReal.comp (measurable_dq hg)
  have hGm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (ρ p.1 * ρ p.2 * dq g p) :=
    ENNReal.measurable_ofReal.comp (((H.cont.measurable.comp measurable_fst).mul
      (H.cont.measurable.comp measurable_snd)).mul (measurable_dq hg))
  have hpt : ∀ x y : ℝ, ENNReal.ofReal (ρ x * ρ y * dq g (x, y)) =
      ENNReal.ofReal (ρ x) * (ENNReal.ofReal (ρ y) * ENNReal.ofReal (dq g (x, y))) := fun x y => by
    rw [ENNReal.ofReal_mul (mul_nonneg (H.nonneg x) (H.nonneg y)), ENNReal.ofReal_mul (H.nonneg x), mul_assoc]
  have hHm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (ρ p.2) * ENNReal.ofReal (dq g p) :=
    (hρm.comp measurable_snd).mul hFm
  unfold formE
  rw [lintegral_prod _ hFm.aemeasurable, lintegral_prod _ hGm.aemeasurable]
  have hinner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (dq g (x, y)) ∂(muRho ρ) =
      ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (dq g (x, y)) := fun x =>
    lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x)) volume hρm
      (hFm.comp measurable_prodMk_left)
  have hmx : Measurable fun x : ℝ => ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (dq g (x, y)) :=
    hHm.lintegral_prod_right'
  calc ∫⁻ x, (∫⁻ y, ENNReal.ofReal (dq g (x, y)) ∂(muRho ρ)) ∂(muRho ρ)
      = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (dq g (x, y))) ∂(muRho ρ) :=
        lintegral_congr fun x => hinner x
    _ = ∫⁻ x, ENNReal.ofReal (ρ x) * ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (dq g (x, y)) := by
        unfold muRho
        exact lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x)) volume hρm hmx
    _ = _ := by
        refine lintegral_congr fun x => ?_
        simp_rw [hpt]
        exact (lintegral_const_mul _ (hHm.comp measurable_prodMk_left)).symm

/-! ### Finiteness of the unweighted energy -/

theorem Eu_lt_top (H : CoreHyp ρ) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    {S : Set ℝ} (hS : IsCompact S) (hSP : S ⊆ {x | 0 < ρ x}) (hg0 : ∀ x, x ∉ S → g x = 0)
    (hN : formN (muRho ρ) g < ⊤) : Eu g < ⊤ := by
  have hPopen : IsOpen {x : ℝ | 0 < ρ x} := isOpen_lt continuous_const H.cont
  obtain ⟨η, hη, hηsub⟩ := hS.exists_cthickening_subset_open hPopen hSP
  have hT : IsCompact (Metric.cthickening η S) := hS.cthickening
  obtain ⟨c, hc0, hc⟩ := hT.exists_forall_le' (f := ρ) (a := 0) H.cont.continuousOn
    (fun x hx => hηsub hx)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set T := Metric.cthickening η S with hTdef
  have hST : S ⊆ T := Metric.self_subset_cthickening S
  set F1 : ℝ × ℝ → ℝ≥0∞ := fun p => S.indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
    ENNReal.ofReal (Kc η (p.1 - p.2)) with hF1
  set F2 : ℝ × ℝ → ℝ≥0∞ := fun p => S.indicator (fun _ => (1 : ℝ≥0∞)) p.2 *
    ENNReal.ofReal (Kc η (p.1 - p.2)) with hF2
  set W : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (ρ p.1 * ρ p.2 * dq g p) with hW
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hF1m : Measurable F1 :=
    ((measurable_const.indicator hSm).comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp ((measurable_Kc η).comp (measurable_fst.sub measurable_snd)))
  have hF2m : Measurable F2 :=
    ((measurable_const.indicator hSm).comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp ((measurable_Kc η).comp (measurable_fst.sub measurable_snd)))
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp (((H.cont.measurable.comp measurable_fst).mul
      (H.cont.measurable.comp measurable_snd)).mul (measurable_dq hg))
  -- far pairs
  have hfar : ∀ a b : ℝ, a ∈ S → b ∉ T → η ≤ |a - b| := by
    intro a b ha hb
    by_contra hlt
    push Not at hlt
    exact hb (Metric.mem_cthickening_of_dist_le b a η S ha (by rw [Real.dist_eq, abs_sub_comm]; exact hlt.le))
  have hkern : ∀ a b : ℝ, a ∈ S → b ∉ T →
      ENNReal.ofReal (dq g (a, b)) ≤ ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Kc η (a - b)) := by
    intro a b ha hb
    have hz := hfar a b ha hb
    have hz2 : η ^ 2 ≤ (a - b) ^ 2 := by
      have := pow_le_pow_left₀ hη.le hz 2
      rwa [sq_abs] at this
    have hzpos : 0 < (a - b) ^ 2 := lt_of_lt_of_le (by positivity) hz2
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold dq
    simp only [hg0 b (fun h => hb (hST h)), sub_zero]
    rw [Kc_eq hη, div_le_iff₀ hzpos]
    have h1 : (g a) ^ 2 ≤ M ^ 2 := by
      have := hM a
      nlinarith [abs_nonneg (g a), sq_abs (g a)]
    have hd : 0 < η ^ 2 + (a - b) ^ 2 := by positivity
    have h2 : 1 ≤ 2 * (a - b) ^ 2 / (η ^ 2 + (a - b) ^ 2) := by
      rw [le_div_iff₀ hd]; nlinarith
    calc (g a) ^ 2 ≤ M ^ 2 := h1
      _ ≤ M ^ 2 * (2 * (a - b) ^ 2 / (η ^ 2 + (a - b) ^ 2)) := by
          nlinarith [sq_nonneg M]
      _ = M ^ 2 * (2 / (η ^ 2 + (a - b) ^ 2)) * (a - b) ^ 2 := by ring
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (dq g p) ≤
      ENNReal.ofReal ((c ^ 2)⁻¹) * W p + ENNReal.ofReal (M ^ 2) * (F1 p + F2 p) := by
    intro p
    by_cases hA : p.1 ∈ T ∧ p.2 ∈ T
    · have h1 : c ≤ ρ p.1 := hc _ hA.1
      have h2 : c ≤ ρ p.2 := hc _ hA.2
      have hprod : c ^ 2 ≤ ρ p.1 * ρ p.2 := by nlinarith
      have : dq g p ≤ (c ^ 2)⁻¹ * (ρ p.1 * ρ p.2 * dq g p) := by
        have hd := dq_nonneg g p
        rw [← mul_assoc]
        have : 1 ≤ (c ^ 2)⁻¹ * (ρ p.1 * ρ p.2) := by
          rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]; linarith
        nlinarith
      calc ENNReal.ofReal (dq g p) ≤ ENNReal.ofReal ((c ^ 2)⁻¹ * (ρ p.1 * ρ p.2 * dq g p)) :=
            ENNReal.ofReal_le_ofReal this
        _ = ENNReal.ofReal ((c ^ 2)⁻¹) * W p := ENNReal.ofReal_mul (by positivity)
        _ ≤ _ := le_self_add
    · by_cases h1 : p.1 ∈ S
      · have h2 : p.2 ∉ T := fun h2 => hA ⟨hST h1, h2⟩
        have := hkern p.1 p.2 h1 h2
        have e : F1 p = ENNReal.ofReal (Kc η (p.1 - p.2)) := by simp [hF1, h1]
        calc ENNReal.ofReal (dq g p) ≤ ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Kc η (p.1 - p.2)) := this
          _ = ENNReal.ofReal (M ^ 2) * F1 p := by rw [e]
          _ ≤ ENNReal.ofReal (M ^ 2) * (F1 p + F2 p) := by gcongr; exact le_self_add
          _ ≤ _ := le_add_self
      · by_cases h2 : p.2 ∈ S
        · have h1' : p.1 ∉ T := fun h => hA ⟨h, hST h2⟩
          have := hkern p.2 p.1 h2 h1'
          have e : F2 p = ENNReal.ofReal (Kc η (p.1 - p.2)) := by simp [hF2, h2]
          have hsw : dq g (p.2, p.1) = dq g p := by
            unfold dq; simp only []; rw [← neg_sub p.1 p.2, neg_sq]
            rw [← neg_sub (g p.1) (g p.2), neg_sq]
          have hk : Kc η (p.2 - p.1) = Kc η (p.1 - p.2) := by rw [← neg_sub p.1 p.2, Kc_neg]
          rw [hsw, hk] at this
          calc ENNReal.ofReal (dq g p) ≤ ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Kc η (p.1 - p.2)) := this
            _ = ENNReal.ofReal (M ^ 2) * F2 p := by rw [e]
            _ ≤ ENNReal.ofReal (M ^ 2) * (F1 p + F2 p) := by gcongr; exact le_add_self
            _ ≤ _ := le_add_self
        · have : dq g p = 0 := by simp [dq, hg0 _ h1, hg0 _ h2]
          rw [this]; simp
  have hF1int : ∫⁻ p, F1 p ∂(volume.prod volume) = ENNReal.ofReal (2 * Real.pi / η) * volume S := by
    rw [lintegral_prod _ hF1m.aemeasurable]
    have : ∀ x : ℝ, ∫⁻ y, F1 (x, y) = S.indicator (fun _ => ENNReal.ofReal (2 * Real.pi / η)) x := by
      intro x
      by_cases hx : x ∈ S
      · simp only [hF1, hx, Set.indicator_of_mem, one_mul]
        exact lintegral_Kc_shift hη x
      · simp [hF1, hx]
    simp_rw [this]
    exact lintegral_indicator_const hSm _
  have hF2int : ∫⁻ p, F2 p ∂(volume.prod volume) = ∫⁻ p, F1 p ∂(volume.prod volume) := by
    have := lintegral_prod_swap (μ := volume) (ν := volume) F1
    rw [← this]
    refine lintegral_congr fun p => ?_
    simp only [hF1, hF2, Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub, Kc_neg]
  have hWint : ∫⁻ p, W p ∂(volume.prod volume) = formE (muRho ρ) g := (formE_eq_unweighted H hg).symm
  have hfinS : volume S ≠ ⊤ := hS.measure_lt_top.ne
  unfold Eu
  calc ∫⁻ p, ENNReal.ofReal (dq g p) ∂(volume.prod volume)
      ≤ ∫⁻ p, (ENNReal.ofReal ((c ^ 2)⁻¹) * W p + ENNReal.ofReal (M ^ 2) * (F1 p + F2 p)) ∂(volume.prod volume) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((c ^ 2)⁻¹) * formE (muRho ρ) g +
        ENNReal.ofReal (M ^ 2) * (∫⁻ p, F1 p ∂(volume.prod volume) + ∫⁻ p, F2 p ∂(volume.prod volume)) := by
        rw [lintegral_add_left (hWm.const_mul _), lintegral_const_mul _ hWm,
          lintegral_const_mul _ (show Measurable fun p => F1 p + F2 p from hF1m.add hF2m),
          lintegral_add_left hF1m, hWint]
    _ < ⊤ := by
        rw [hF2int, hF1int]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_of_le_of_lt (formE_le_formN _ _) hN), ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
        exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.measure_lt_top,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.measure_lt_top⟩

/-- **The mollification step** holds under `CoreHyp`. -/
theorem mollifyCore (H : CoreHyp ρ) : MollifyCore ρ := by
  intro g hg ⟨M, hM⟩ S hS hSP hg0 hN
  obtain ⟨B, hB⟩ := H.bdd
  have hU := Eu_lt_top H hg hM hS hSP hg0 hN
  have h1 := l2_mollify_tendsto hg hM hS hg0
  have h2 := mollify_energy hg hM hS hg0 hU
  have hr : ∀ n : ℕ, Measurable fun x => g x - mol n g x := fun n =>
    hg.sub (contDiff_mol n hg hM).continuous.measurable
  have hb : Tendsto (fun n : ℕ => ENNReal.ofReal B * L2u (fun x => g x - mol n g x) +
      ENNReal.ofReal B * (ENNReal.ofReal B * Eu (fun x => g x - mol n g x))) atTop (𝓝 0) := by
    have a1 : Tendsto (fun n : ℕ => ENNReal.ofReal B * L2u (fun x => g x - mol n g x)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
    have a2 : Tendsto (fun n : ℕ => ENNReal.ofReal B * (ENNReal.ofReal B * Eu (fun x => g x - mol n g x)))
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal B)
      have := ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal B)
      simpa using this
    simpa using a1.add a2
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal B * L2u (fun x => g x - mol n g x) +
      ENNReal.ofReal B * (ENNReal.ofReal B * Eu (fun x => g x - mol n g x)) < ENNReal.ofReal ε :=
    hb.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨mol n g, contDiff_mol n hg hM, hasCompactSupport_mol n (HasCompactSupport.intro hS hg0), ?_⟩
  exact lt_of_le_of_lt (formN_le_unweighted H hB (hr n)) hn

/-- **The density theorem for `μ = ρ dx`** (`CC:F03:core`, first assertion): unconditional version of `core_density`. -/
theorem core_density' (H : CoreHyp ρ) {h : ℝ → ℝ} (hh : Measurable h) (hN : formN (muRho ρ) h < ⊤) :
    Approx (muRho ρ) h :=
  core_density H (mollifyCore H) hh hN

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.core_density'
