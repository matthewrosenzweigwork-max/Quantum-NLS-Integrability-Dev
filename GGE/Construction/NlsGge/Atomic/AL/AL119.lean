import Mathlib
import NlsGge.Atomic.AL.AL115
import NlsGge.Atomic.AL.AL117
import NlsGge.Atomic.AL.AL118
import NlsGge.Hierarchy.ALTiltMeasure38

                                                                                                     
                                                                                                
                                                                            
                                                                                                           
                                                                                                             
                      
set_option autoImplicit false
open scoped Nat
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core
open NlsGge.Pilot NlsGge.Weights
open Set Filter Topology MeasureTheory
namespace NlsGge.ThirdConsultation.AL

theorem al119 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta : delta ≤ lower / 64)
    (A B : ℝ) (hA : 0 < A)
    (hpart : ∀ᶠ N : ℕ in atTop,
      A ≤ alZ38 (L := 2 * N + 1) c.val (alMeshStep38 N) ∧
      alZ38 (L := 2 * N + 1) (alTiltCoeff38 c.val delta) (alMeshStep38 N) ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun alpha : ZMod (2 * N + 1) → ℂ =>
        Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft alpha)‖ ^ 2))
        (alEta38 (2 * N + 1) c.val (alMeshStep38 N)) ∧
      (∫ alpha, Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft alpha)‖ ^ 2)
        ∂alEta38 (2 * N + 1) c.val (alMeshStep38 N)) ≤ C := by
  have hlo : 0 < lower := c.property.1
  obtain ⟨-, -, -, hDpos, -, hlim⟩ := al115 lower upper c delta hdelta0.le hdelta
  set Dd := alTiltLimit38 c.val delta with hDd
  have hev : ∀ᶠ N : ℕ in atTop, Dd / 2 < alTiltD38 c.val (alMeshStep38 N) delta N :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 hpart
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt ((3 * lower / 4)⁻¹)
  refine ⟨|2 / Dd * (B / A)| + 1, by positivity, ?_⟩
  rw [eventually_atTop]
  refine ⟨max (max N₂ N₄) (max N₃ 2), fun N hN => ?_⟩
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN22 : 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNL : (3 * lower / 4)⁻¹ < ((2 * N + 1 : ℕ) : ℝ) := by
    refine lt_of_lt_of_le hN₃ ?_
    have : (N₃ : ℝ) ≤ N := by exact_mod_cast hN3
    push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hh0 : 0 < alMeshStep38 N := by unfold alMeshStep38; positivity
  obtain ⟨hD, hZ, hZt, hint, hEq⟩ := al117 lower upper c delta hdelta0.le hdelta N hNL
  have hDlow := hN₂ N hN2
  have hP := hN₄ N hN4
  -- eta lives on the disk
  have hnull : alEta38 (2 * N + 1) c.val (alMeshStep38 N) (alDisk38 (2 * N + 1))ᶜ = 0 := by
    unfold alEta38
    rw [Measure.smul_apply, alWeighted_eq_withDensity38 c.property hh0,
      withDensity_apply _ (measurableSet_alDisk38).compl]
    have : ∫⁻ α in (alDisk38 (2 * N + 1))ᶜ, ENNReal.ofReal
        (alIntegrand38 (L := 2 * N + 1) c.val (alMeshStep38 N) α) = 0 := by
      rw [setLIntegral_congr_fun (measurableSet_alDisk38).compl (g := fun _ => 0)]
      · simp
      · intro α hα
        have : ¬ IsALField38 α := hα
        simp [alIntegrand38, this]
    rw [this]; simp
  have hae : ∀ᵐ α ∂(alEta38 (2 * N + 1) c.val (alMeshStep38 N)),
      α ∈ alDisk38 (2 * N + 1) := by
    have := (measure_eq_zero_iff_ae_notMem
      (μ := alEta38 (2 * N + 1) c.val (alMeshStep38 N))
      (s := (alDisk38 (2 * N + 1))ᶜ)).1 hnull
    filter_upwards [this] with α hα
    simpa using hα
  have hle : ∀ᵐ α ∂(alEta38 (2 * N + 1) c.val (alMeshStep38 N)),
      Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft α)‖ ^ 2) ≤
        Real.exp (delta * alTiltG38 (alMeshStep38 N) α) := by
    filter_upwards [hae] with α hα
    obtain ⟨h1, -, h3, h4⟩ := al118 N hN22 α hα
    apply Real.exp_le_exp.2
    rw [← h1]
    nlinarith
  have hmeasEq : ∀ᵐ α ∂(alEta38 (2 * N + 1) c.val (alMeshStep38 N)),
      Real.exp (delta * (1 / 2 * alH2Sq38 α)) =
        Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft α)‖ ^ 2) := by
    filter_upwards [hae] with α hα
    obtain ⟨h1, -, -, -⟩ := al118 N hN22 α hα
    rw [← h1]; congr 1; ring
  have hmeas : Measurable fun α : ZMod (2 * N + 1) → ℂ =>
      Real.exp (delta * (1 / 2 * alH2Sq38 α)) :=
    (measurable_const.mul (measurable_const.mul measurable_alH2Sq38)).exp
  have hasm : AEStronglyMeasurable (fun α : ZMod (2 * N + 1) → ℂ =>
      Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft α)‖ ^ 2))
      (alEta38 (2 * N + 1) c.val (alMeshStep38 N)) :=
    hmeas.aestronglyMeasurable.congr hmeasEq
  have hint2 : Integrable (fun α : ZMod (2 * N + 1) → ℂ =>
      Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft α)‖ ^ 2))
      (alEta38 (2 * N + 1) c.val (alMeshStep38 N)) :=
    hint.mono' hasm (by
      filter_upwards [hle] with α hα
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hα)
  refine ⟨hint2, ?_⟩
  have hB0 : 0 ≤ B := le_trans hZt.le hP.2
  calc ∫ α, Real.exp ((delta / 2) * ‖alQ4Interp38 2 N (ZMod.dft α)‖ ^ 2)
          ∂alEta38 (2 * N + 1) c.val (alMeshStep38 N)
      ≤ ∫ α, Real.exp (delta * alTiltG38 (alMeshStep38 N) α)
          ∂alEta38 (2 * N + 1) c.val (alMeshStep38 N) :=
        integral_mono_ae hint2 hint hle
    _ = (alTiltD38 c.val (alMeshStep38 N) delta N)⁻¹ *
        (alZ38 (L := 2 * N + 1) (alTiltCoeff38 c.val delta) (alMeshStep38 N) /
          alZ38 (L := 2 * N + 1) c.val (alMeshStep38 N)) := hEq
    _ ≤ 2 / Dd * (B / A) := by
        have hr : 0 ≤ alZ38 (L := 2 * N + 1) (alTiltCoeff38 c.val delta) (alMeshStep38 N) /
            alZ38 (L := 2 * N + 1) c.val (alMeshStep38 N) := (div_pos hZt hZ).le
        have hDi : (alTiltD38 c.val (alMeshStep38 N) delta N)⁻¹ ≤ 2 / Dd := by
          rw [inv_eq_one_div, div_le_div_iff₀ hD hDpos]; linarith
        have hq : alZ38 (L := 2 * N + 1) (alTiltCoeff38 c.val delta) (alMeshStep38 N) /
            alZ38 (L := 2 * N + 1) c.val (alMeshStep38 N) ≤ B / A :=
          div_le_div₀ hB0 hP.2 hA hP.1
        exact mul_le_mul hDi hq hr (by positivity)
    _ ≤ |2 / Dd * (B / A)| + 1 := by linarith [le_abs_self (2 / Dd * (B / A))]

end NlsGge.ThirdConsultation.AL
