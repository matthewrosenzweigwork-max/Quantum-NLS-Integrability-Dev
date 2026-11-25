                                                                                                                  
                                                                                                                          
                                                                              
import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Atomic.AL.AL057
import NlsGge.Atomic.AL.AL059
import NlsGge.Atomic.AL.AL061

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik
open Set
namespace NlsGge.ThirdConsultation.AL


def sampleModulus (u : SobolevHilbert 1) (r : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x y : ℝ, |x - y| ≤ r ∧
    v = ‖alCanon38 u x - alCanon38 u y‖}

namespace al058Aux

theorem alh38_tendsto : Tendsto (fun N : ℕ => alh38 N) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => (alh38_pos N).le) (fun N => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold alh38
  exact one_div_le_one_div_of_le (by positivity)
    (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

theorem sample_eq (y : SobolevHilbert 1) (N : ℕ) (shift : ℤ) (hshift : |shift| ≤ 1) (t : ℝ) :
    ∃ s : ℝ, |s - t| ≤ 2 * alh38 N ∧ sampleStep N shift y t = alCanon38 y s := by
  have hh := alh38_pos N
  have hfl1 := Int.floor_le (t / alh38 N)
  have hfl2 := Int.lt_floor_add_one (t / alh38 N)
  have hsh : |(shift : ℝ)| ≤ 1 := by exact_mod_cast hshift
  refine ⟨((Int.floor (t / alh38 N) + shift : ℤ) : ℝ) * alh38 N, ?_, ?_⟩
  · have h1 : (Int.floor (t / alh38 N) : ℝ) * alh38 N ≤ t := by
      have := mul_le_mul_of_nonneg_right hfl1 hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    have h2 : t < (Int.floor (t / alh38 N) : ℝ) * alh38 N + alh38 N := by
      have := mul_lt_mul_of_pos_right hfl2 hh
      rwa [div_mul_cancel₀ _ hh.ne', add_mul, one_mul] at this
    have hk : |(Int.floor (t / alh38 N) : ℝ) * alh38 N - t| ≤ alh38 N := by
      rw [abs_le]; constructor <;> linarith
    have hs : |(shift : ℝ) * alh38 N| ≤ alh38 N := by
      rw [abs_mul, abs_of_pos hh]; exact mul_le_of_le_one_left hh.le hsh
    have e : ((Int.floor (t / alh38 N) + shift : ℤ) : ℝ) * alh38 N - t =
        ((Int.floor (t / alh38 N) : ℝ) * alh38 N - t) + (shift : ℝ) * alh38 N := by
      push_cast; ring
    rw [e]
    calc |((Int.floor (t / alh38 N) : ℝ) * alh38 N - t) + (shift : ℝ) * alh38 N|
        ≤ |(Int.floor (t / alh38 N) : ℝ) * alh38 N - t| + |(shift : ℝ) * alh38 N| :=
          abs_add_le _ _
      _ ≤ alh38 N + alh38 N := add_le_add hk hs
      _ = 2 * alh38 N := by ring
  · calc sampleStep N shift y t
        = alCanon38 y (alt38 N (((Int.floor (t / alh38 N) + shift : ℤ)) : ZMod (2 * N + 1))) := by
          unfold sampleStep stepArray alSample38
          rw [Int.cast_add]
      _ = alCanon38 y (((Int.floor (t / alh38 N) + shift : ℤ) : ℝ) * alh38 N) :=
          AL061Aux.canon_cell0 y N _

theorem modulus_le (u : SobolevHilbert 1) {r s t : ℝ} (hst : |s - t| ≤ r) :
    ‖alCanon38 u s - alCanon38 u t‖ ≤ sampleModulus u r := by
  unfold sampleModulus
  apply le_csSup
  · refine ⟨2 * (‖u‖ * ‖reciprocalBracketL2‖), ?_⟩
    rintro v ⟨x, y, _, rfl⟩
    calc ‖alCanon38 u x - alCanon38 u y‖ ≤ ‖alCanon38 u x‖ + ‖alCanon38 u y‖ := norm_sub_le _ _
      _ ≤ ‖u‖ * ‖reciprocalBracketL2‖ + ‖u‖ * ‖reciprocalBracketL2‖ :=
          add_le_add (alCanon_norm_le38 u x) (alCanon_norm_le38 u y)
      _ = 2 * (‖u‖ * ‖reciprocalBracketL2‖) := by ring
  · exact ⟨s, t, hst, rfl⟩

theorem modulus_nonneg (u : SobolevHilbert 1) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ sampleModulus u r := by
  have h := modulus_le u (r := r) (s := 0) (t := 0) (by simpa using hr)
  rwa [sub_self, norm_zero] at h

theorem dist_circle_le (x y : ℝ) : dist (x : PhysicalCircle) (y : PhysicalCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, ← Real.norm_eq_abs]
  exact QuotientAddGroup.norm_mk_le_norm

theorem modulus_small (u : SobolevHilbert 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ δ → sampleModulus u r ≤ ε := by
  have hF : UniformContinuous (physicalH1CanonicalContinuousRepresentativeCLM u) :=
    CompactSpace.uniformContinuous_of_continuous
      (physicalH1CanonicalContinuousRepresentativeCLM u).continuous
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuous_iff.1 hF (ε / 2) (by linarith)
  refine ⟨δ / 2, by linarith, fun r hr0 hrδ => ?_⟩
  have key : sampleModulus u r ≤ ε / 2 := by
    unfold sampleModulus
    apply csSup_le
    · exact ⟨‖alCanon38 u 0 - alCanon38 u 0‖, 0, 0, by simp [hr0], rfl⟩
    · rintro v ⟨x, y, hxy, rfl⟩
      have hd : dist (x : PhysicalCircle) (y : PhysicalCircle) < δ :=
        lt_of_le_of_lt (dist_circle_le x y) (by linarith)
      have h3 := hδF hd
      rw [dist_eq_norm] at h3
      exact le_of_lt h3
  linarith

theorem modulus_tendsto (u : SobolevHilbert 1) :
    Tendsto (fun N : ℕ => sampleModulus u (2 * alh38 N)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδM⟩ := modulus_small u (half_pos hε)
  have h2 : Tendsto (fun N : ℕ => 2 * alh38 N) atTop (𝓝 0) := by
    simpa using alh38_tendsto.const_mul 2
  filter_upwards [(tendsto_order.1 h2).2 δ hδ] with N hN
  have hr0 : 0 ≤ 2 * alh38 N := by linarith [alh38_pos N]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_nonneg u hr0)]
  linarith [hδM _ hr0 hN.le]

theorem step_bound (y u : SobolevHilbert 1) (N : ℕ) (shift : ℤ) (hshift : |shift| ≤ 1) (t : ℝ) :
    ‖sampleStep N shift y t - alCanon38 u t‖ ≤
      ‖physicalH1CanonicalContinuousRepresentativeCLM (y - u)‖ + sampleModulus u (2 * alh38 N) := by
  obtain ⟨s, hs, heq⟩ := sample_eq y N shift hshift t
  rw [heq]
  have hA : ‖alCanon38 y s - alCanon38 u s‖ ≤
      ‖physicalH1CanonicalContinuousRepresentativeCLM (y - u)‖ := by
    rw [← alCanon_sub38]
    unfold alCanon38
    exact ContinuousMap.norm_coe_le_norm _ _
  have hB := modulus_le u hs
  calc ‖alCanon38 y s - alCanon38 u t‖
      = ‖(alCanon38 y s - alCanon38 u s) + (alCanon38 u s - alCanon38 u t)‖ := by
        congr 1; abel
    _ ≤ ‖alCanon38 y s - alCanon38 u s‖ + ‖alCanon38 u s - alCanon38 u t‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hA hB

end al058Aux

theorem al058 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    (∀ N : ℕ, ∀ shift : ℤ, |shift| ≤ 1 → ∀ t : ℝ,
      ‖sampleStep N shift (x N) t - alCanon38 u t‖ ≤
        ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ +
        sampleModulus u (2 * alh38 N)) ∧
    Tendsto (fun N => sampleModulus u (2 * alh38 N)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ shift : ℤ, |shift| ≤ 1 → ∀ t : ℝ,
        ‖sampleStep N shift (x N) t - alCanon38 u t‖ < ε) := by
  have h2 := al058Aux.modulus_tendsto u
  refine ⟨fun N shift hshift t => al058Aux.step_bound (x N) u N shift hshift t, h2, ?_⟩
  intro ε hε
  have h1 := (al057 x u hx).1
  have hsum := h1.add h2
  rw [add_zero] at hsum
  filter_upwards [(tendsto_order.1 hsum).2 ε hε] with N hN shift hshift t
  exact lt_of_le_of_lt (al058Aux.step_bound (x N) u N shift hshift t) hN

end NlsGge.ThirdConsultation.AL
