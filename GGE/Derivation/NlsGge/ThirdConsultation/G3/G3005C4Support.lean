import Mathlib
import NlsGge.Atomic.G2.G2046
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3005UpperHost
import NlsGge.ThirdConsultation.G3.G3005C4Topology
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.PairRealBridge

/- G3-005 SUPPORT C4 (proof development, AUTHOR; not self-reviewed). Target NlsGge/ThirdConsultation/G3/G3005C4Support.lean (proposed).
   Proves conjunct 4 of Pro round 9 sec. 9 G3_005: Nonempty (UpperStartPath m phi), for gap <> 0, as pure geometry plus
   the canonical sheet +-canonRoot38. Route: three straight C1 arcs in the slit isolating disc,
     arc1: lamPlus -> c (c on the line L through the cut, just beyond lamPlus),
     arc2: c -> p, arc3: p -> mu (p off L, on the side of mu; interior points off L hence off the cut),
   with the sheet e * canonRoot38 on all interior points (one global sign e), extended by 0 at the branch end of arc1 and by
   the limit r = antiDiscrim mu at the terminal end of arc3 (G3005C4.sheet_limit; limit sign chosen so that e*limit = r).
   No hypothesis beyond gap <> 0. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3005C4
noncomputable section

def line (x y : ℂ) (t : ℝ) : ℂ := x + (t : ℂ) * (y - x)

theorem line_zero (x y : ℂ) : line x y 0 = x := by simp [line]
theorem line_one (x y : ℂ) : line x y 1 = y := by simp [line]
theorem line_cont (x y : ℂ) : Continuous (line x y) := by unfold line; fun_prop
theorem line_contDiff (x y : ℂ) : ContDiff ℝ 1 (line x y) := by
  unfold line
  exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem line_mem_ball {C : ℂ} {R : ℝ} {x y : ℂ} (hx : x ∈ ball C R) (hy : y ∈ ball C R)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : line x y t ∈ ball C R := by
  have h := (convex_ball C R).add_smul_sub_mem hx hy ht
  rw [Complex.real_smul] at h
  exact h

/-- Height over the line through the cut: imaginary part of `(z - a)/γ`. -/
def hgt (a γ z : ℂ) : ℝ := ((z - a) / γ).im

theorem hgt_line (a γ x y : ℂ) (hγ : γ ≠ 0) (t : ℝ) :
    hgt a γ (line x y t) = (1 - t) * hgt a γ x + t * hgt a γ y := by
  unfold hgt line
  have e : (x + (t:ℂ) * (y - x) - a) / γ = (1 - (t:ℂ)) * ((x - a) / γ) + (t:ℂ) * ((y - a) / γ) := by
    field_simp; ring
  rw [e]
  simp [Complex.add_im, Complex.mul_im]

theorem hgt_add (a γ z d : ℂ) (κ : ℝ) :
    hgt a γ (z + (κ:ℂ) * d) = hgt a γ z + κ * (d / γ).im := by
  unfold hgt
  have e : (z + (κ:ℂ) * d - a) / γ = (z - a) / γ + (κ:ℂ) * (d / γ) := by ring
  rw [e]
  simp [Complex.add_im, Complex.mul_im]

theorem hgt_seg {a b z : ℂ} (h : z ∈ segment ℝ a b) (hγ : b - a ≠ 0) : hgt a (b - a) z = 0 := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := h
  obtain rfl : u = 1 - v := by linarith
  have e : ((1 - v) • a + v • b - a) = (v : ℂ) * (b - a) := by
    simp only [Complex.real_smul]; push_cast; ring
  unfold hgt
  rw [e, mul_div_cancel_right₀ _ hγ]
  simp

theorem notseg_of_hgt {a b z : ℂ} (hγ : b - a ≠ 0) (hne : hgt a (b - a) z ≠ 0) :
    z ∉ segment ℝ a b := fun h => hne (hgt_seg h hγ)

theorem hgt_beyond (a b : ℂ) (hγ : b - a ≠ 0) (s : ℝ) :
    hgt a (b - a) (b + (s:ℂ) * (b - a)) = 0 := by
  unfold hgt
  have e : (b + (s:ℂ) * (b - a) - a) / (b - a) = 1 + (s:ℂ) := by field_simp; ring
  rw [e]; simp

theorem notseg_beyond (a b : ℂ) (hγ : b - a ≠ 0) (s : ℝ) (hs : 0 < s) :
    b + (s:ℂ) * (b - a) ∉ segment ℝ a b := by
  rintro ⟨u, v, hu, hv, huv, h⟩
  obtain rfl : u = 1 - v := by linarith
  have h2 : (((v - 1 - s : ℝ)) : ℂ) * (b - a) = 0 := by
    simp only [Complex.real_smul] at h
    push_cast at h ⊢
    linear_combination h
  have h3 : ((v - 1 - s : ℝ) : ℂ) = 0 := (mul_eq_zero.1 h2).resolve_right hγ
  have h4 : v - 1 - s = 0 := by exact_mod_cast h3
  linarith

theorem exists_small (z0 d : ℂ) (U : Set ℂ) (hU : IsOpen U) (hz : z0 ∈ U) :
    ∃ η : ℝ, 0 < η ∧ z0 + (η : ℂ) * d ∈ U := by
  have hc : Continuous (fun s : ℝ => z0 + (s : ℂ) * d) := by fun_prop
  have hev : ∀ᶠ s : ℝ in 𝓝 (0:ℝ), z0 + (s : ℂ) * d ∈ U :=
    hc.continuousAt.eventually_mem (hU.mem_nhds (by simpa using hz))
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, by positivity, h ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

theorem not_gap (φ : PotPair) (hgk : φ ∈ gkW) (m : ℤ) (z : ℂ)
    (hz : z ∈ ball (discC φ m) (discR φ m))
    (hnot : z ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)) : z ∉ gapSegments38 φ := by
  have hom := a5OwnClosedBall_omittedDomain38 φ hgk (discC φ) (discR φ)
    (isolating_family38 φ hgk) m z (ball_subset_closedBall hz)
  intro hmem
  simp only [gapSegments38, Set.mem_iUnion] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hkm : k = m
  · subst hkm; exact hnot hk
  · exact hom.2 k hkm hk

theorem canon_cont (φ : PotPair) (hgk : φ ∈ gkW) (g : ℝ → ℂ) (hg : Continuous g) (S : Set ℝ)
    (h : ∀ t ∈ S, g t ∉ gapSegments38 φ) :
    ContinuousOn (fun t => canonRoot38 φ (g t)) S := by
  intro t ht
  have hA : AnalyticAt ℂ (canonRoot38 φ) (g t) :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun w : ℂ => (φ, w)) (canonRoot_analytic38 _ ⟨hgk, h t ht⟩)
      (analyticAt_const.prod analyticAt_id)
  exact (hA.continuousAt.comp hg.continuousAt).continuousWithinAt

theorem perChar_cont (φ : PotPair) : Continuous (perChar φ) :=
  continuousOn_univ.mp (analyticOnNhd_perChar_z φ).continuousOn

end
end G3005C4
end NlsGge.GKDefinitionDesign
