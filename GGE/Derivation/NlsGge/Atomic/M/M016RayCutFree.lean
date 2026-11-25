import Mathlib
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.StdRootBranchesDefs

/- M016 RAYCUTFREE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016RayCutFree.lean. GK38 only. Locally uniform cut-freeness of the imaginary ray: near every
   ψ₀ ∈ gkW there is one neighbourhood V ⊆ gkW and one height B such that `I*t` avoids all gap segments of every
   ψ ∈ V for t > B. Proof: the common isolating family on V has real centres and radii `π/4` for |n| > N. -/

set_option autoImplicit false
open Set Filter Topology Metric

namespace NlsGge.ThirdConsultation.M016ChartAux

open NlsGge.GK38

theorem ray_cutFree_uniform (ψ₀ : PotPair) (h₀ : ψ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 ψ₀ ∧ V ⊆ gkW ∧ ∃ B : ℝ, ∀ ψ ∈ V, ∀ t : ℝ, B < t →
      Complex.I * (t : ℂ) ∉ gapSegments38 ψ := by
  obtain ⟨V, hV, hVW, _, _, C, R, c, N, hgeom, hspec⟩ := local_isolatingFamily_common38 ψ₀ h₀
  refine ⟨V, hV, hVW, Real.pi / 4 + ∑ m ∈ Finset.Icc (-(N : ℤ)) N, R m,
    fun ψ hψ t ht hmem => ?_⟩
  obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
  have hball := ((hspec ψ hψ).1 n).1 hn
  have hsum0 : 0 ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) N, R m :=
    Finset.sum_nonneg fun m _ => (hgeom.1 m).1.le
  have hRn : R n ≤ Real.pi / 4 + ∑ m ∈ Finset.Icc (-(N : ℤ)) N, R m := by
    by_cases hN : (N : ℤ) < |n|
    · rw [((hgeom.2.2.2.2) n hN).2.1]
      linarith
    · push_neg at hN
      have hmemI : n ∈ Finset.Icc (-(N : ℤ)) N := by
        rw [Finset.mem_Icc]
        exact abs_le.1 hN
      have := Finset.single_le_sum (fun m _ => (hgeom.1 m).1.le) hmemI
      linarith [Real.pi_pos]
  have him : (C n).im = 0 := (hgeom.1 n).2
  have hIm : (Complex.I * (t : ℂ) - C n).im = t := by simp [him]
  have hle : t ≤ ‖Complex.I * (t : ℂ) - C n‖ := by
    have := Complex.abs_im_le_norm (Complex.I * (t : ℂ) - C n)
    rw [hIm] at this
    linarith [le_abs_self t]
  rw [mem_ball, dist_eq_norm] at hball
  linarith

end NlsGge.ThirdConsultation.M016ChartAux
