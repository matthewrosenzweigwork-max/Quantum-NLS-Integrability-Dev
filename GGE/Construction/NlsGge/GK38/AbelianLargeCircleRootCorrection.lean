import NlsGge.GK38.AbelianLargeCircleSeparation
import NlsGge.GK38.XiSqRootCorrection

/-! Full principal-square-root corrections on the actual midpoint circles.
Genuine absolute summability is earned before forming any product estimate. -/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6LargeCircle_root_correction_term38 (g w : ℂ) (d : ℝ)
    (hd : 1/2 ≤ d) (hsep : (Real.pi/2)*d ≤ ‖w‖) :
    ‖Complex.sqrt (1-(g/4)/w^2)-1‖ ≤
      (2/Real.pi^2)*(‖g‖/d) := by
  have hdpos : 0 < d := by linarith
  have hw : 0 < ‖w‖ := (mul_pos (half_pos Real.pi_pos) hdpos).trans_le hsep
  have hden : Real.pi^2*d^2 ≤ 4*‖w‖^2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (Real.pi/2)*d) hsep 2
    nlinarith
  have hinv : 1/d ≤ 2 := (div_le_iff₀ hdpos).2 (by linarith)
  calc
    _ ≤ ‖g‖/(4*‖w‖^2) := a5QNormDifference_le38 g w
    _ ≤ ‖g‖/(Real.pi^2*d^2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = (1/Real.pi^2)*(‖g‖/d)*(1/d) := by ring
    _ ≤ (1/Real.pi^2)*(‖g‖/d)*2 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

theorem p6LargeCircle_root_correction_errors38 (σ g : ℤ → ℂ)
    (hσ : Summable (fun m : ℤ => ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖^2))
    (hg : Summable (fun m : ℤ => ‖g m‖^2)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 →
      Summable (fun m : ℤ => ‖Complex.sqrt (1-(g m/4)/(σ m-z)^2)-1‖) ∧
      (∑' m : ℤ, ‖Complex.sqrt (1-(g m/4)/(σ m-z)^2)-1‖) ≤ ε := by
  intro ε hε
  obtain ⟨Nσ,hNσ⟩ := p6LargeCircle_eventual_separation38 σ hσ
  have hgg : Summable (fun m : ℤ =>
      ‖((m : ℂ)*(Real.pi : ℂ)+g m)-(m : ℂ)*(Real.pi : ℂ)‖^2) := by
    simpa only [add_sub_cancel_left] using hg
  obtain ⟨Ng,hNg⟩ := Lib.circle_sum_bound hgg
    (mul_pos hε (by positivity : 0 < Real.pi^2/2))
  refine ⟨max Nσ Ng,fun ν hν z hz => ?_⟩
  have hsum : ∀ s : Finset ℤ,
      ∑ m ∈ s, ‖g m‖/Lib.circDist ν m ≤ ε*(Real.pi^2/2) := by
    intro s
    simpa only [Lib.prodDev,add_sub_cancel_left] using hNg ν ((le_max_right _ _).trans hν) s
  have hnonneg : ∀ m : ℤ, 0 ≤ ‖g m‖/Lib.circDist ν m :=
    fun m => div_nonneg (norm_nonneg _) (Lib.circDist_pos ν m).le
  have hs := summable_of_sum_le hnonneg hsum
  have hb := Real.tsum_le_of_sum_le hnonneg hsum
  have hdom := hs.mul_left (2/Real.pi^2)
  have hterm (m : ℤ) : ‖Complex.sqrt (1-(g m/4)/(σ m-z)^2)-1‖ ≤
      (2/Real.pi^2)*(‖g m‖/Lib.circDist ν m) :=
    p6LargeCircle_root_correction_term38 (g m) (σ m-z) (Lib.circDist ν m)
      (Lib.half_le_circDist ν m) (hNσ ν ((le_max_left _ _).trans hν) z hz m)
  have herr := hdom.of_nonneg_of_le (fun m => norm_nonneg _) hterm
  refine ⟨herr,(herr.tsum_le_tsum hterm hdom).trans ?_⟩
  rw [tsum_mul_left]
  calc
    (2/Real.pi^2)*(∑' m : ℤ, ‖g m‖/Lib.circDist ν m) ≤
        (2/Real.pi^2)*(ε*(Real.pi^2/2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ε := by field_simp

end
end NlsGge.GK38
