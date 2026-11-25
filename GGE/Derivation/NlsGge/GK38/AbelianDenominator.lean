import NlsGge.GK38.AbelianParameterBounds
import NlsGge.GK38.IsolatingGeometry

/-! Prospective actual denominator bounds. Closed original discs are used for
analyticity; no new isolating family or arbitrary sigma placement is assumed. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- Quantitative separation extends to the two original CLOSED discs. -/
theorem p2ClosedDiscs_separation38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (n m : ℤ) (hnm : n ≠ m)
    (v z : ℂ) (hv : v ∈ closedBall (C n) (R n))
    (hz : z ∈ closedBall (C m) (R m)) :
    c⁻¹*|((n-m:ℤ):ℝ)| ≤ ‖v-z‖ := by
  have hsep := isolating_geometry_closure_separated38 C R c N hg n m hnm
  have hlow := (hg.2.2.2.1 n m hnm).1
  rw [ballDistance38_eq _ _ (hg.1 n).1 (hg.1 m).1,
    max_eq_right (by linarith)] at hlow
  have htri := dist_triangle4 (C n) v z (C m)
  have hv' : dist (C n) v ≤ R n := by simpa only [dist_comm] using mem_closedBall.mp hv
  have hz' := mem_closedBall.mp hz
  rw [dist_eq_norm v z] at htri
  linarith

/-- Sigma_n in its own original disc earns BOTH denominator nonzero on the WHOLE
other filled disc and the precise weighted reciprocal bound. -/
theorem p2OwnSigma_denominator38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (n m : ℤ) (hnm : n ≠ m)
    (s : Lib.L2Seq) (hs : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    Lib.sigmaOf s n-z ≠ 0 ∧ ‖(((n-m:ℤ):ℂ))/(Lib.sigmaOf s n-z)‖ ≤ c := by
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hg.2.2.1
  have hd : 0 < |((n-m:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hnm)
  have hbound := p2ClosedDiscs_separation38 C R c N hg n m hnm (Lib.sigmaOf s n) z hs hz
  have hnorm : 0 < ‖Lib.sigmaOf s n-z‖ :=
    (mul_pos (inv_pos.mpr hc) hd).trans_le hbound
  refine ⟨norm_pos_iff.mp hnorm,?_⟩
  rw [norm_div,Complex.norm_intCast,div_le_iff₀ hnorm]
  have hh := mul_le_mul_of_nonneg_left hbound hc.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] using hh

/-- Actual input Hilbert tails place ALL sufficiently large sigma_n in the same
original full family's tail discs, uniformly on ONE input neighbourhood. -/
theorem p2Input_tail_own_disc38 (s₀ : Lib.L2Seq)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (Ng : ℕ)
    (hg : IsolatingGeometry38 C R c Ng) :
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ N : ℕ,
      ∀ s ∈ V, ∀ n : ℤ, (N:ℤ) < |n| → Lib.sigmaOf s n ∈ ball (C n) (R n) := by
  obtain ⟨V,hV,Ns,hs⟩ := p2Input_uniform_tail38 s₀ (Real.pi/4) (by positivity)
  refine ⟨V,hV,max Ng Ns,?_⟩
  intro s hsV n hn
  have hng : (Ng:ℤ) < |n| := by have he := le_max_left Ng Ns; omega
  have hns : (Ns:ℤ) < |n| := by have he := le_max_right Ng Ns; omega
  rw [(hg.2.2.2.2 n hng).1,(hg.2.2.2.2 n hng).2.1,mem_ball_iff_norm]
  simpa only [Lib.sigmaOf,countingCenter38,add_sub_cancel_left] using hs s hsV n hns

/-- Pure lattice geometry for the finite exceptional input labels. The threshold
is earned later from a common actual input-norm bound; no final bound is assumed. -/
theorem p2Far_disc_denominator38 (s : Lib.L2Seq) (n m : ℤ) (A : ℝ)
    (hA : ‖s n‖ ≤ A)
    (hfar : 2*(A+Real.pi/4) ≤ Real.pi*|((n-m:ℤ):ℝ)|)
    (hnm : n ≠ m) (z : ℂ)
    (hz : z ∈ closedBall ((m:ℂ)*(Real.pi:ℂ)) (Real.pi/4)) :
    Lib.sigmaOf s n-z ≠ 0 ∧
      ‖(((n-m:ℤ):ℂ))/(Lib.sigmaOf s n-z)‖ ≤ 2/Real.pi := by
  have hdist : ‖((n:ℂ)*(Real.pi:ℂ))-((m:ℂ)*(Real.pi:ℂ))‖ =
      Real.pi*|((n-m:ℤ):ℝ)| := by
    rw [← sub_mul,← Int.cast_sub,norm_mul,Complex.norm_intCast,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    ring
  have htri : Real.pi*|((n-m:ℤ):ℝ)| ≤ A+‖Lib.sigmaOf s n-z‖+Real.pi/4 := by
    have he := dist_triangle4 ((n:ℂ)*(Real.pi:ℂ)) (Lib.sigmaOf s n) z ((m:ℂ)*(Real.pi:ℂ))
    rw [dist_eq_norm,hdist] at he
    have hs : dist ((n:ℂ)*(Real.pi:ℂ)) (Lib.sigmaOf s n) ≤ A := by
      rw [dist_comm,dist_eq_norm]
      simpa only [Lib.sigmaOf,add_sub_cancel_left] using hA
    have hz' := mem_closedBall.mp hz
    rw [dist_eq_norm (Lib.sigmaOf s n) z] at he
    linarith
  have hd : 0 < |((n-m:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hnm)
  have hl : (Real.pi/2)*|((n-m:ℤ):ℝ)| ≤ ‖Lib.sigmaOf s n-z‖ := by linarith
  have hnorm : 0 < ‖Lib.sigmaOf s n-z‖ := (mul_pos (by positivity) hd).trans_le hl
  refine ⟨norm_pos_iff.mp hnorm,?_⟩
  rw [norm_div,Complex.norm_intCast,div_le_iff₀ hnorm]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith

#print axioms p2ClosedDiscs_separation38
#print axioms p2OwnSigma_denominator38
#print axioms p2Input_tail_own_disc38
#print axioms p2Far_disc_denominator38
end
end NlsGge.GK38
