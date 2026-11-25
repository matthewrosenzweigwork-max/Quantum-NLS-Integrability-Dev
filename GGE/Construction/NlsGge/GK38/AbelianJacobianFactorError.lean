import NlsGge.GK38.AbelianJacobianQuotients
import NlsGge.GK38.AbelianJacobianInputEnvelope
import NlsGge.GK38.AbelianRatioRowError

/-! Actual complex diagonal factor error, uniformly over every signed excited index.
UNCOMPILED source preparation. The row envelopes depend on the actual current input. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem cut_lattice_displacement (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (m : ℤ) (z : ℂ)
    (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖z-(m : ℂ)*(Real.pi : ℂ)‖ ≤ p2RowEnvelope38 φ s m := by
  have hc := p2Actual_cut_midpoint_norm_le38 φ hφ m z hz
  have he : z-(m : ℂ)*(Real.pi : ℂ) =
      (z-tauN φ m)+(tauN φ m-(m : ℂ)*(Real.pi : ℂ)) := by ring
  rw [he]
  calc
    _ ≤ ‖z-tauN φ m‖+‖tauN φ m-(m : ℂ)*(Real.pi : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖lamPlus φ m-lamMinus φ m‖/2+‖tauN φ m-(m : ℂ)*(Real.pi : ℂ)‖ :=
      add_le_add hc le_rfl
    _ ≤ p2RowEnvelope38 φ s m := by
      unfold p2RowEnvelope38
      linarith [norm_nonneg (s m)]

theorem normalized_cut_input_error (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (n m : ℤ) (z : ℂ)
    (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖(z-(m : ℂ)*(Real.pi : ℂ)-s n)/(((n-m : ℤ) : ℂ))‖ ≤
      p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m := by
  have hw : ‖(((n-m : ℤ) : ℂ))‖⁻¹ = Lib.c3w m n := by
    rw [Complex.norm_intCast]
    simp only [Int.cast_sub,Lib.c3w,one_div]
  have hE := p2RowEnvelope_nonneg38 φ s m
  have hc := cut_lattice_displacement φ hφ s m z hz
  rw [norm_div,div_eq_mul_inv,hw]
  calc
    _ ≤ (‖z-(m : ℂ)*(Real.pi : ℂ)‖+‖s n‖)*Lib.c3w m n :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Lib.c3w_nonneg m n)
    _ = ‖z-(m : ℂ)*(Real.pi : ℂ)‖*Lib.c3w m n+‖s n‖*Lib.c3w m n := by ring
    _ ≤ p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_right hc (Lib.c3w_nonneg m n)).trans
          (mul_le_of_le_one_right hE (Lib.c3w_le_one m n))
      · exact p3InputRowEnvelope_point38 s m n

theorem weighted_reciprocal_sub_inv_pi (s : Lib.L2Seq) (n m : ℤ)
    (hnm : n ≠ m) (z : ℂ) (hd : Lib.sigmaOf s n-z ≠ 0) :
    (((n-m : ℤ) : ℂ))/(Lib.sigmaOf s n-z)-1/(Real.pi : ℂ) =
      (1/(Real.pi : ℂ))*((((n-m : ℤ) : ℂ))/(Lib.sigmaOf s n-z))*
        ((z-(m : ℂ)*(Real.pi : ℂ)-s n)/(((n-m : ℤ) : ℂ))) := by
  have hidx : (((n-m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hnm
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hd,hidx,hpi]
  unfold Lib.sigmaOf
  push_cast
  ring

theorem weighted_reciprocal_error (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (n m : ℤ) (hnm : n ≠ m)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) (z : ℂ)
    (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖(((n-m : ℤ) : ℂ))/(Lib.sigmaOf s n-z)-1/(Real.pi : ℂ)‖ ≤
      (c/Real.pi)*(p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m) := by
  have hzball : z ∈ closedBall (C m) (R m) := by
    obtain ⟨d,M,hg,hsp⟩ := hfam
    exact ball_subset_closedBall ((hsp.1 m).1 hz)
  have hd := p2OwnSigma_denominator38 C R c N hgeom n m hnm s hσ z hzball
  have herror := normalized_cut_input_error φ hφ s n m z hz
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hgeom.2.2.1
  have hpiNorm : ‖1/(Real.pi : ℂ)‖ = 1/Real.pi := by
    rw [norm_div,norm_one,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [weighted_reciprocal_sub_inv_pi s n m hnm z hd.1]
  rw [norm_mul,norm_mul,hpiNorm]
  calc
    _ ≤ (1/Real.pi)*c*(p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd.2 (by positivity)) herror
        (norm_nonneg _) (mul_nonneg (by positivity) hc)
    _ = _ := by ring

theorem diagonalFactor_error (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (n m : ℤ) (hnm : n ≠ m)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) (z : ℂ)
    (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m))
    (H b : ℝ) (_hH : 0 ≤ H) (_hb : 0 ≤ b)
    (hbound : ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H)
    (herror : ‖p2OmittedRatio38 m ((φ,s),z)-1‖ ≤ b) :
    ‖p3DiagonalFactor38 n m φ s z-1/(Real.pi : ℂ)‖ ≤
      (c*H/Real.pi)*(p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m)+b/Real.pi := by
  have he : p3DiagonalFactor38 n m φ s z-1/(Real.pi : ℂ) =
      ((((n-m : ℤ) : ℂ))/(Lib.sigmaOf s n-z)-1/(Real.pi : ℂ))*
        p2OmittedRatio38 m ((φ,s),z)+
      (p2OmittedRatio38 m ((φ,s),z)-1)/(Real.pi : ℂ) := by
    unfold p3DiagonalFactor38
    ring
  have hr := weighted_reciprocal_error φ hφ C R c N hgeom hfam s n m hnm hσ z hz
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hgeom.2.2.1
  have hF : 0 ≤ p3InputRowEnvelope38 s m := Real.sqrt_nonneg _
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ ((c/Real.pi)*(p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m))*H+b/Real.pi := by
      exact add_le_add (mul_le_mul hr hbound (norm_nonneg _)
        (mul_nonneg (div_nonneg hc Real.pi_pos.le)
          (add_nonneg (p2RowEnvelope_nonneg38 φ s m) hF)))
        (div_le_div_of_nonneg_right herror Real.pi_pos.le)
    _ = _ := by ring

end
end NlsGge.GK38.P3JacobianColumns
