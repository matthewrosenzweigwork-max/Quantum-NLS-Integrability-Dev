import NlsGge.GK38.AbelianActualDifferenceDiagonalOperator
import NlsGge.GK38.AbelianFullGapCompactDomain
import NlsGge.GK38.AbelianFixedWeightedMass

/-! UNCOMPILED actual nonmissing OPERATOR-norm convergence, uniformly on the
GENUINE fixed full gap cube and along BOTH signed spectral tails. All product
row square masses are proved summable before their tsums or limits occur. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6FixedWeightedMajorant38 (u : PhysicalL2) (n : ℤ) : ℝ :=
  2*(p5GapEnvelope38 u n)^2*
      (∑' m : ℤ, p6FixedGapRowEnvelope38 u m^2*Lib.c3w m n^2)+
    2*(∑' m : ℤ, (p6FixedGapRowEnvelope38 u m*p2RowEnvelope38 (realSlice u) 0 m)^2*
      Lib.c3w m n^2)

def p6NonmissingNormMajorant38 (u : PhysicalL2) (c H : ℝ) (n : ℤ) : ℝ :=
  (2*c*H)*(p5GapEnvelope38 u n+Real.sqrt
    (∑' m : ℤ, p2RowEnvelope38 (realSlice u) 0 m^2*Lib.c3w m n^2))+
  Real.sqrt ((2*c^2*H)^2*Lib.invSqSum*p6FixedWeightedMajorant38 u n)

theorem p6GapCube_offDiagonal_norm_majorant38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ s ∈ p6ComplexFullGapCube38 u, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
        ‖p2OmittedRatio38 m ((realSlice u,s),z)‖ ≤ H)
    (n : ℤ) (s : Lib.L2Seq) (hs : s ∈ p6ComplexFullGapCube38 u) :
    ‖p6DifferenceOffDiagonalBlock38 n (realSlice u) s‖ ≤
      Real.sqrt ((2*c^2*H)^2*Lib.invSqSum*p6FixedWeightedMajorant38 u n) := by
  have hgap := p6ComplexFullGapCube_actual_gaps38 u s hs
  have hσ := p6ComplexFullGapCube_original_placement38 u C R hfam s hs
  have hb := (p6ActualDifference_offDiagonal_isHS_norm_bound38 (realSlice u)
    (realSlice_mem_gkW u) C R c N hg hfam s hσ H hH (hRatio s hs) n).2
  have hm := p6WeightedMass_common_majorant38 (p2RowEnvelope38 (realSlice u) s)
    (p6FixedGapRowEnvelope38 u) (p2RowEnvelope38 (realSlice u) 0)
    (p2RowEnvelope_nonneg38 (realSlice u) s) (p6FixedGapRowEnvelope_nonneg38 u)
    (p6FullGap_row_envelope38 u s hgap) (p6FixedGapRowEnvelope_summable38 u)
    (p6CutCenter_envelope_summable38 (realSlice u) (realSlice_mem_gkW u))
    ‖s n‖ (p5GapEnvelope38 u n) (norm_nonneg _) (p6FullGap_input_envelope38 u s hgap n) n
  apply hb.trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (sq_nonneg _) Lib.invSqSum_nonneg)

theorem p6GapCube_nonmissing_norm_majorant38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ s ∈ p6ComplexFullGapCube38 u, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
        ‖p2OmittedRatio38 m ((realSlice u,s),z)‖ ≤ H)
    (n : ℤ) (s : Lib.L2Seq) (hs : s ∈ p6ComplexFullGapCube38 u) :
    ‖p6NonmissingDifference38 n (realSlice u) s‖ ≤ p6NonmissingNormMajorant38 u c H n := by
  have hgap := p6ComplexFullGapCube_actual_gaps38 u s hs
  have hσ := p6ComplexFullGapCube_original_placement38 u C R hfam s hs
  have hd := p6ActualDifference_diagonal_operator_norm38 (realSlice u)
    (realSlice_mem_gkW u) C R c N hg hfam s hσ H hH (hRatio s hs) n
  have ho := p6GapCube_offDiagonal_norm_majorant38 u C R c N hg hfam H hH hRatio n s hs
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hA : 0 ≤ 2*c*H := by positivity
  have he : p6NonmissingDifference38 n (realSlice u) s=
      p6ComplexDiagonal38 (p6NonmissingDifference38 n (realSlice u) s)+
        p6DifferenceOffDiagonalBlock38 n (realSlice u) s := by
    unfold p6DifferenceOffDiagonalBlock38
    abel
  calc
    _ = ‖p6ComplexDiagonal38 (p6NonmissingDifference38 n (realSlice u) s)+
        p6DifferenceOffDiagonalBlock38 n (realSlice u) s‖ := congrArg norm he
    _ ≤ ‖p6ComplexDiagonal38 (p6NonmissingDifference38 n (realSlice u) s)‖+
        ‖p6DifferenceOffDiagonalBlock38 n (realSlice u) s‖ := norm_add_le _ _
    _ ≤ (2*c*H)*(‖s n‖+Real.sqrt
        (∑' m : ℤ, p2RowEnvelope38 (realSlice u) 0 m^2*Lib.c3w m n^2))+
        Real.sqrt ((2*c^2*H)^2*Lib.invSqSum*p6FixedWeightedMajorant38 u n) := add_le_add hd ho
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (p6FullGap_input_envelope38 u s hgap n) le_rfl) hA) le_rfl

theorem p6NonmissingNormMajorant_cofinite_zero38 (u : PhysicalL2) (c H : ℝ) :
    Tendsto (p6NonmissingNormMajorant38 u c H) cofinite (𝓝 (0 : ℝ)) := by
  have hgs := p5GapEnvelope_summable38 u
  have hEs := p6FixedGapRowEnvelope_summable38 u
  have hds := p6CutCenter_envelope_summable38 (realSlice u) (realSlice_mem_gkW u)
  have hg0 (n : ℤ) : 0 ≤ p5GapEnvelope38 u n := by unfold p5GapEnvelope38; positivity
  have hg : Tendsto (p5GapEnvelope38 u) cofinite (𝓝 (0 : ℝ)) := by
    have hh := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hgs.tendsto_cofinite_zero
    simpa only [Function.comp_def,Real.sqrt_sq (hg0 _),Real.sqrt_zero] using hh
  have hd := p6ShiftedSquareMass_cofinite_zero38 (p2RowEnvelope38 (realSlice u) 0) hds
  have hdsqrt : Tendsto (fun n : ℤ => Real.sqrt
      (∑' m : ℤ, p2RowEnvelope38 (realSlice u) 0 m^2*Lib.c3w m n^2))
      cofinite (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hd
  have hdiag := (tendsto_const_nhds (x := 2*c*H)).mul (hg.add hdsqrt)
  have hm := p6FixedWeightedMass_majorant_cofinite_zero38 (p5GapEnvelope38 u)
    (p6FixedGapRowEnvelope38 u) (p2RowEnvelope38 (realSlice u) 0) hgs hEs hds
  have hscaled : Tendsto (fun n : ℤ => (2*c^2*H)^2*Lib.invSqSum*p6FixedWeightedMajorant38 u n)
      cofinite (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero,p6FixedWeightedMajorant38] using tendsto_const_nhds.mul hm
  have hoff := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hscaled
  change Tendsto (fun n : ℤ =>
    (2*c*H)*(p5GapEnvelope38 u n+Real.sqrt
      (∑' m : ℤ, p2RowEnvelope38 (realSlice u) 0 m^2*Lib.c3w m n^2))+
    Real.sqrt ((2*c^2*H)^2*Lib.invSqSum*p6FixedWeightedMajorant38 u n))
    cofinite (𝓝 (0 : ℝ))
  simpa only [Function.comp_def,p6NonmissingNormMajorant38,add_zero,mul_zero,Real.sqrt_zero] using hdiag.add hoff

theorem p6Actual_nonmissing_compact_cofinite_operator_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℤ in cofinite, ∀ s ∈ p6ComplexFullGapCube38 u,
      ‖p6NonmissingDifference38 n (realSlice u) s‖ < ε := by
  obtain ⟨H,hH,hRatio⟩ := p6ComplexFullGapCube_common_ratio38 u
  have ht := (p6NonmissingNormMajorant_cofinite_zero38 u c H).eventually (gt_mem_nhds hε)
  filter_upwards [ht] with n hn s hs
  exact (p6GapCube_nonmissing_norm_majorant38 u C R c N hg hfam H hH hRatio n s hs).trans_lt hn

end
end NlsGge.GK38
