import NlsGge.GK38.AbelianNonmissingCompactOperatorLimit
import NlsGge.GK38.AbelianMissingCoordinateEstimates
import NlsGge.GK38.AbelianMissingDiagonalCompactTail

/-! UNCOMPILED actual padded Qn -> Qstar in TRUE operator norm, uniformly on
ONE genuine fixed full gap cube, along BOTH signed tails. The missing row,
column and diagonal are included. No inverse/tube/limit oracle is a premise. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6FullCornerNormMajorant38 (u : PhysicalL2) (c H : ℝ) (n : ℤ) : ℝ :=
  p6NonmissingNormMajorant38 u c H n+
    Real.sqrt ((2*c*H)^2*p6FixedGapRowEnvelope38 u n^2*Lib.invSqSum)+
    Real.sqrt ((2*c*H)^2*(∑' m : ℤ, p6FixedGapRowEnvelope38 u m^2*Lib.c3w m n^2))

theorem p6FullCornerNormMajorant_cofinite_zero38 (u : PhysicalL2) (c H : ℝ) :
    Tendsto (p6FullCornerNormMajorant38 u c H) cofinite (𝓝 (0 : ℝ)) := by
  have hE := p6FixedGapRowEnvelope_summable38 u
  have hrowmass : Tendsto (fun n : ℤ => (2*c*H)^2*p6FixedGapRowEnvelope38 u n^2*Lib.invSqSum)
      cofinite (𝓝 (0 : ℝ)) := by
    have hh := ((tendsto_const_nhds (x := (2*c*H)^2)).mul
      hE.tendsto_cofinite_zero).mul (tendsto_const_nhds (x := Lib.invSqSum))
    simpa only [mul_zero,zero_mul] using hh
  have hrow := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hrowmass
  have hcolmass : Tendsto (fun n : ℤ =>
      (2*c*H)^2*(∑' m : ℤ, p6FixedGapRowEnvelope38 u m^2*Lib.c3w m n^2))
      cofinite (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (p6ShiftedSquareMass_cofinite_zero38 (p6FixedGapRowEnvelope38 u) hE)
  have hcol := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hcolmass
  change Tendsto (fun n : ℤ =>
    p6NonmissingNormMajorant38 u c H n+
      Real.sqrt ((2*c*H)^2*p6FixedGapRowEnvelope38 u n^2*Lib.invSqSum)+
      Real.sqrt ((2*c*H)^2*(∑' m : ℤ, p6FixedGapRowEnvelope38 u m^2*Lib.c3w m n^2)))
    cofinite (𝓝 (0 : ℝ))
  simpa only [Function.comp_def,p6FullCornerNormMajorant38,Real.sqrt_zero,add_zero] using
    ((p6NonmissingNormMajorant_cofinite_zero38 u c H).add hrow).add hcol

theorem p6Actual_full_compact_cofinite_operator_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℤ in cofinite, ∀ s ∈ p5FullRealGapCube38 u,
      ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
        p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε := by
  obtain ⟨c,M,hg,hsp⟩ := hfam
  have hfamily : IsolatingFamily38 (realSlice u) C R := ⟨c,M,hg,hsp⟩
  obtain ⟨H,hH,hRatio⟩ := p6ComplexFullGapCube_common_ratio38 u
  have hscalar := (p6FullCornerNormMajorant_cofinite_zero38 u c H).eventually
    (gt_mem_nhds (half_pos hε))
  have hdiag := p6Actual_missing_diagonal_compact_cofinite38 u C R hfamily (ε/2) (half_pos hε)
  filter_upwards [hscalar,hdiag] with n hn hdn s hs
  let t : Lib.L2Seq := p6RealInclude38 s
  let T := p6PaddedJacobian38 n (realSlice u) t-p6Qstar38 (realSlice u) t
  have ht : t ∈ p6ComplexFullGapCube38 u := ⟨s,hs,rfl⟩
  have hB := p6GapCube_nonmissing_norm_majorant38 u C R c M hg hfamily H hH hRatio n t ht
  have hRow := p6GapCube_missing_row_norm38 u C R c M hg hfamily H hH hRatio n t ht
  have hCol := p6GapCube_missing_column_norm38 u C R c M hg hfamily H hH hRatio n t ht
  have hD : ‖T (lp.single 2 n (1 : ℂ)) n‖=
      ‖(2 : ℂ)-p6Qstar38 (realSlice u) t (lp.single 2 n (1 : ℂ)) n‖ := by
    change ‖p6PaddedJacobian38 n (realSlice u) t (lp.single 2 n (1 : ℂ)) n-
      p6Qstar38 (realSlice u) t (lp.single 2 n (1 : ℂ)) n‖=_
    rw [p6PaddedJacobian_missing_row38,lp.single_apply_self,mul_one]
  have hnorm := (p6Full_operator_norm_le_blocks38 n T).trans
    (add_le_add (add_le_add (add_le_add hB hRow) hCol) le_rfl)
  rw [hD] at hnorm
  calc
    _ ≤ p6FullCornerNormMajorant38 u c H n+
        ‖(2 : ℂ)-p6Qstar38 (realSlice u) t (lp.single 2 n (1 : ℂ)) n‖ := hnorm
    _ < ε/2+ε/2 := add_lt_add hn (hdn s hs)
    _ = ε := by ring

theorem p6ActualPadded_Qstar_compact_signed_operator_limit38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
      ∀ s ∈ p5FullRealGapCube38 u,
        ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
          p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε := by
  intro ε hε
  have ht := p6Actual_full_compact_cofinite_operator_limit38 u C R hfam ε hε
  have hbad : {n : ℤ | ¬ ∀ s ∈ p5FullRealGapCube38 u,
      ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
        p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε}.Finite := eventually_cofinite.mp ht
  obtain ⟨b,hb⟩ := (hbad.image (fun n : ℤ => |n|)).bddAbove
  refine ⟨b.natAbs+1,?_⟩
  intro n hn
  by_contra hnot
  have hnle : |n| ≤ b := hb ⟨n,hnot,rfl⟩
  have hbabs : b ≤ (b.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self b
  have hnat : n.natAbs ≤ b.natAbs := by
    have hh : (n.natAbs : ℤ) ≤ (b.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact hnle.trans hbabs
    exact_mod_cast hh
  omega

end
end NlsGge.GK38
