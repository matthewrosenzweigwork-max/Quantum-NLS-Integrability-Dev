import NlsGge.GK38.AbelianCompactDiagonalTails
import NlsGge.GK38.AbelianActualDifferenceOperatorBlock
import NlsGge.GK38.AbelianFullRealDiagonalEquiv
import NlsGge.GK38.AbelianFullGapCompactDomain

/-! UNCOMPILED actual missing diagonal tail. Parent's actual real square-error
row and actual real/complex derivative intertwining earn genuine complex
square summability. TRUE operator continuity plus genuine fixed compactness
then gives a uniform cofinite tail; no fixed open-ball tail is asserted. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Qstar_real_diagonal_norm_error38 (u : PhysicalL2) (s : P6RealSpace38) (m : ℤ) :
    ‖p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 m (1 : ℂ)) m-2‖=
      ‖p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m-2‖ := by
  have he := congrArg (fun q : Lib.L2Seq => q m)
    (p6RealQstar_include38 u s (lp.single 2 m (1 : ℝ)))
  rw [p6RealInclude_single38,p6RealInclude_apply38] at he
  rw [← he]
  have hcast :
      ((p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m : ℝ) : ℂ)-2=
      ((p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m-2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub,Complex.ofReal_ofNat]
  rw [hcast,Complex.norm_real]

theorem p6Qstar_complex_diagonal_square_error_summable38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38) :
    Summable (fun m : ℤ =>
      ‖p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 m (1 : ℂ)) m-2‖^2) := by
  obtain ⟨a,ha0,has,hbound⟩ := P6FullJacobian.actual_real_diagonal_square_error u C R hfam s
  apply has.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro m
  rw [p6Qstar_real_diagonal_norm_error38]
  have hb := hbound m
  nlinarith [norm_nonneg (p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m-2),ha0 m]

theorem p6Qstar_centered_diagonal38 (u : PhysicalL2) (s : P6RealSpace38) (m : ℤ) :
    (p6Qstar38 (realSlice u) (p6RealInclude38 s)-
      (2 : ℂ) • ContinuousLinearMap.id ℂ Lib.L2Seq) (lp.single 2 m (1 : ℂ)) m=
      p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 m (1 : ℂ)) m-2 := by
  change p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 m (1 : ℂ)) m-
    ((2 : ℂ) • lp.single (E := fun _ : ℤ => ℂ) 2 m (1 : ℂ)) m=_
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply_self,mul_one]

theorem p6Actual_missing_diagonal_compact_cofinite38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℤ in cofinite, ∀ s ∈ p5FullRealGapCube38 u,
      ‖(2 : ℂ)-p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 n (1 : ℂ)) n‖ < ε := by
  let A : P6RealSpace38 → (Lib.L2Seq →L[ℂ] Lib.L2Seq) :=
    fun s => p6Qstar38 (realSlice u) (p6RealInclude38 s)-
      (2 : ℂ) • ContinuousLinearMap.id ℂ Lib.L2Seq
  have hQ : Continuous (fun s : P6RealSpace38 => p6Qstar38 (realSlice u) (p6RealInclude38 s)) :=
    ContinuousOn.comp_continuous
      (g := fun p : PotPair × Lib.L2Seq => p6Qstar38 p.1 p.2)
      (f := fun s : P6RealSpace38 => (realSlice u,p6RealInclude38 s))
      p6Qstar_joint_analytic38.continuousOn
      (continuous_const.prodMk p6RealInclude38.continuous)
      (fun _ => ⟨realSlice_mem_gkW u,mem_univ _⟩)
  have hA : Continuous A := hQ.sub continuous_const
  have hsquare (s : P6RealSpace38) :
      Summable (fun m : ℤ => ‖A s (lp.single 2 m (1 : ℂ)) m‖^2) := by
    simpa only [A,p6Qstar_centered_diagonal38] using
      p6Qstar_complex_diagonal_square_error_summable38 u C R hfam s
  obtain ⟨S,hS⟩ := p6Compact_diagonal_tails38 (p5FullRealGapCube38 u)
    (p5FullRealGapCube_isCompact38 u) A hA
    (fun s _ => by simpa only [p6ComplexSingle_classical38] using! hsquare s) ε hε
  apply eventually_cofinite.mpr
  apply S.finite_toSet.subset
  intro n hn
  by_contra hnS
  apply hn
  intro s hs
  have hb := hS s hs n hnS
  have hb' : ‖A s (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)) n‖ < ε := by
    simpa only [p6ComplexSingle_classical38] using! hb
  have he : ‖A s (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)) n‖=
      ‖p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 n (1 : ℂ)) n-2‖ := by
    simpa only [A] using!
      congrArg (fun z : ℂ => ‖z‖) (p6Qstar_centered_diagonal38 u s n)
  have hb'' :
      ‖p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 n (1 : ℂ)) n-2‖ < ε :=
    he ▸ hb'
  simpa only [norm_sub_rev] using hb''

end
end NlsGge.GK38
