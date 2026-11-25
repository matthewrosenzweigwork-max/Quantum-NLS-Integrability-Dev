import NlsGge.GK38.PairCompactInterval

/-! # F6: operator-norm continuity of the Volterra primitive tests

The time modulus comes from the L2 small-interval estimate, not from
operator-norm continuity of point evaluation on arbitrary continuous maps.
-/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- A potential is tested by an entry of its zero-spectral Volterra primitive. -/
def primitiveTest38 (N : PairCont38) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    PotPair →L[ℂ] ℂ :=
  (fundEntryL38 t i j).comp
    ((ContinuousLinearMap.apply ℂ PairCont38 N).comp volterraZeroL)

@[simp] theorem primitiveTest38_apply (N : PairCont38) (t : Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) (φ : PotPair) :
    primitiveTest38 N t i j φ = volterraP φ 0 N t i j := rfl

/-- Uniform operator-norm square-root modulus in time. -/
theorem norm_primitiveTest38_time_sub (N : PairCont38)
    (s t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖primitiveTest38 N t i j - primitiveTest38 N s i j‖ ≤
      2 * ‖N‖ * Real.sqrt |(t : ℝ) - s| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
  simpa only [sub_apply, primitiveTest38_apply, mul_assoc, mul_left_comm,
    mul_comm] using norm_volterraZero_time_sub38 φ N s t i j

/-- Uniform operator-norm Lipschitz bound in the continuous input. -/
theorem norm_primitiveTest38_input_sub (N M : PairCont38)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖primitiveTest38 N t i j - primitiveTest38 M t i j‖ ≤ 2 * ‖N - M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
  simp only [sub_apply, primitiveTest38_apply]
  have heq : volterraP φ 0 N t i j - volterraP φ 0 M t i j =
      volterraP φ 0 (N - M) t i j := by
    rw [map_sub]; rfl
  rw [heq]
  have hv : ‖volterraP φ 0‖ ≤ 2 * ‖φ‖ := by
    simpa using (norm_volterraP_le φ 0).trans
      (by simpa using potL1Norm38_le_two_mul φ)
  calc
    ‖volterraP φ 0 (N - M) t i j‖ ≤ ‖volterraP φ 0 (N - M)‖ :=
      (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
        ((volterraP φ 0 (N - M)).norm_coe_le_norm t))
    _ ≤ ‖volterraP φ 0‖ * ‖N - M‖ := (volterraP φ 0).le_opNorm _
    _ ≤ (2 * ‖N - M‖) * ‖φ‖ := by
      calc _ ≤ (2 * ‖φ‖) * ‖N - M‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
           _ = _ := by ring

/-- Joint continuity of the smoothed scalar test in input and time. -/
theorem continuous_primitiveTest38 (i j : Fin 2) :
    Continuous (fun p : PairCont38 × Set.Icc (0 : ℝ) 1 => primitiveTest38 p.1 p.2 i j) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : ∀ q : PairCont38 × Set.Icc (0 : ℝ) 1,
      ‖primitiveTest38 q.1 q.2 i j - primitiveTest38 p.1 p.2 i j‖ ≤
        2 * ‖q.1 - p.1‖ + 2 * ‖p.1‖ * Real.sqrt |(q.2 : ℝ) - p.2| := by
    intro q
    exact (norm_sub_le_norm_sub_add_norm_sub _ (primitiveTest38 p.1 q.2 i j) _).trans
      (add_le_add (norm_primitiveTest38_input_sub q.1 p.1 q.2 i j)
        (norm_primitiveTest38_time_sub p.1 p.2 q.2 i j))
  have hc : Continuous (fun q : PairCont38 × Set.Icc (0 : ℝ) 1 =>
      2 * ‖q.1 - p.1‖ + 2 * ‖p.1‖ * Real.sqrt |(q.2 : ℝ) - p.2|) := by fun_prop
  exact squeeze_zero (fun _ => norm_nonneg _) hb (by simpa using hc.tendsto p)

end
end NlsGge.GK38
