import NlsGge.Atomic.G1.G1097Support

/- G1-097 PRODUCTION01 (proof development, AUTHOR; NOT COMPILED: lane blocked by snapshot bound, see G1097_STOP.md).
   Target NlsGge/Atomic/G1/G1097.lean, namespace NlsGge.GKDefinitionDesign. Head from root/gpt6pro_followup7
   STATEMENTS/G1.md section G1-097 (no later Pro round 6-9 change found by grep). Supporting staged module:
   G1097A_SUPPORT01.lean.txt (four-solution integral, endpoint values, pointwise kernel rewritings). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1097_wedge_D_S (φ : PotPair) (z : ℂ) :
    wedge ![1, 1] (terminalSeed φ z) = -2 * normingFactor φ z := by
  simp only [wedge, terminalSeed, normingFactor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

theorem G1097_pp_pt (u v : PhysicalL2) (m n : ℤ) (hm : gkMu v m = gkMu u m)
    (hn : gkMu v n = gkMu u n) (s : ℝ) :
    kernelWedge38 (mixedKernel u v m false) (mixedKernel u v n false) s =
      G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
        ![1, 1] ![1, 1] ![1, 1] ![1, 1] s := by
  rw [G1097_kw_eq, G1097_plus_pt u v m hm s, G1097_plus_pt u v n hn s]
  rfl

theorem G1097_pp (u v : PhysicalL2) (h : normingDirichletMap u = normingDirichletMap v)
    (m n : ℤ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, kernelWedge38 (mixedKernel u v m false) (mixedKernel u v n false) t) = 0 := by
  have hm : gkMu v m = gkMu u m := (G1096_norming_eq u v h m).1
  have hn : gkMu v n = gkMu u n := (G1096_norming_eq u v h n).1
  have hφm : dirichletChar (realSlice u) (gkMu u m : ℂ) = 0 := G1096_dir_gkMu u m
  have hφn : dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 := G1096_dir_gkMu u n
  rw [intervalIntegral.integral_congr (fun s _ => G1097_pp_pt u v m n hm hn s)]
  rw [(G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
      (G1097_gkMu_ne u m n hmn) ![1, 1] ![1, 1] ![1, 1] ![1, 1]).2]
  rw [G1097_wedge_dd_one (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ) hφm hφn,
    G1097_wedge_dd_zero (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ)]
  simp

theorem G1097_pm_pt (u v : PhysicalL2) (m n : ℤ) (hm : gkMu v m = gkMu u m)
    (hn : gkMu v n = gkMu u n) (s : ℝ) :
    kernelWedge38 (mixedKernel u v m false) (mixedKernel u v n true) s =
      Complex.I * (G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
          ![1, 1] ![1, 1] ![1, 1] (terminalSeed (realSlice v) (gkMu u n : ℂ)) s +
        G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
          ![1, 1] (terminalSeed (realSlice u) (gkMu u n : ℂ)) ![1, 1] ![1, 1] s) := by
  rw [G1097_kw_eq, G1097_plus_pt u v m hm s, G1097_minus_pt u v n hn s,
    G1097_starProd_comm (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
      (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s),
    G1097_wedge_I_right]
  rfl

theorem G1097_pm (u v : PhysicalL2) (h : normingDirichletMap u = normingDirichletMap v)
    (m n : ℤ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, kernelWedge38 (mixedKernel u v m false) (mixedKernel u v n true) t) = 0 := by
  have hm : gkMu v m = gkMu u m := (G1096_norming_eq u v h m).1
  have hn : gkMu v n = gkMu u n := (G1096_norming_eq u v h n).1
  have hne := G1097_gkMu_ne u m n hmn
  have hφm : dirichletChar (realSlice u) (gkMu u m : ℂ) = 0 := G1096_dir_gkMu u m
  have hφn : dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 := G1096_dir_gkMu u n
  have hψm : dirichletChar (realSlice v) (gkMu u m : ℂ) = 0 := by
    rw [← hm]
    exact G1096_dir_gkMu v m
  have hψn : dirichletChar (realSlice v) (gkMu u n : ℂ) = 0 := by
    rw [← hn]
    exact G1096_dir_gkMu v n
  have i1 := (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
    ![1, 1] ![1, 1] ![1, 1] (terminalSeed (realSlice v) (gkMu u n : ℂ))).1
  have i2 := (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
    ![1, 1] (terminalSeed (realSlice u) (gkMu u n : ℂ)) ![1, 1] ![1, 1]).1
  rw [intervalIntegral.integral_congr (fun s _ => G1097_pm_pt u v m n hm hn s),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2]
  rw [(G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
      ![1, 1] ![1, 1] ![1, 1] (terminalSeed (realSlice v) (gkMu u n : ℂ))).2,
    (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
      ![1, 1] (terminalSeed (realSlice u) (gkMu u n : ℂ)) ![1, 1] ![1, 1]).2]
  rw [G1097_wedge_dd_one (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ) hφm hφn,
    G1097_wedge_dd_zero (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ),
    G1097_wedge_dd_one (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hψm hψn,
    G1097_wedge_dd_zero (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)]
  simp

theorem G1097_mm_pt (u v : PhysicalL2) (m n : ℤ) (hm : gkMu v m = gkMu u m)
    (hn : gkMu v n = gkMu u n) (s : ℝ) :
    kernelWedge38 (mixedKernel u v m true) (mixedKernel u v n true) s =
      -(G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
          ![1, 1] ![1, 1] (terminalSeed (realSlice v) (gkMu u m : ℂ))
          (terminalSeed (realSlice v) (gkMu u n : ℂ)) s +
        G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
          ![1, 1] (terminalSeed (realSlice u) (gkMu u n : ℂ))
          (terminalSeed (realSlice v) (gkMu u m : ℂ)) ![1, 1] s +
        G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
          (terminalSeed (realSlice u) (gkMu u m : ℂ)) ![1, 1]
          ![1, 1] (terminalSeed (realSlice v) (gkMu u n : ℂ)) s +
        G1097_W (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)
          (terminalSeed (realSlice u) (gkMu u m : ℂ)) (terminalSeed (realSlice u) (gkMu u n : ℂ))
          ![1, 1] ![1, 1] s) := by
  rw [G1097_kw_eq, G1097_minus_pt u v m hm s, G1097_minus_pt u v n hn s,
    G1097_starProd_comm (solution (realSlice v) (gkMu u m : ℂ) ![1, 1] s)
      (solution (realSlice u) (gkMu u m : ℂ) (terminalSeed (realSlice u) (gkMu u m : ℂ)) s),
    G1097_starProd_comm (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
      (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s),
    G1097_wedge_I_sum]
  rfl

theorem G1097_mm (u v : PhysicalL2) (h : normingDirichletMap u = normingDirichletMap v)
    (m n : ℤ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, kernelWedge38 (mixedKernel u v m true) (mixedKernel u v n true) t) = 0 := by
  have hm : gkMu v m = gkMu u m := (G1096_norming_eq u v h m).1
  have hn : gkMu v n = gkMu u n := (G1096_norming_eq u v h n).1
  have hne := G1097_gkMu_ne u m n hmn
  have hφm : dirichletChar (realSlice u) (gkMu u m : ℂ) = 0 := G1096_dir_gkMu u m
  have hφn : dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 := G1096_dir_gkMu u n
  have hψm : dirichletChar (realSlice v) (gkMu u m : ℂ) = 0 := by
    rw [← hm]
    exact G1096_dir_gkMu v m
  have hψn : dirichletChar (realSlice v) (gkMu u n : ℂ) = 0 := by
    rw [← hn]
    exact G1096_dir_gkMu v n
  have i1 := (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
    ![1, 1] ![1, 1] (terminalSeed (realSlice v) (gkMu u m : ℂ))
    (terminalSeed (realSlice v) (gkMu u n : ℂ))).1
  have i2 := (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
    ![1, 1] (terminalSeed (realSlice u) (gkMu u n : ℂ))
    (terminalSeed (realSlice v) (gkMu u m : ℂ)) ![1, 1]).1
  have i3 := (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
    (terminalSeed (realSlice u) (gkMu u m : ℂ)) ![1, 1]
    ![1, 1] (terminalSeed (realSlice v) (gkMu u n : ℂ))).1
  have i4 := (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
    (terminalSeed (realSlice u) (gkMu u m : ℂ)) (terminalSeed (realSlice u) (gkMu u n : ℂ))
    ![1, 1] ![1, 1]).1
  rw [intervalIntegral.integral_congr (fun s _ => G1097_mm_pt u v m n hm hn s),
    intervalIntegral.integral_neg,
    intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]
  rw [(G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
      ![1, 1] ![1, 1] (terminalSeed (realSlice v) (gkMu u m : ℂ))
      (terminalSeed (realSlice v) (gkMu u n : ℂ))).2,
    (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
      ![1, 1] (terminalSeed (realSlice u) (gkMu u n : ℂ))
      (terminalSeed (realSlice v) (gkMu u m : ℂ)) ![1, 1]).2,
    (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
      (terminalSeed (realSlice u) (gkMu u m : ℂ)) ![1, 1]
      ![1, 1] (terminalSeed (realSlice v) (gkMu u n : ℂ))).2,
    (G1097_four (realSlice u) (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hne
      (terminalSeed (realSlice u) (gkMu u m : ℂ)) (terminalSeed (realSlice u) (gkMu u n : ℂ))
      ![1, 1] ![1, 1]).2]
  rw [G1097_wedge_dd_one (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ) hφm hφn,
    G1097_wedge_dd_zero (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ),
    G1097_E1 (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ) hφm,
    G1097_E2 (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hψn,
    G1097_E3 (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ),
    G1097_E4 (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ),
    G1097_E2 (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ) hφn,
    G1097_E1 (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hψm,
    G1097_E4 (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ),
    G1097_E3 (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ),
    G1097_wedge_dd_one (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ) hψm hψn,
    G1097_wedge_dd_zero (realSlice v) (gkMu u m : ℂ) (gkMu u n : ℂ)]
  ring

theorem G1097_diag_pt (u v : PhysicalL2) (n : ℤ) (hμ : gkMu v n = gkMu u n)
    (hη : normingFactor (realSlice v) (gkMu u n : ℂ) = normingFactor (realSlice u) (gkMu u n : ℂ))
    (s : ℝ) :
    kernelWedge38 (mixedKernel u v n false) (mixedKernel u v n true) s =
      (2 * normingFactor (realSlice u) (gkMu u n : ℂ) * Complex.I) *
        (pairKernelExt38 (dirState u n) s 0 * pairKernelExt38 (dirState u n) s 1 +
          pairKernelExt38 (dirState v n) s 0 * pairKernelExt38 (dirState v n) s 1) := by
  have e1 : wedge (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
      (solution (realSlice v) (gkMu u n : ℂ) (terminalSeed (realSlice v) (gkMu u n : ℂ)) s) =
      -2 * normingFactor (realSlice u) (gkMu u n : ℂ) := by
    rw [G1097_wedge_solution_const, G1097_wedge_D_S, hη]
  have e2 : wedge (solution (realSlice u) (gkMu u n : ℂ) ![1, 1] s)
      (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s) =
      -2 * normingFactor (realSlice u) (gkMu u n : ℂ) := by
    rw [G1097_wedge_solution_const, G1097_wedge_D_S]
  rw [G1097_kw_eq, G1097_plus_pt u v n hμ s, G1097_minus_pt u v n hμ s, G1097_wedge_I_right,
    G1097_alg1, G1097_alg2, e1, e2, ← G1097_dirPt u n s, ← G1097_dirPtV u v n hμ s]
  ring

theorem G1097_diag (u v : PhysicalL2) (h : normingDirichletMap u = normingDirichletMap v) (n : ℤ) :
    (∫ t in (0 : ℝ)..1, kernelWedge38 (mixedKernel u v n false) (mixedKernel u v n true) t) =
      Complex.I * normingFactor (realSlice u) (gkMu u n : ℂ) *
        ((energy (dirState u n) + energy (dirState v n) : ℝ) : ℂ) := by
  have hμ : gkMu v n = gkMu u n := (G1096_norming_eq u v h n).1
  have hη : normingFactor (realSlice v) (gkMu u n : ℂ) = normingFactor (realSlice u) (gkMu u n : ℂ) :=
    (G1096_norming_eq u v h n).2
  have hX : IntervalIntegrable (fun s : ℝ => pairKernelExt38 (dirState u n) s 0 *
      pairKernelExt38 (dirState u n) s 1) volume 0 1 :=
    (((continuous_apply 0).comp (continuous_pairKernelExt38 (dirState u n))).mul
      ((continuous_apply 1).comp (continuous_pairKernelExt38 (dirState u n)))).intervalIntegrable 0 1
  have hY : IntervalIntegrable (fun s : ℝ => pairKernelExt38 (dirState v n) s 0 *
      pairKernelExt38 (dirState v n) s 1) volume 0 1 :=
    (((continuous_apply 0).comp (continuous_pairKernelExt38 (dirState v n))).mul
      ((continuous_apply 1).comp (continuous_pairKernelExt38 (dirState v n)))).intervalIntegrable 0 1
  have hQu : (∫ s in (0 : ℝ)..1, pairKernelExt38 (dirState u n) s 0 * pairKernelExt38 (dirState u n) s 1)
      = Q (dirState u n) / 2 := by
    unfold Q
    ring
  have hQv : (∫ s in (0 : ℝ)..1, pairKernelExt38 (dirState v n) s 0 * pairKernelExt38 (dirState v n) s 1)
      = Q (dirState v n) / 2 := by
    unfold Q
    ring
  rw [intervalIntegral.integral_congr (fun s _ => G1097_diag_pt u v n hμ hη s),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hX hY, hQu, hQv,
    real_denominator _ (dirState_real_symmetry u n), real_denominator _ (dirState_real_symmetry v n)]
  push_cast
  ring

theorem G1097_nonzero (u v : PhysicalL2) (n : ℤ) :
    Complex.I * normingFactor (realSlice u) (gkMu u n : ℂ) *
      ((energy (dirState u n) + energy (dirState v n) : ℝ) : ℂ) ≠ 0 := by
  have hnf : normingFactor (realSlice u) (gkMu u n : ℂ) ≠ 0 :=
    normingFactor_ne_zero_at_dirichlet_root38 _ _ (G1096_dir_gkMu u n)
  have hE : 0 < energy (dirState u n) := dirState_energy_positive u n
  have hF : 0 ≤ energy (dirState v n) := by
    unfold energy
    exact intervalIntegral.integral_nonneg zero_le_one (fun s _ => by positivity)
  have hsum : (0 : ℝ) < energy (dirState u n) + energy (dirState v n) := by linarith
  have hcast : ((energy (dirState u n) + energy (dirState v n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsum.ne'
  exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hnf) hcast

theorem G1_097 (u v : PhysicalL2)
    (h : normingDirichletMap u = normingDirichletMap v) :
    (∀ m n : ℤ,
      (∫ t in (0 : ℝ)..1,
        kernelWedge38 (mixedKernel u v m false) (mixedKernel u v n false) t) = 0 ∧
      (∫ t in (0 : ℝ)..1,
        kernelWedge38 (mixedKernel u v m true) (mixedKernel u v n true) t) = 0 ∧
      (∫ t in (0 : ℝ)..1,
        kernelWedge38 (mixedKernel u v m false) (mixedKernel u v n true) t) =
        if m=n then
          Complex.I * normingFactor (realSlice u) (gkMu u n : ℂ) *
            ((energy (dirState u n) + energy (dirState v n) : ℝ) : ℂ)
        else 0) ∧
    (∀ n : ℤ,
      Complex.I * normingFactor (realSlice u) (gkMu u n : ℂ) *
        ((energy (dirState u n) + energy (dirState v n) : ℝ) : ℂ) ≠ 0) := by
  refine ⟨fun m n => ⟨?_, ?_, ?_⟩, fun n => G1097_nonzero u v n⟩
  · by_cases hmn : m = n
    · rw [hmn]
      exact G1097_kw_self _
    · exact G1097_pp u v h m n hmn
  · by_cases hmn : m = n
    · rw [hmn]
      exact G1097_kw_self _
    · exact G1097_mm u v h m n hmn
  · by_cases hmn : m = n
    · rw [hmn, if_pos rfl]
      exact G1097_diag u v h n
    · rw [if_neg hmn]
      exact G1097_pm u v h m n hmn

end
end NlsGge.GKDefinitionDesign
