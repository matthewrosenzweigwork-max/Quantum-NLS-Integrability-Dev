import NlsGge.Atomic.LIB.LIB009
import Mathlib.Analysis.Complex.Liouville
import NlsGge.Analysis.AnalyticTsum38

set_option autoImplicit false

open Metric

namespace NlsGge.Atomic.LIB

noncomputable section

universe u

/-- Cauchy's derivative estimate in the fixed positive-radius convention.
The Banach-valued norm bound is the pinned Mathlib estimate; analyticity on the
closed ball supplies differentiability on the ball and continuity on its
closure. -/
theorem cauchy_iterated_deriv_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {c : ℂ} {R M : ℝ} {f : ℂ → F}
    (k : ℕ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ‖iteratedDeriv k f c‖ ≤ k.factorial * M / R ^ k := by
  have hfc : DiffContOnCl ℂ f (ball c R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro z hz
    exact (hf z hz).differentiableAt.differentiableWithinAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    k hR hfc hM

/-- The corresponding bound for the factorial-normalized Taylor coefficient. -/
theorem cauchy_taylor_coefficient_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {c : ℂ} {R M : ℝ} {f : ℂ → F}
    (k : ℕ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ‖((k.factorial : ℂ)⁻¹) • iteratedDeriv k f c‖ ≤ M / R ^ k := by
  have hderiv := cauchy_iterated_deriv_bound k hR hf hM
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hnorm :
      ‖((k.factorial : ℂ)⁻¹) • iteratedDeriv k f c‖ =
        ‖iteratedDeriv k f c‖ / (k.factorial : ℝ) := by
    calc
      ‖((k.factorial : ℂ)⁻¹) • iteratedDeriv k f c‖ =
          ((k.factorial : ℝ)⁻¹) * ‖iteratedDeriv k f c‖ := by
        simp [norm_smul, norm_inv]
      _ = ‖iteratedDeriv k f c‖ / (k.factorial : ℝ) := by
        rw [div_eq_mul_inv, mul_comm]
  rw [hnorm]
  apply (div_le_iff₀ hfac).2
  calc
    ‖iteratedDeriv k f c‖ ≤ (k.factorial : ℝ) * M / R ^ k := by
      exact_mod_cast hderiv
    _ = M / R ^ k * (k.factorial : ℝ) := by ring

/-- The full iterated-derivative estimate along any unit complex line through a
point in the Banach parameter ball. -/
theorem cauchy_unit_line_iterated_deriv_bound {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x v : E} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall x R))
    (hM : ∀ z ∈ sphere x R, ‖f z‖ ≤ M)
    (hR : 0 < R) (hv : ‖v‖ = 1) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => f (x + z • v)) 0‖ ≤
      k.factorial * M / R ^ k := by
  let g : ℂ → F := fun z => f (x + z • v)
  have hmem (z : ℂ) (hz : ‖z‖ ≤ R) : x + z • v ∈ closedBall x R := by
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖x + z • v - x‖ = ‖z • v‖ := by congr 1; abel
      _ = ‖z‖ * ‖v‖ := norm_smul _ _
      _ = ‖z‖ := by rw [hv, mul_one]
      _ ≤ R := hz
  have hga (z : ℂ) (hz : ‖z‖ ≤ R) : AnalyticAt ℂ g z := by
    haveI : IsScalarTower ℂ ℂ E := ⟨fun a b w => by simpa using (mul_smul a b w)⟩
    have hline : AnalyticAt ℂ (fun t : ℂ => x + t • v) z := by
      have hsmul : AnalyticAt ℂ (fun t : ℂ => t • v) z := by
        convert analyticAt_id.smul (analyticAt_const (v := v) (x := z)) using 1
        · ext t
          rfl
        · exact this
      have hconst : AnalyticAt ℂ (fun _ : ℂ => x) z := analyticAt_const
      convert hsmul.add hconst using 1
      ext t
      simp [add_comm]
    have hfz : AnalyticAt ℂ f (x + z • v) := hf _ (hmem z hz)
    have hcomp : AnalyticAt ℂ (f ∘ (fun t : ℂ => x + t • v)) z :=
      AnalyticAt.comp (g := f) (f := fun t : ℂ => x + t • v) hfz hline
    simpa [g, Function.comp_def] using hcomp
  have hgan : AnalyticOnNhd ℂ g (closedBall 0 R) := by
    intro z hz
    have hz' : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact hga z hz'
  have hcircle : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ M := by
    intro z hz
    have hz_norm : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
    apply hM (x + z • v)
    rw [mem_sphere_iff_norm]
    calc
      ‖(x + z • v) - x‖ = ‖z • v‖ := by congr 1; abel
      _ = ‖z‖ * ‖v‖ := norm_smul _ _
      _ = R := by rw [hv, mul_one, hz_norm]
  simpa [g] using cauchy_iterated_deriv_bound k hR hgan hcircle

/-- Cauchy's estimate along a unit complex line through the center of a Banach
parameter ball.  The boundary circle of a unit-direction line maps exactly to
the boundary sphere, so the original boundary supremum is retained. -/
theorem cauchy_fderiv_center_unit_direction_bound {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x v : E} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall x R))
    (hM : ∀ z ∈ sphere x R, ‖f z‖ ≤ M)
    (hR : 0 < R) (hv : ‖v‖ = 1) :
    ‖fderiv ℂ f x v‖ ≤ M / R := by
  let g : ℂ → F := fun z => f (x + z • v)
  have hmem (z : ℂ) (hz : ‖z‖ ≤ R) : x + z • v ∈ closedBall x R := by
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖x + z • v - x‖ = ‖z • v‖ := by congr 1; abel
      _ = ‖z‖ * ‖v‖ := norm_smul _ _
      _ = ‖z‖ := by rw [hv, mul_one]
      _ ≤ R := hz
  have hline (z : ℂ) (hz : ‖z‖ ≤ R) :
      HasDerivAt g (fderiv ℂ f (x + z • v) v) z := by
    have hF : HasFDerivAt f (fderiv ℂ f (x + z • v)) (x + z • v) :=
      ((hf _ (hmem z hz)).differentiableAt).hasFDerivAt
    have hz' : HasDerivAt (fun t : ℂ => x + t • v) v z := by
      simpa using ((hasDerivAt_id z).smul_const v).const_add x
    exact hF.comp_hasDerivAt z hz'
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro z hz
    have hz' : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact (hline z hz').differentiableAt.differentiableWithinAt
  have hcircle : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ M := by
    intro z hz
    have hz_norm : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
    apply hM (x + z • v)
    rw [mem_sphere_iff_norm]
    calc
      ‖(x + z • v) - x‖ = ‖z • v‖ := by congr 1; abel
      _ = ‖z‖ * ‖v‖ := norm_smul _ _
      _ = R := by rw [hv, mul_one, hz_norm]
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hR hdc hcircle
  have hderiv0 := (hline 0 (by simpa using hR.le)).deriv
  have hzero : deriv g 0 = fderiv ℂ f x v := by
    simpa [g] using hderiv0
  rw [hzero] at hbound
  exact hbound

/-- Banach-parameter Cauchy estimate on a smaller ball.  The hypotheses retain
the nested radii `r' + R ≤ r`; the conclusion bounds the full Fréchet operator
norm and therefore each unit directional derivative without polarization. -/
theorem cauchy_fderiv_unit_direction_bound {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x y v : E} {r r' R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall x r))
    (hM : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M)
    (hy : y ∈ closedBall x r') (hR : 0 < R) (hrr : r' + R ≤ r)
    (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℂ f y v‖ ≤ M / R := by
  have hopen : ‖fderiv ℂ f y‖ ≤ M / R :=
    NlsGge.AnalyticTsum38.norm_fderiv_le_of_closedBall38
      (f := f) (x := x) (y := y) (r := r) (r' := r') (R := R) (M := M)
      hf hM hy hR hrr
  calc
    ‖fderiv ℂ f y v‖ ≤ ‖fderiv ℂ f y‖ * ‖v‖ := (fderiv ℂ f y).le_opNorm v
    _ ≤ ‖fderiv ℂ f y‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = ‖fderiv ℂ f y‖ := mul_one _
    _ ≤ M / R := hopen

end
end NlsGge.Atomic.LIB
