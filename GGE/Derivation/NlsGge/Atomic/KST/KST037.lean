import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST033
import NlsGge.Atomic.KST.KST035
import NlsGge.Atomic.KST.KST036
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host

/- KST-037 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST037.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-037"
   (identical in gpt6pro_followup1..10; no Pro round 5-12 entry touches KST-037).  No repair of the head.
   Route (source eq. (74)): F = adaptedFourier is analytic on the open componentwise 2M ball (KST-036) with
   ||F y - y|| <= M/16 on the closed componentwise 2M ball (KST-035).  For x in the componentwise M ball and h in
   the Hilbert pair space, the complex line t |-> F(x+t h) - (x+t h) on |t| <= M/(2||h||) stays in the componentwise
   3M/2 ball (each component norm <= pair norm), so Mathlib's Cauchy estimate
   `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` gives ||(dF_x - id) h|| <= (M/16)/(M/(2||h||)) = ||h||/8. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002

namespace NlsGge.ThirdConsultation.KST

theorem kst037 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  ∀ x ∈ componentBall ω M,
    HasFDerivAt (adaptedFourier ω hω (adaptedThreshold w M))
      (fderiv ℂ (adaptedFourier ω hω (adaptedThreshold w M)) x) x ∧
    ‖fderiv ℂ (adaptedFourier ω hω (adaptedThreshold w M)) x-
      ContinuousLinearMap.id ℂ (Weighted ω)‖ ≤ (1/8 : ℝ) := by
  intro ω hω
  letI := weightFact ω hω
  have hM0 : 0 < M := by linarith
  have hana := kst036 w Cw M hM hw hunbounded v hv
  obtain ⟨-, -, hmain⟩ := kst035 w Cw M hM hw hunbounded
  have hmain' := fun x hx => (hmain v hv x hx).2
  intro x hx
  set F := adaptedFourier ω hω (adaptedThreshold w M) with hF
  have hxU : x ∈ componentOpenBall ω (2*M) := fun ch => lt_of_le_of_lt (hx ch) (by linarith)
  have hdiff : DifferentiableAt ℂ F x := (hana x hxU).differentiableAt
  refine ⟨hdiff.hasFDerivAt, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => ?_
  have hsub : (fderiv ℂ F x - ContinuousLinearMap.id ℂ (Weighted ω)) h = fderiv ℂ F x h - h := by
    simp
  rw [hsub]
  by_cases h0 : h = 0
  · simp [h0]
  have hr : 0 < ‖h‖ := norm_pos_iff.2 h0
  set R : ℝ := M / (2 * ‖h‖) with hR
  have hRpos : 0 < R := by positivity
  -- points of the closed disc lie in the componentwise 3M/2 ball
  have hline : ∀ t : ℂ, ‖t‖ ≤ R → x + t • h ∈ componentBall ω (3 * M / 2) := by
    intro t ht ch
    have h1 : ‖(x + t • h) ch‖ ≤ ‖x ch‖ + ‖t‖ * ‖h ch‖ := by
      calc ‖(x + t • h) ch‖ = ‖x ch + t • h ch‖ := by simp
        _ ≤ ‖x ch‖ + ‖t • h ch‖ := norm_add_le _ _
        _ = ‖x ch‖ + ‖t‖ * ‖h ch‖ := by rw [norm_smul]
    have h2 : ‖h ch‖ ≤ ‖h‖ := PiLp.norm_apply_le h ch
    have h3 : ‖t‖ * ‖h ch‖ ≤ R * ‖h‖ :=
      mul_le_mul ht h2 (norm_nonneg _) hRpos.le
    have h4 : R * ‖h‖ = M / 2 := by rw [hR]; field_simp
    have h5 := hx ch
    linarith
  have hlineU : ∀ t : ℂ, ‖t‖ ≤ R → x + t • h ∈ componentOpenBall ω (2*M) := by
    intro t ht ch
    have := hline t ht ch
    linarith
  set g : ℂ → Weighted ω := fun t => F (x + t • h) - (x + t • h) with hg
  have hL : ∀ t : ℂ, HasDerivAt (fun s : ℂ => x + s • h) h t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hFd : ∀ t : ℂ, ‖t‖ ≤ R → DifferentiableAt ℂ (fun s : ℂ => F (x + s • h)) t := by
    intro t ht
    have hd : DifferentiableAt ℂ F (x + t • h) := (hana _ (hlineU t ht)).differentiableAt
    exact (hd.hasFDerivAt.comp_hasDerivAt t (hL t)).differentiableAt
  have hgd : DifferentiableOn ℂ g (Metric.closedBall 0 R) := by
    intro t ht
    have ht' : ‖t‖ ≤ R := by simpa using ht
    exact (((hFd t ht').sub (hL t).differentiableAt).differentiableWithinAt)
  have hdc : DiffContOnCl ℂ g (Metric.ball 0 R) :=
    hgd.diffContOnCl_ball (subset_refl _)
  have hsph : ∀ t ∈ Metric.sphere (0 : ℂ) R, ‖g t‖ ≤ M / 16 := by
    intro t ht
    have ht' : ‖t‖ ≤ R := by simp at ht; exact ht.le
    exact hmain' _ (fun ch => by
      have := hline t ht' ch
      linarith)
  have hcauchy : ‖deriv g 0‖ ≤ M / 16 / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc hsph
  have hder : HasDerivAt g (fderiv ℂ F x h - h) 0 := by
    have h1 : HasDerivAt (fun s : ℂ => F (x + s • h)) (fderiv ℂ F x h) 0 := by
      have hx0 : x = x + (0 : ℂ) • h := by simp
      have hd : HasFDerivAt F (fderiv ℂ F x) (x + (0 : ℂ) • h) := by
        rw [← hx0]; exact hdiff.hasFDerivAt
      exact hd.comp_hasDerivAt (0 : ℂ) (hL 0)
    exact h1.sub (hL 0)
  have hval : ‖fderiv ℂ F x h - h‖ ≤ M / 16 / R := by
    rw [← hder.deriv]; exact hcauchy
  have hcalc : M / 16 / R = ‖h‖ / 8 := by
    rw [hR]; field_simp; ring
  calc ‖fderiv ℂ F x h - h‖ ≤ M / 16 / R := hval
    _ = (1/8 : ℝ) * ‖h‖ := by rw [hcalc]; ring

end NlsGge.ThirdConsultation.KST
end
