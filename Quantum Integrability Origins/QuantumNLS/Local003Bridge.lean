import Mathlib
import QuantumNLS.Local003Holo

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage H2c: the bridge from the actual reduced map
to the complexified one.

`bridge_pack`: for every `n` there are `F0 ∈ 𝒜`, `G : L² →L[ℝ] 𝒜` with `‖F0‖ ≤ 1/r`, `Jclm F0 = E E*` (the free spectral projection),
`‖G u‖ ≤ 2√κ C_{L,r} ‖u‖`, such that on the common ball `‖u‖ < goodRadius` (and `‖G u‖ < 1`) the actual entry
`(B_n(u) e₀)₁ = (reducedMatrix2 e₀)₁ = bn (G u)`.  Here `P = P*` and `S = S*` (stage M4) turn `U* D U` into `S Fm(P D P) S`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Bridge
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local003Analytic
  QuantumNLS.Local003Isometry QuantumNLS.Local003Neumann QuantumNLS.Local003Holo

variable {L κ r : ℝ}

lemma extC_wA_mul {n : ℤ} (F : Alg L (center L n) r) {z : ℂ} (hz : z ∈ sphere (center L n) r) :
    extC (wA L n r * F) z = (z - center L n) • extC F z := by
  rw [extC_apply _ hz, extC_apply _ hz]
  show ((z - center L n) • (1 : H2 L →L[ℂ] H2 L)) * F ⟨z, hz⟩ = _
  rw [smul_mul_assoc, one_mul]

theorem bridge_pack (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) :
    ∃ (F0 : Alg L (center L n) r) (G : Lp ℂ 2 (μI L) →L[ℝ] Alg L (center L n) r),
      ‖F0‖ ≤ 1 / r ∧
      Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n) ∧
      (∀ u, ‖G u‖ ≤ 2 * Real.sqrt κ * Cconst L r * ‖u‖) ∧
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < goodRadius κ L r → ‖G u‖ < 1 →
        Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 = bn L n hr F0 (G u)) := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  obtain ⟨F0, G, hF0e, hF0n, hGn, -, hres⟩ := neumann_pack (κ := κ) hr hr2 n
  have hres0 : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r := fun z hz =>
    hyp.res r n z hr hr2 hz
  have hP0 : Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n) := by
    rw [← freeProj_eq (κ := κ) hL hr hr2 n hres0, Jclm_apply]
    unfold freeProj rieszProj Jfun
    congr 1
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    rw [extC_apply _ hz]
    exact hF0e ⟨z, hz⟩
  refine ⟨F0, G, hF0n, hP0, hGn, fun u hu hG1 => ?_⟩
  have c := ctx_of_ball hL hr hr2 n u hu
  have hPe : perturbedProj L κ (u : ℝ → ℂ) n r = Pn L n hr F0 (G u) := by
    show _ = Jclm L (center L n) hr (F0 * Ring.inverse (1 - G u))
    rw [Jclm_apply]
    unfold perturbedProj rieszProj Jfun
    congr 1
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    exact hres u hG1 z hz
  have hDe : dressedIntegral L κ (u : ℝ → ℂ) n r = Dn L n hr F0 (G u) := by
    show _ = Jclm L (center L n) hr (wA L n r * (F0 * Ring.inverse (1 - G u)))
    rw [Jclm_apply]
    unfold dressedIntegral Jfun
    congr 1
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    rw [extC_wA_mul _ hz, ← hres u hG1 z hz]
  have hC : compressionMatrix L κ (u : ℝ → ℂ) n r = Fm L n (Pn L n hr F0 (G u)) := by
    rw [← hPe]; rfl
  have hS : Sn L n hr F0 (G u) = invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) := by
    unfold Sn; rw [hC]
  have hadj := adjU c
  -- the operator identity
  have hop : ∀ v : E2, Bf L κ (u : ℝ → ℂ) n r v = (pm L n : ℂ) • v + Bn L n hr F0 (G u) v := by
    intro v
    show (pm L n : ℂ) • v + (ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r))
      (dressedIntegral L κ (u : ℝ → ℂ) n r (Uf L κ (u : ℝ → ℂ) n r v)) = _
    rw [hadj]
    congr 1
    show invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)
      (ContinuousLinearMap.adjoint (embed L n) (perturbedProj L κ (u : ℝ → ℂ) n r
        (dressedIntegral L κ (u : ℝ → ℂ) n r (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n
          (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) v)))))) = _
    unfold Bn
    rw [hS, hPe, hDe]
    rfl
  have := congrArg (fun w : E2 => w 1) (hop (vec2 1 0))
  simp only at this
  rw [this]
  simp [bn, vec2]

end QuantumNLS.Local003Bridge
#print axioms QuantumNLS.Local003Bridge.bridge_pack
