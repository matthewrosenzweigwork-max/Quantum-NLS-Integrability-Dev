import Mathlib
import QuantumNLS.Local003Bridge
import QuantumNLS.Local003Est
import QuantumNLS.Local003Odd

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage R1: instantiation of the abstract
estimates `Local003Est.est_cubic`/`est_deriv` on the actual objects.

* `compat`: on the Banach algebra `Alg = C(Γ_n, B(H))` the real-module structure used for the bounded real-linear map
  `G` of `neumann_pack` agrees with the one induced by the complex structure: `(t:ℝ) • Y = (t:ℂ) • Y`.
  `agree_eq`: hence the two `NormedSpace ℝ` structures coincide, and `est_cubic_agree`/`est_deriv_agree` transport the
  abstract estimates to `G : L² →L[ℝ] Alg`.
* `bridge_pack'`: the proof of `Local003Bridge.bridge_pack`, with the facts of `neumann_pack` that the first-order
  computation needs retained (`F0` is the free resolvent on `Γ_n`, `G u z` is the multiplication operator `V_u R_0(z)`).
* `inst_est`: with `U = L²`, `X = Alg`, `𝔟 = bn`, `b u = (B_n(u) e₀)₁`, `q0 = 1/3`, `M = 27 r/2`, `K = 2√κ C_{L,r}`,
  `ρ = min(goodRadius, 1/(24(K+1)))` (`n`-independent), parity from `Local003Odd.entries_parity`:
  the cubic estimate `‖b(u) - ℓ(u)‖ ≤ C₁‖u‖³`, `ℓ(u) = d/dζ bn(ζ G u)|₀`, and the quadratic derivative estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Inst
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local003Neumann QuantumNLS.Local003Holo
  QuantumNLS.Local003Analytic

variable {L κ r : ℝ}

/-- The two real-module structures on the Banach algebra agree: `t • Y = (t : ℂ) • Y`. -/
lemma compat (c : ℂ) (t : ℝ) (Y : Alg L c r) : t • Y = (t : ℂ) • Y := by
  ext z x : 2
  show t • ((Y z) x) = (t : ℂ) • ((Y z) x)
  exact (Complex.coe_smul t _).symm

lemma agree_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (iR : NormedSpace ℝ X)
    (h : ∀ (t : ℝ) (x : X), t • x = (t : ℂ) • x) : iR = NormedSpace.complexToReal := by
  apply NormedSpace.ext
  funext t x
  exact h t x

section Transport
variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [iR : NormedSpace ℝ X]
  (h : ∀ (t : ℝ) (x : X), t • x = (t : ℂ) • x) (G : U →L[ℝ] X) (𝔟 : X → ℂ) (b : U → ℂ) {q0 M K ρ : ℝ}

include h in
theorem est_cubic_agree (hq0 : 0 < q0)
    (hana : AnalyticOnNhd ℂ 𝔟 (ball 0 q0)) (hM : ∀ Y ∈ ball (0 : X) q0, ‖𝔟 Y‖ ≤ M)
    (hK : 0 ≤ K) (hGn : ∀ u, ‖G u‖ ≤ K * ‖u‖) (hρ : 0 < ρ) (hρK : K * ρ ≤ q0 / 8)
    (hb : ∀ u, ‖u‖ < ρ → b u = 𝔟 (G u)) (hodd : ∀ u, ‖u‖ < ρ → b (-u) = - b u)
    {u : U} (hu : ‖u‖ < ρ) :
    ‖b u - deriv (fun ζ : ℂ => 𝔟 (ζ • G u)) 0‖ ≤ 32 * M * (K * ‖u‖) ^ 3 / q0 ^ 3 := by
  have e := agree_eq iR h
  subst e
  exact QuantumNLS.Local003Est.est_cubic G 𝔟 b hq0 hana hM hK hGn hρ hρK hb hodd hu

include h in
theorem est_deriv_agree (hq0 : 0 < q0)
    (hana : AnalyticOnNhd ℂ 𝔟 (ball 0 q0)) (hM : ∀ Y ∈ ball (0 : X) q0, ‖𝔟 Y‖ ≤ M)
    (hK : 0 ≤ K) (hGn : ∀ u, ‖G u‖ ≤ K * ‖u‖) (hρ : 0 < ρ) (hρK : K * ρ ≤ q0 / 8)
    (hb : ∀ u, ‖u‖ < ρ → b u = 𝔟 (G u)) (hodd : ∀ u, ‖u‖ < ρ → b (-u) = - b u)
    {u : U} (hu : ‖u‖ < ρ) (v : U) :
    DifferentiableAt ℝ b u ∧
      ‖fderiv ℝ b u v - fderiv ℝ b 0 v‖ ≤ 128 * M * (K * ‖u‖) ^ 2 * (K * ‖v‖) / q0 ^ 3 := by
  have e := agree_eq iR h
  subst e
  exact QuantumNLS.Local003Est.est_deriv G 𝔟 b hq0 hana hM hK hGn hρ hρK hb hodd hu v

end Transport

/-- The proof of `Local003Bridge.bridge_pack`, retaining the facts of `neumann_pack` used by the first-order
computation: `F0` is the free resolvent on `Γ_n` and `G u z` is the multiplication operator `V_u R_0(z)`. -/
theorem bridge_pack' (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) :
    ∃ (F0 : Alg L (center L n) r) (G : Lp ℂ 2 (μI L) →L[ℝ] Alg L (center L n) r),
      (∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz) ∧
      ‖F0‖ ≤ 1 / r ∧
      Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n) ∧
      (∀ u, ‖G u‖ ≤ 2 * Real.sqrt κ * Cconst L r * ‖u‖) ∧
      (∀ (u : Lp ℂ 2 (μI L)) (zz : sphere (center L n) r),
        IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) zz) (u : ℝ → ℂ) (G u zz)) ∧
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < QuantumNLS.Local003Isometry.goodRadius κ L r → ‖G u‖ < 1 →
        QuantumNLS.Local003Analytic.Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 = bn L n hr F0 (G u)) := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  obtain ⟨F0, G, hF0e, hF0n, hGn, hMul, hres⟩ := neumann_pack (κ := κ) hr hr2 n
  have hres0 : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r := fun z hz =>
    hyp.res r n z hr hr2 hz
  have hP0 : Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n) := by
    rw [← QuantumNLS.Local002Free.freeProj_eq (κ := κ) hL hr hr2 n hres0, Jclm_apply]
    unfold freeProj rieszProj Jfun
    congr 1
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    rw [extC_apply _ hz]
    exact hF0e ⟨z, hz⟩
  refine ⟨F0, G, hF0e, hF0n, hP0, hGn, hMul, fun u hu hG1 => ?_⟩
  have c := QuantumNLS.Local003Isometry.ctx_of_ball hL hr hr2 n u hu
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
    rw [QuantumNLS.Local003Bridge.extC_wA_mul _ hz, ← hres u hG1 z hz]
  have hC : compressionMatrix L κ (u : ℝ → ℂ) n r = Fm L n (Pn L n hr F0 (G u)) := by
    rw [← hPe]; rfl
  have hS : Sn L n hr F0 (G u) = invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) := by
    unfold Sn; rw [hC]
  have hadj := QuantumNLS.Local003Isometry.adjU c
  have hop : ∀ v : E2, QuantumNLS.Local003Analytic.Bf L κ (u : ℝ → ℂ) n r v =
      (pm L n : ℂ) • v + Bn L n hr F0 (G u) v := by
    intro v
    show (pm L n : ℂ) • v + (ContinuousLinearMap.adjoint (QuantumNLS.Local003Analytic.Uf L κ (u : ℝ → ℂ) n r))
      (dressedIntegral L κ (u : ℝ → ℂ) n r (QuantumNLS.Local003Analytic.Uf L κ (u : ℝ → ℂ) n r v)) = _
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

lemma ball_norm_lt {c : ℂ} {Y : Alg L c r} {q : ℝ} (hY : Y ∈ ball (0 : Alg L c r) q) : ‖Y‖ < q := by
  have h2 : dist Y 0 < q := hY
  have h3 : ‖Y‖ = dist Y 0 := (dist_zero_right Y).symm
  rw [h3]; exact h2

/-- The constants of the estimates (depending only on `r`, `κ`, `L`). -/
def Kc (κ L r : ℝ) : ℝ := 2 * Real.sqrt κ * Cconst L r
def rho1 (κ L r : ℝ) : ℝ := min (QuantumNLS.Local003Isometry.goodRadius κ L r) (1 / (24 * (Kc κ L r + 1)))
def C1c (κ L r : ℝ) : ℝ := 32 * (27 * r / 2) * Kc κ L r ^ 3 / (1 / 3 : ℝ) ^ 3
def C2c (κ L r : ℝ) : ℝ := 128 * (27 * r / 2) * Kc κ L r ^ 3 / (1 / 3 : ℝ) ^ 3

lemma Kc_nonneg (κ L r : ℝ) : 0 ≤ Kc κ L r := by
  unfold Kc
  have := Cconst_nonneg L r
  positivity

lemma rho1_pos (κ L r : ℝ) : 0 < rho1 κ L r := by
  unfold rho1
  refine lt_min (QuantumNLS.Local003Isometry.goodRadius_pos κ L r) ?_
  have := Kc_nonneg κ L r
  positivity

lemma rho1_le_good (κ L r : ℝ) : rho1 κ L r ≤ QuantumNLS.Local003Isometry.goodRadius κ L r := min_le_left _ _

lemma Kc_rho1 (κ L r : ℝ) : Kc κ L r * rho1 κ L r ≤ (1 / 3 : ℝ) / 8 := by
  have hK := Kc_nonneg κ L r
  have h1 : rho1 κ L r ≤ 1 / (24 * (Kc κ L r + 1)) := min_le_right _ _
  calc Kc κ L r * rho1 κ L r ≤ Kc κ L r * (1 / (24 * (Kc κ L r + 1))) := by gcongr
    _ ≤ (1 / 3 : ℝ) / 8 := by
      rw [← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith

/-- **R1.** The abstract estimates on the actual objects, uniformly in `n`. -/
theorem inst_est (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) :
    ∃ (F0 : Alg L (center L n) r) (G : Lp ℂ 2 (μI L) →L[ℝ] Alg L (center L n) r),
      (∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz) ∧
      ‖F0‖ ≤ 1 / r ∧
      Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n) ∧
      (∀ u, ‖G u‖ ≤ Kc κ L r * ‖u‖) ∧
      (∀ (u : Lp ℂ 2 (μI L)) (zz : sphere (center L n) r),
        IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) zz) (u : ℝ → ℂ) (G u zz)) ∧
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < rho1 κ L r →
        QuantumNLS.Local003Analytic.Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 = bn L n hr F0 (G u)) ∧
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < rho1 κ L r →
        ‖QuantumNLS.Local003Analytic.Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 -
          deriv (fun ζ : ℂ => bn L n hr F0 (ζ • G u)) 0‖ ≤ C1c κ L r * ‖u‖ ^ 3) ∧
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < rho1 κ L r →
        DifferentiableAt ℝ (fun w : Lp ℂ 2 (μI L) => QuantumNLS.Local003Analytic.Bf L κ (w : ℝ → ℂ) n r (vec2 1 0) 1) u ∧
        ∀ v : Lp ℂ 2 (μI L),
          ‖fderiv ℝ (fun w : Lp ℂ 2 (μI L) => QuantumNLS.Local003Analytic.Bf L κ (w : ℝ → ℂ) n r (vec2 1 0) 1) u v -
            fderiv ℝ (fun w : Lp ℂ 2 (μI L) => QuantumNLS.Local003Analytic.Bf L κ (w : ℝ → ℂ) n r (vec2 1 0) 1) 0 v‖
              ≤ C2c κ L r * ‖u‖ ^ 2 * ‖v‖) := by
  obtain ⟨F0, G, hF0e, hF0n, hP0, hGn, hMul, hbr⟩ := bridge_pack' (κ := κ) hL hr hr2 n
  have hK := Kc_nonneg κ L r
  have hρ := rho1_pos κ L r
  have hρK := Kc_rho1 κ L r
  have hGn' : ∀ u, ‖G u‖ ≤ Kc κ L r * ‖u‖ := fun u => by
    have := hGn u; unfold Kc; linarith
  have hsmallG : ∀ u : Lp ℂ 2 (μI L), ‖u‖ < rho1 κ L r → ‖G u‖ < 1 := fun u hu => by
    have h1 : Kc κ L r * ‖u‖ ≤ Kc κ L r * rho1 κ L r := by gcongr
    have h2 : Kc κ L r * ‖u‖ ≤ 1 / 24 := by linarith
    linarith [hGn' u]
  have hb : ∀ u : Lp ℂ 2 (μI L), ‖u‖ < rho1 κ L r →
      QuantumNLS.Local003Analytic.Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 = bn L n hr F0 (G u) := fun u hu =>
    hbr u (lt_of_lt_of_le hu (rho1_le_good κ L r)) (hsmallG u hu)
  have hodd : ∀ u : Lp ℂ 2 (μI L), ‖u‖ < rho1 κ L r →
      QuantumNLS.Local003Analytic.Bf L κ ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) n r (vec2 1 0) 1 =
        -QuantumNLS.Local003Analytic.Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 := fun u hu =>
    (QuantumNLS.Local003Odd.entries_parity hL hr hr2 n u
      (lt_of_lt_of_le (lt_of_lt_of_le hu (rho1_le_good κ L r)) (min_le_left _ _))).2
  have hana : AnalyticOnNhd ℂ (bn L n hr F0) (ball 0 (1 / 3 : ℝ)) := fun Y hY =>
    analyticAt_bn L n hr F0 hF0n hL hP0 (ball_norm_lt hY)
  have hM : ∀ Y ∈ ball (0 : Alg L (center L n) r) (1 / 3 : ℝ), ‖bn L n hr F0 Y‖ ≤ 27 * r / 2 := fun Y hY =>
    bound_bn L n hr F0 hF0n hL hP0 (ball_norm_lt hY)
  refine ⟨F0, G, hF0e, hF0n, hP0, hGn', hMul, hb, fun u hu => ?_, fun u hu => ?_⟩
  · have := @est_cubic_agree (Lp ℂ 2 (μI L)) (Alg L (center L n) r) inferInstance inferInstance inferInstance
      inferInstance inferInstance (fun t Y => compat _ t Y) G (bn L n hr F0)
      (fun w : Lp ℂ 2 (μI L) => QuantumNLS.Local003Analytic.Bf L κ (w : ℝ → ℂ) n r (vec2 1 0) 1)
      (1 / 3) (27 * r / 2) (Kc κ L r) (rho1 κ L r) (by norm_num) hana hM hK hGn' hρ hρK hb hodd u hu
    refine this.trans (le_of_eq ?_)
    unfold C1c; ring
  · have key := fun v => @est_deriv_agree (Lp ℂ 2 (μI L)) (Alg L (center L n) r) inferInstance inferInstance
      inferInstance inferInstance inferInstance (fun t Y => compat _ t Y) G (bn L n hr F0)
      (fun w : Lp ℂ 2 (μI L) => QuantumNLS.Local003Analytic.Bf L κ (w : ℝ → ℂ) n r (vec2 1 0) 1)
      (1 / 3) (27 * r / 2) (Kc κ L r) (rho1 κ L r) (by norm_num) hana hM hK hGn' hρ hρK hb hodd u hu v
    refine ⟨(key 0).1, fun v => (key v).2.trans (le_of_eq ?_)⟩
    unfold C2c; ring

end QuantumNLS.Local003Inst
#print axioms QuantumNLS.Local003Inst.compat
#print axioms QuantumNLS.Local003Inst.est_cubic_agree
#print axioms QuantumNLS.Local003Inst.est_deriv_agree
#print axioms QuantumNLS.Local003Inst.bridge_pack'
#print axioms QuantumNLS.Local003Inst.inst_est
