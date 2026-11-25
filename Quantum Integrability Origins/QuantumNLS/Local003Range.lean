import Mathlib
import QuantumNLS.Local003Proj

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage M3: `ran P ⊂ 𝓓_σ`, the bounded
restriction `𝓛_u|_{ran P} = D + p_n P`, and eigenvectors inside the contour.

Source (proof, line 106): "The spectral subspace is invariant under `𝓛_u` and the contour in the definition of `B_n` gives
its bounded restriction."  Everything is stated for the actual objects `perturbedProj`, `dressedIntegral`, `LuGraph`.

* `P_Lu`: `(g, φ) ∈ Graph(𝓛_u) → P φ = D g + p_n P g`.
* `pair_mem`: `(P f, D f + p_n P f) ∈ Graph(𝓛_u)` for all `f` (needs graph self-adjointness: `Local002SA`).
* `eigen_P`: `(f, λ f) ∈ Graph(𝓛_u)` and `|λ - p_n| < r` give `P f = f` (Cauchy integral formula).
* `graph_add`, `graph_smul`, `graph_zero`: the graph of a self-adjoint operator is a linear subspace. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Range
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Circle
  QuantumNLS.Local003Hermitian QuantumNLS.Local003Proj QuantumNLS.LocalSpectral.Round25

variable {L κ r : ℝ}

/-- Vector form of the Riesz projection. -/
lemma P_apply (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) (f : H2 L) :
    perturbedProj L κ (u : ℝ → ℂ) n r f = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
      ∮ z in C(center L n, r), resolvent L κ (u : ℝ → ℂ) (parity n) z f := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  unfold perturbedProj rieszProj
  rw [smul_apply]
  congr 1
  exact QuantumNLS.Local002Free.circleIntegral_apply (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z)
    (hcont.circleIntegrable hr.le) f

/-- Vector form of the dressed integral. -/
lemma D_apply (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) (f : H2 L) :
    dressedIntegral L κ (u : ℝ → ℂ) n r f = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
      ∮ z in C(center L n, r), (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z f := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  unfold dressedIntegral
  rw [smul_apply]
  congr 1
  have := QuantumNLS.Local002Free.circleIntegral_apply
    (fun z => (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z)
    (((continuousOn_id.sub continuousOn_const).smul hcont).circleIntegrable hr.le) f
  simpa only [smul_apply] using this

/-- `P φ = D g + p_n P g` on the graph. -/
theorem P_Lu (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) {g φ : H2 L}
    (hp : (g, φ) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n)) :
    perturbedProj L κ (u : ℝ → ℂ) n r φ =
      dressedIntegral L κ (u : ℝ → ℂ) n r g + (pm L n : ℂ) • perturbedProj L κ (u : ℝ → ℂ) n r g := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  have hpt : ∀ z ∈ sphere (center L n) r, resolvent L κ (u : ℝ → ℂ) (parity n) z φ =
      z • resolvent L κ (u : ℝ → ℂ) (parity n) z g - g := by
    intro z hz
    have := (res_isRes hyp hr hr2 n u hq hz).2 (g, φ) hp
    simp only at this
    rw [map_sub, map_smul] at this
    rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp this).symm
  have c1 : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z g) (sphere (center L n) r) :=
    hcont.clm_apply continuousOn_const
  have c2 : ContinuousOn (fun z : ℂ => z • resolvent L κ (u : ℝ → ℂ) (parity n) z g)
      (sphere (center L n) r) := continuousOn_id.smul c1
  have c3 : ContinuousOn (fun z : ℂ => (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z g)
      (sphere (center L n) r) := (continuousOn_id.sub continuousOn_const).smul c1
  have c4 : ContinuousOn (fun z : ℂ => center L n • resolvent L κ (u : ℝ → ℂ) (parity n) z g)
      (sphere (center L n) r) := c1.const_smul (center L n)
  have i1 := c1.circleIntegrable hr.le
  have i2 := c2.circleIntegrable hr.le
  have i3 := c3.circleIntegrable hr.le
  have i4 := c4.circleIntegrable hr.le
  have igc : CircleIntegrable (fun _ : ℂ => g) (center L n) r :=
    continuousOn_const.circleIntegrable hr.le
  have hg0 : ∮ z in C(center L n, r), g = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      (f := fun _ => g) continuousOn_const (fun _ _ => differentiableAt_const _)
  have hsplit : ∮ z in C(center L n, r), z • resolvent L κ (u : ℝ → ℂ) (parity n) z g =
      (∮ z in C(center L n, r), (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z g) +
        center L n • ∮ z in C(center L n, r), resolvent L κ (u : ℝ → ℂ) (parity n) z g := by
    rw [← circleIntegral.integral_smul, ← circleIntegral.integral_add i3 i4]
    refine circleIntegral.integral_congr hr.le (fun z _ => ?_)
    simp only [sub_smul]; abel
  rw [P_apply hr hr2 n u hq, D_apply hr hr2 n u hq, P_apply hr hr2 n u hq g]
  have hcen : (pm L n : ℂ) = center L n := rfl
  rw [hcen, circleIntegral.integral_congr hr.le (fun z hz => hpt z hz), circleIntegral.integral_sub i2 igc,
    hg0, sub_zero, hsplit, smul_add, smul_comm (center L n)]

/-- The graph of a self-adjoint operator is closed under addition, scalars, and contains `0`. -/
lemma graph_add {G : Set (H2 L × H2 L)} (hG : G = adjGraph G) {p q : H2 L × H2 L} (hp : p ∈ G) (hq : q ∈ G) :
    p + q ∈ G := by
  rw [hG] at hp hq ⊢
  intro w hw
  simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
  rw [hp w hw, hq w hw]

lemma graph_smul {G : Set (H2 L × H2 L)} (hG : G = adjGraph G) (c : ℂ) {p : H2 L × H2 L} (hp : p ∈ G) :
    c • p ∈ G := by
  rw [hG] at hp ⊢
  intro w hw
  simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left]
  rw [hp w hw]

lemma graph_zero {G : Set (H2 L × H2 L)} (hG : G = adjGraph G) : ((0 : H2 L), (0 : H2 L)) ∈ G := by
  rw [hG]
  intro w hw
  simp

/-- The graph is a closed-under-combination set: the linear structure of eigenspaces. -/
lemma eig_add {G : Set (H2 L × H2 L)} (hG : G = adjGraph G) {lam : ℂ} {f f' : H2 L}
    (hf : (f, lam • f) ∈ G) (hf' : (f', lam • f') ∈ G) : (f + f', lam • (f + f')) ∈ G := by
  have := graph_add hG hf hf'
  simpa [smul_add] using this

lemma eig_smul {G : Set (H2 L × H2 L)} (hG : G = adjGraph G) {lam : ℂ} (c : ℂ) {f : H2 L}
    (hf : (f, lam • f) ∈ G) : (c • f, lam • (c • f)) ∈ G := by
  have := graph_smul hG c hf
  simpa [smul_comm lam c f] using this

/-- **`ran P ⊂ 𝓓_σ` with `𝓛_u P f = D f + p_n P f`.** -/
theorem pair_mem (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1)
    (hSA : IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n))) (f : H2 L) :
    (perturbedProj L κ (u : ℝ → ℂ) n r f,
      dressedIntegral L κ (u : ℝ → ℂ) n r f + (pm L n : ℂ) • perturbedProj L κ (u : ℝ → ℂ) n r f) ∈
        LuGraph L κ (u : ℝ → ℂ) (parity n) := by
  rw [hSA.eq]
  intro p hp
  have h1 := P_Lu hr hr2 n u hq hp
  simp only [inner_add_left, inner_smul_left, Complex.conj_ofReal]
  rw [proj_symm hL hr hr2 n u hq f p.2, h1, inner_add_right, inner_smul_right,
    ← dressedIntegral_symm hL hr hr2 n u hq f p.1, ← proj_symm hL hr hr2 n u hq f p.1]

/-- An eigenvector with eigenvalue inside the contour lies in the range of `P`: `P f = f`. -/
theorem eigen_P (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) {f : H2 L} {lam : ℂ}
    (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n)) (hlam : ‖lam - center L n‖ < r) :
    perturbedProj L κ (u : ℝ → ℂ) n r f = f := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  have hne : ∀ z ∈ sphere (center L n) r, z - lam ≠ 0 := by
    intro z hz hz0
    have hzr : ‖z - center L n‖ = r := mem_sphere_iff_norm.mp hz
    have : z = lam := sub_eq_zero.mp hz0
    rw [this] at hzr
    linarith
  have hpt : ∀ z ∈ sphere (center L n) r, resolvent L κ (u : ℝ → ℂ) (parity n) z f = (z - lam)⁻¹ • f := by
    intro z hz
    have := (res_isRes hyp hr hr2 n u hq hz).2 (f, lam • f) hf
    simp only at this
    rw [← sub_smul, map_smul] at this
    calc resolvent L κ (u : ℝ → ℂ) (parity n) z f
        = (z - lam)⁻¹ • ((z - lam) • resolvent L κ (u : ℝ → ℂ) (parity n) z f) := by
          rw [smul_smul, inv_mul_cancel₀ (hne z hz), one_smul]
      _ = (z - lam)⁻¹ • f := by rw [this]
  have hball : lam ∈ ball (center L n) r := mem_ball_iff_norm.mpr hlam
  have hcau := circleIntegral.integral_sub_inv_of_mem_ball hball
  rw [P_apply hr hr2 n u hq,
    circleIntegral.integral_congr hr.le (fun z hz => hpt z hz), circleIntegral.integral_smul_const, hcau,
    smul_smul]
  have h2 : ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * (2 * Real.pi * Complex.I) = 1 :=
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  rw [h2, one_smul]

end QuantumNLS.Local003Range
#print axioms QuantumNLS.Local003Range.P_Lu
#print axioms QuantumNLS.Local003Range.pair_mem
#print axioms QuantumNLS.Local003Range.eigen_P
#print axioms QuantumNLS.Local003Range.eig_add
