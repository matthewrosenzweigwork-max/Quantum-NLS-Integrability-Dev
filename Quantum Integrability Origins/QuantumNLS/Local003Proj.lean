import Mathlib
import QuantumNLS.Local003Hermitian
import QuantumNLS.Local002Rank

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage M2: operator-level facts about the
spectral projection `P = P_n(u)` and the operator `𝓛_u` on `𝓓_σ`.

* `proj_symm`: `P_n(u)` is self-adjoint (the contour trick of `Local003Hermitian.dressedIntegral_symm` with weight `1`).
* `P_Lu`: for `(g, φ) ∈ Graph(𝓛_u)`, `P φ = D g + p_n P g`, where `D` is the dressed integral
  `(2πi)⁻¹∮(z-p_n)(z-𝓛_u)⁻¹dz` (from `R(z)φ = z R(z) g - g`).
* `pair_mem`: `(P f, D f + p_n P f) ∈ Graph(𝓛_u)` for every `f ∈ H`; hence `ran P ⊂ 𝓓_σ` and `𝓛_u|_{ran P} = p_n + D` is
  the bounded operator `D + p_n P` (self-adjointness of the graph, with Hermiticity of `P` and `D`).
* `eigen_P`: an eigenvector of `𝓛_u` with eigenvalue strictly inside the contour satisfies `P f = f`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Proj
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Circle
  QuantumNLS.Local003Hermitian QuantumNLS.LocalSpectral.Round24 QuantumNLS.LocalSpectral.Round25

variable {L κ r : ℝ}

/-- The resolvent on the contour is continuous. -/
lemma res_cont (hyp : FreeResolventHyp L κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) :
    ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (sphere (center L n) r) := by
  have hpos : 0 < 1 - qpar κ L r u := by linarith
  exact continuousOn_resolvent _ (M := r⁻¹ * (1 - qpar κ L r u)⁻¹) (by positivity)
    (contour_resolvent hyp hr hr2 n u hq)

lemma res_isRes (hyp : FreeResolventHyp L κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) {z : ℂ} (hz : z ∈ sphere (center L n) r) :
    IsResolvent L κ (u : ℝ → ℂ) (parity n) z (resolvent L κ (u : ℝ → ℂ) (parity n) z) := by
  obtain ⟨R, hR, -⟩ := contour_resolvent hyp hr hr2 n u hq z hz
  rw [resolvent_eq hR]; exact hR

/-- Generic inner-product formula for `(2πi)⁻¹∮F(z) dz`, `F` continuous on the circle. -/
lemma inner_circle {c : ℂ} (F : ℂ → H2 L →L[ℂ] H2 L) (hr : 0 ≤ r) (hF : ContinuousOn F (sphere c r))
    (φ ψ : H2 L) :
    ⟪φ, (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral F c r) ψ⟫_ℂ =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(c, r), ⟪φ, F z ψ⟫_ℂ := by
  have hFi : CircleIntegrable F c r := hF.circleIntegrable hr
  have hFv : CircleIntegrable (fun z => F z ψ) c r :=
    (hF.clm_apply continuousOn_const).circleIntegrable hr
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, QuantumNLS.Local002Free.circleIntegral_apply _ hFi ψ]
  congr 1
  have := clm_circleIntegral (innerSL ℂ φ) hFv
  simpa only [innerSL_apply_apply] using this

lemma proj_unfold (n : ℤ) (u : ℝ → ℂ) :
    perturbedProj L κ u n r = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
      circleIntegral (fun z => resolvent L κ u (parity n) z) (center L n) r := rfl

/-- **`P_n(u)` is self-adjoint.** -/
theorem proj_symm (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) (φ ψ : H2 L) :
    ⟪perturbedProj L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ = ⟪φ, perturbedProj L κ (u : ℝ → ℂ) n r ψ⟫_ℂ := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  have hrel : ∀ z ∈ sphere (center L n) r, ∀ φ ψ : H2 L,
      ⟪resolvent L κ (u : ℝ → ℂ) (parity n) z φ, ψ⟫_ℂ =
        ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) (conj z) ψ⟫_ℂ := by
    intro z hz φ ψ
    obtain ⟨Rz, hRz, -⟩ := contour_resolvent hyp hr hr2 n u hq z hz
    obtain ⟨Rc, hRc, -⟩ := contour_resolvent hyp hr hr2 n u hq (conj z) (sphere_conj hz)
    rw [resolvent_eq hRz, resolvent_eq hRc]
    exact resolvent_adjoint_rel (fun p hp q hq' => graph_symm hL hr hr2 n _ hp hq') hRz
      (by simpa using hRc) φ ψ
  let a : ℝ := pm L n
  let f : H2 L → H2 L → ℂ → ℂ := fun φ ψ z => ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) z ψ⟫_ℂ
  have hfc : ∀ φ ψ : H2 L, ContinuousOn (f φ ψ) (sphere ((a : ℂ)) r) := by
    intro φ ψ
    have hc : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (sphere ((a : ℂ)) r) := hcont
    exact ContinuousOn.inner continuousOn_const (hc.clm_apply continuousOn_const)
  let J : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hJapply : ∀ w : ℂ, J w = conj w := fun w => rfl
  have hJ : ∀ z x : ℂ, J (z • x) = conj z • J x := fun z x => by simp [hJapply]
  have hkey := circle_swap_normalized J hJ (fun z => f ψ φ z • ContinuousLinearMap.id ℂ ℂ)
    (fun z => f φ ψ z • ContinuousLinearMap.id ℂ ℂ) a r hr.le
    (((hfc ψ φ).smul continuousOn_const).circleIntegrable hr.le)
    (((hfc φ ψ).smul continuousOn_const).circleIntegrable hr.le) (by
      intro z hz x
      have hz' : z ∈ sphere (center L n) r := hz
      have h1 := hrel (conj z) (sphere_conj hz') φ ψ
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, f, hJapply]
      have e1 : conj ⟪ψ, resolvent L κ (u : ℝ → ℂ) (parity n) (conj z) φ⟫_ℂ =
          ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) z ψ⟫_ℂ := by
        rw [inner_conj_symm, h1, Complex.conj_conj]
      rw [map_mul, e1]) 1
  have hG := apply_one_circle (c := (a : ℂ)) hr.le (hfc φ ψ)
  have hF := apply_one_circle (c := (a : ℂ)) hr.le (hfc ψ φ)
  have hJ1 : J 1 = 1 := by simp [hJapply]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hJ1, hG, hF] at hkey
  have e1 := inner_circle (c := ((a : ℝ) : ℂ)) (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) hr.le hcont φ ψ
  have e2 := inner_circle (c := ((a : ℝ) : ℂ)) (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) hr.le hcont ψ φ
  have p1 : ∀ x y : H2 L, ⟪x, perturbedProj L κ (u : ℝ → ℂ) n r y⟫_ℂ = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) *
      ∮ z in C(((a : ℝ) : ℂ), r), f x y z := fun x y => by
    rw [proj_unfold]; exact inner_circle (c := ((a : ℝ) : ℂ)) (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) hr.le hcont x y
  calc ⟪perturbedProj L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ
      = conj ⟪ψ, perturbedProj L κ (u : ℝ → ℂ) n r φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f ψ φ z) := by rw [p1]
    _ = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f φ ψ z := by
        simpa [hJapply, smul_eq_mul] using hkey.symm
    _ = _ := (p1 φ ψ).symm

end QuantumNLS.Local003Proj
#print axioms QuantumNLS.Local003Proj.proj_symm
