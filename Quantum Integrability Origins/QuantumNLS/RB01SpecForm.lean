import Mathlib
import QuantumNLS.RB01SpecIdem
import QuantumNLS.Local003Isometry
import QuantumNLS.TerraMultiRound27SwapBall

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-24: the LOCAL-003 operator facts re-derived under
square-smallness (arbitrary real fields, high labels) instead of the small-ball `Local003Isometry.Ctx`, and the
doublet form of RB01Matrix's `B_n` (source `collective_actions.tex:272-307`: "`B_n` is Hermitian and commutes with
`(z₁, z₂) ↦ (z̄₂, z̄₁)`", eq. `GB01-B`).

The frozen LOCAL-003 proofs use `qpar < 1` only to obtain resolvents on the contour; here they come from
`RB01Resolvent.resolvent_exists` (`hres`).  The proofs of `proj_symm'`, `dressed_symm'`, `P_Lu'`, `pair_mem'`,
`eigen_P'` follow the frozen `Local003Proj.proj_symm`, `Local003Hermitian.dressedIntegral_symm`,
`Local003Range.P_Lu`, `pair_mem`, `eigen_P` verbatim with this substitution.
* `eigen_D'`: `D f = (λ − p_n) f` for an eigenvector with `|λ − p_n| < r`;
* `proj_swap'`, `dressed_swap'` (Terra r24 `riesz_swap`, `dressed_swap`), `S_swap`, `K_swap`;
* `Bmat = S^{-1/2} K S^{-1/2}` (the RB01Matrix/RB01Bridge `B_n − p_n`), **`Bmat_form`**: `Bmat = [[a, b̄],[b, a]]`,
  `a ∈ ℝ` (Hermitian: `S`, `K` Hermitian and `star_invSqrtM`; swap: `invSqrtM_swap`; then the frozen
  `Local003Hermitian.reducedMatrix_form` argument, `form_of_herm_swap`). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantumNLS.RB01SpecForm

open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Circle
  QuantumNLS.Local003Hermitian QuantumNLS.Local003Proj QuantumNLS.Local003Range
  QuantumNLS.LocalSpectral.Round23 QuantumNLS.LocalSpectral.Round24 QuantumNLS.LocalSpectral.Round27
open QuantumNLS.RB01Resolvent (SqSmall resolvent_exists Rb Rb_nonneg selfAdjoint_of_sqSmall)

/-- A Hermitian map of `ℂ²` commuting with `swapConj` has the form `[[a, b̄],[b, a]]`, `a ∈ ℝ`. -/
theorem form_of_herm_swap (B : E2 →L[ℂ] E2) (hsw : ∀ v : E2, B (swapConj v) = swapConj (B v))
    (hherm : ∀ v w : E2, ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ) :
    ∃ (a : ℝ) (b : ℂ), ∀ v : E2, B v = vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1) := by
  let e0 : E2 := vec2 1 0
  let e1 : E2 := vec2 0 1
  have hs0 : swapConj e0 = e1 := by ext i; fin_cases i <;> simp [swapConj, e0, e1, vec2]
  have hd : conj (B e0 0) = B e0 0 := by
    have := hherm e0 e0
    simpa [PiLp.inner_apply, e0, vec2, Fin.sum_univ_two] using this
  obtain ⟨a, ha⟩ := Complex.conj_eq_iff_real.mp hd
  have hB1 : B e1 = swapConj (B e0) := by rw [← hs0]; exact hsw e0
  have h10 : B e1 0 = conj (B e0 1) := by rw [hB1]; simp [swapConj, vec2]
  have h11 : B e1 1 = (a : ℂ) := by rw [hB1]; simp [swapConj, vec2, ha]
  refine ⟨a, B e0 1, fun v => ?_⟩
  have hv : v = v 0 • e0 + v 1 • e1 := by ext i; fin_cases i <;> simp [e0, e1, vec2]
  have hBv : B v = v 0 • B e0 + v 1 • B e1 := by
    conv_lhs => rw [hv]
    simp
  have t0 := congrArg (fun w : E2 => w 0) hBv
  have t1 := congrArg (fun w : E2 => w 1) hBv
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at t0 t1
  have c0 : B v 0 = (a : ℂ) * v 0 + conj (B e0 1) * v 1 := by rw [t0, ha, h10]; ring
  have c1 : B v 1 = B e0 1 * v 0 + (a : ℂ) * v 1 := by rw [t1, h11]; ring
  ext i
  fin_cases i
  · simpa [vec2] using c0
  · simpa [vec2] using c1

variable {L κ r : ℝ} {n : ℤ} {u : Lp ℂ 2 (μI L)}

section Ops

variable (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hu : SqSmall L κ r n u)
include hL hr hr2 hu

theorem hres : ∀ z ∈ sphere (center L n) r, ∃ R : H2 L →L[ℂ] H2 L,
    IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧ ‖R‖ ≤ Rb L κ r u := by
  intro z hz
  have h : ‖z - (pm L n : ℂ)‖ = r := by simpa [LocalSpectral.center, mem_sphere_iff_norm] using hz
  exact resolvent_exists hL hr hr2 hu (by rw [h]; linarith) h.le

theorem res_cont' :
    ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (sphere (center L n) r) :=
  continuousOn_resolvent _ (Rb_nonneg L κ hr u) (hres hL hr hr2 hu)

theorem res_isRes' {z : ℂ} (hz : z ∈ sphere (center L n) r) :
    IsResolvent L κ (u : ℝ → ℂ) (parity n) z (resolvent L κ (u : ℝ → ℂ) (parity n) z) := by
  obtain ⟨R, hR, -⟩ := hres hL hr hr2 hu z hz
  rw [resolvent_eq hR]; exact hR

theorem hrel' : ∀ z ∈ sphere (center L n) r, ∀ φ ψ : H2 L,
    ⟪resolvent L κ (u : ℝ → ℂ) (parity n) z φ, ψ⟫_ℂ =
      ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) (conj z) ψ⟫_ℂ := by
  intro z hz φ ψ
  obtain ⟨Rz, hRz, -⟩ := hres hL hr hr2 hu z hz
  obtain ⟨Rc, hRc, -⟩ := hres hL hr hr2 hu (conj z) (sphere_conj hz)
  rw [resolvent_eq hRz, resolvent_eq hRc]
  exact resolvent_adjoint_rel (fun p hp q hq' => graph_symm hL hr hr2 n _ hp hq') hRz
    (by simpa using hRc) φ ψ

/-- **`P_n(u)` is self-adjoint** (square-small version of `Local003Proj.proj_symm`). -/
theorem proj_symm' (φ ψ : H2 L) :
    ⟪perturbedProj L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ = ⟪φ, perturbedProj L κ (u : ℝ → ℂ) n r ψ⟫_ℂ := by
  have hcont := res_cont' hL hr hr2 hu
  have hrel := hrel' hL hr hr2 hu
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
  have p1 : ∀ x y : H2 L, ⟪x, perturbedProj L κ (u : ℝ → ℂ) n r y⟫_ℂ = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) *
      ∮ z in C(((a : ℝ) : ℂ), r), f x y z := fun x y => by
    rw [proj_unfold]
    exact inner_circle (c := ((a : ℝ) : ℂ)) (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) hr.le hcont x y
  calc ⟪perturbedProj L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ
      = conj ⟪ψ, perturbedProj L κ (u : ℝ → ℂ) n r φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f ψ φ z) := by rw [p1]
    _ = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f φ ψ z := by
        simpa [hJapply, smul_eq_mul] using hkey.symm
    _ = _ := (p1 φ ψ).symm

theorem inner_dressed' (φ ψ : H2 L) :
    ⟪φ, dressedIntegral L κ (u : ℝ → ℂ) n r ψ⟫_ℂ =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) *
        ∮ z in C(((pm L n : ℝ) : ℂ), r), (z - (pm L n : ℂ)) *
          ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) z ψ⟫_ℂ := by
  have hcont := res_cont' hL hr hr2 hu
  have hF : CircleIntegrable (fun z => (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z)
      (center L n) r :=
    ((continuousOn_id.sub continuousOn_const).smul hcont).circleIntegrable hr.le
  have hFv : CircleIntegrable (fun z => ((z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z) ψ)
      (center L n) r := by
    have : ContinuousOn (fun z => ((z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z) ψ)
        (sphere (center L n) r) :=
      (((continuousOn_id.sub continuousOn_const).smul hcont).clm_apply continuousOn_const)
    exact this.circleIntegrable hr.le
  unfold dressedIntegral
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, QuantumNLS.Local002Free.circleIntegral_apply _ hF ψ]
  congr 1
  have := clm_circleIntegral (innerSL ℂ φ) hFv
  simp only [innerSL_apply_apply] at this
  rw [center_eq] at this ⊢
  rw [this]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul]

/-- **The dressed contour integral is Hermitian** (square-small version). -/
theorem dressed_symm' (φ ψ : H2 L) :
    ⟪dressedIntegral L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ = ⟪φ, dressedIntegral L κ (u : ℝ → ℂ) n r ψ⟫_ℂ := by
  have hcont := res_cont' hL hr hr2 hu
  have hrel := hrel' hL hr hr2 hu
  let a : ℝ := pm L n
  let f : H2 L → H2 L → ℂ → ℂ := fun φ ψ z =>
    (z - (a : ℂ)) * ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) z ψ⟫_ℂ
  have hfc : ∀ φ ψ : H2 L, ContinuousOn (f φ ψ) (sphere ((a : ℂ)) r) := by
    intro φ ψ
    have hc : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (sphere ((a : ℂ)) r) := hcont
    exact (continuousOn_id.sub continuousOn_const).mul
      (ContinuousOn.inner continuousOn_const (hc.clm_apply continuousOn_const))
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
      have e2 : conj (conj z - (a : ℂ)) = z - (a : ℂ) := by simp [Complex.conj_ofReal]
      rw [map_mul, map_mul, e1, e2]) 1
  have hG := apply_one_circle (c := (a : ℂ)) hr.le (hfc φ ψ)
  have hF := apply_one_circle (c := (a : ℂ)) hr.le (hfc ψ φ)
  have hJ1 : J 1 = 1 := by simp [hJapply]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hJ1, hG, hF] at hkey
  have e1 := inner_dressed' hL hr hr2 hu φ ψ
  have e2 := inner_dressed' hL hr hr2 hu ψ φ
  calc ⟪dressedIntegral L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ
      = conj ⟪ψ, dressedIntegral L κ (u : ℝ → ℂ) n r φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f ψ φ z) := by rw [e2]
    _ = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f φ ψ z := by
        simpa [hJapply, smul_eq_mul] using hkey.symm
    _ = _ := e1.symm

theorem P_apply' (f : H2 L) :
    perturbedProj L κ (u : ℝ → ℂ) n r f = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
      ∮ z in C(center L n, r), resolvent L κ (u : ℝ → ℂ) (parity n) z f := by
  have hcont := res_cont' hL hr hr2 hu
  unfold perturbedProj rieszProj
  rw [ContinuousLinearMap.smul_apply]
  congr 1
  exact QuantumNLS.Local002Free.circleIntegral_apply (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z)
    (hcont.circleIntegrable hr.le) f

theorem D_apply' (f : H2 L) :
    dressedIntegral L κ (u : ℝ → ℂ) n r f = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
      ∮ z in C(center L n, r), (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z f := by
  have hcont := res_cont' hL hr hr2 hu
  unfold dressedIntegral
  rw [ContinuousLinearMap.smul_apply]
  congr 1
  have := QuantumNLS.Local002Free.circleIntegral_apply
    (fun z => (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z)
    (((continuousOn_id.sub continuousOn_const).smul hcont).circleIntegrable hr.le) f
  simpa only [ContinuousLinearMap.smul_apply] using this

/-- Eigenvectors inside the contour: `R(z) f = (z − λ)⁻¹ f` on the contour. -/
theorem res_eig {f : H2 L} {lam : ℂ} (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n))
    (hlam : ‖lam - center L n‖ < r) :
    ∀ z ∈ sphere (center L n) r, resolvent L κ (u : ℝ → ℂ) (parity n) z f = (z - lam)⁻¹ • f := by
  have hne : ∀ z ∈ sphere (center L n) r, z - lam ≠ 0 := by
    intro z hz hz0
    have hzr : ‖z - center L n‖ = r := mem_sphere_iff_norm.mp hz
    have : z = lam := sub_eq_zero.mp hz0
    rw [this] at hzr
    linarith
  intro z hz
  have := (res_isRes' hL hr hr2 hu hz).2 (f, lam • f) hf
  simp only at this
  rw [← sub_smul, map_smul] at this
  calc resolvent L κ (u : ℝ → ℂ) (parity n) z f
      = (z - lam)⁻¹ • ((z - lam) • resolvent L κ (u : ℝ → ℂ) (parity n) z f) := by
        rw [smul_smul, inv_mul_cancel₀ (hne z hz), one_smul]
    _ = (z - lam)⁻¹ • f := by rw [this]

/-- An eigenvector with eigenvalue inside the contour satisfies `P f = f`. -/
theorem eigen_P' {f : H2 L} {lam : ℂ} (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n))
    (hlam : ‖lam - center L n‖ < r) : perturbedProj L κ (u : ℝ → ℂ) n r f = f := by
  have hpt := res_eig hL hr hr2 hu hf hlam
  have hball : lam ∈ ball (center L n) r := mem_ball_iff_norm.mpr hlam
  have hcau := circleIntegral.integral_sub_inv_of_mem_ball hball
  rw [P_apply' hL hr hr2 hu, circleIntegral.integral_congr hr.le (fun z hz => hpt z hz),
    circleIntegral.integral_smul_const, hcau, smul_smul]
  have h2 : ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * (2 * Real.pi * Complex.I) = 1 :=
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  rw [h2, one_smul]

/-- An eigenvector with eigenvalue inside the contour satisfies `D f = (λ − p_n) f`. -/
theorem eigen_D' {f : H2 L} {lam : ℂ} (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n))
    (hlam : ‖lam - center L n‖ < r) :
    dressedIntegral L κ (u : ℝ → ℂ) n r f = (lam - center L n) • f := by
  have hpt := res_eig hL hr hr2 hu hf hlam
  have hball : lam ∈ ball (center L n) r := mem_ball_iff_norm.mpr hlam
  have hcau := QuantumNLS.RB01SpecIdem.weight_cauchy hball
  have hpt' : ∀ z ∈ sphere (center L n) r, (z - center L n) • resolvent L κ (u : ℝ → ℂ) (parity n) z f =
      ((z - center L n) * (z - lam)⁻¹) • f := by
    intro z hz; rw [hpt z hz, smul_smul]
  rw [D_apply' hL hr hr2 hu, circleIntegral.integral_congr hr.le hpt', circleIntegral.integral_smul_const, hcau,
    smul_smul]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_mul]

/-- `P φ = D g + p_n P g` on the graph. -/
theorem P_Lu' {g φ : H2 L} (hp : (g, φ) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n)) :
    perturbedProj L κ (u : ℝ → ℂ) n r φ =
      dressedIntegral L κ (u : ℝ → ℂ) n r g + (pm L n : ℂ) • perturbedProj L κ (u : ℝ → ℂ) n r g := by
  have hcont := res_cont' hL hr hr2 hu
  have hpt : ∀ z ∈ sphere (center L n) r, resolvent L κ (u : ℝ → ℂ) (parity n) z φ =
      z • resolvent L κ (u : ℝ → ℂ) (parity n) z g - g := by
    intro z hz
    have := (res_isRes' hL hr hr2 hu hz).2 (g, φ) hp
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
  rw [P_apply' hL hr hr2 hu, D_apply' hL hr hr2 hu, P_apply' hL hr hr2 hu g]
  have hcen : (pm L n : ℂ) = center L n := rfl
  rw [hcen, circleIntegral.integral_congr hr.le (fun z hz => hpt z hz), circleIntegral.integral_sub i2 igc,
    hg0, sub_zero, hsplit, smul_add, smul_comm (center L n)]

/-- **`ran P ⊂ 𝓓_σ` with `𝓛_u P f = D f + p_n P f`.** -/
theorem pair_mem' (f : H2 L) :
    (perturbedProj L κ (u : ℝ → ℂ) n r f,
      dressedIntegral L κ (u : ℝ → ℂ) n r f + (pm L n : ℂ) • perturbedProj L κ (u : ℝ → ℂ) n r f) ∈
        LuGraph L κ (u : ℝ → ℂ) (parity n) := by
  have hSA := selfAdjoint_of_sqSmall hL hr hr2 hu
  rw [hSA.eq]
  intro p hp
  have h1 := P_Lu' hL hr hr2 hu hp
  simp only [inner_add_left, inner_smul_left, Complex.conj_ofReal]
  rw [proj_symm' hL hr hr2 hu f p.2, h1, inner_add_right, inner_smul_right,
    ← dressed_symm' hL hr hr2 hu f p.1, ← proj_symm' hL hr hr2 hu f p.1]

/-! ### Swap symmetry -/

theorem swap_hyp : ∀ z ∈ Metric.sphere (center L n) r,
    (∃ R, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R) ∧
      (∃ S, IsResolvent L κ (u : ℝ → ℂ) (parity n) (conj z) S) := by
  intro z hz
  obtain ⟨R, hR, -⟩ := hres hL hr hr2 hu z hz
  obtain ⟨S, hS, -⟩ := hres hL hr hr2 hu (conj z) (sphere_conj hz)
  exact ⟨⟨R, hR⟩, ⟨S, hS⟩⟩

theorem S_swap (v : E2) :
    compressionMatrix L κ (u : ℝ → ℂ) n r (swapConj v) = swapConj (compressionMatrix L κ (u : ℝ → ℂ) n r v) := by
  change (ContinuousLinearMap.adjoint (embed L n))
      (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n (swapConj v))) =
    swapConj ((ContinuousLinearMap.adjoint (embed L n))
      (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n v)))
  rw [← embed_swap]
  change (ContinuousLinearMap.adjoint (embed L n))
      (rieszProj L κ (u : ℝ → ℂ) (parity n) n r (swapOp L (embed L n v))) = _
  rw [riesz_swap L κ (u : ℝ → ℂ) (parity n) n r hr.le (swap_hyp hL hr hr2 hu)
    ((res_cont' hL hr hr2 hu).circleIntegrable hr.le), adjoint_embed_swap]
  rfl

/-- `K = E^* D E`. -/
def Kmat (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] E2 :=
  ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ u n r ∘L embed L n

theorem K_swap (v : E2) :
    Kmat L κ (u : ℝ → ℂ) n r (swapConj v) = swapConj (Kmat L κ (u : ℝ → ℂ) n r v) := by
  change (ContinuousLinearMap.adjoint (embed L n))
      (dressedIntegral L κ (u : ℝ → ℂ) n r (embed L n (swapConj v))) =
    swapConj ((ContinuousLinearMap.adjoint (embed L n))
      (dressedIntegral L κ (u : ℝ → ℂ) n r (embed L n v)))
  rw [← embed_swap]
  change (ContinuousLinearMap.adjoint (embed L n))
      (dressedIntegral L κ (u : ℝ → ℂ) n r (swapOp L (embed L n v))) = _
  rw [dressed_swap L κ (u : ℝ → ℂ) n r hr.le (swap_hyp hL hr hr2 hu)
    ((res_cont' hL hr hr2 hu).circleIntegrable hr.le), adjoint_embed_swap]

/-! ### The doublet form of `B_n − p_n = S^{-1/2} K S^{-1/2}` -/

/-- RB01Matrix's `B_n − p_n`. -/
def Bmat (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] E2 :=
  invSqrtM (compressionMatrix L κ u n r) * Kmat L κ u n r * invSqrtM (compressionMatrix L κ u n r)

theorem S_adj : ContinuousLinearMap.adjoint (compressionMatrix L κ (u : ℝ → ℂ) n r) =
    compressionMatrix L κ (u : ℝ → ℂ) n r := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  change ⟪(ContinuousLinearMap.adjoint (embed L n)) (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n v)), w⟫_ℂ =
    ⟪v, (ContinuousLinearMap.adjoint (embed L n)) (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n w))⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, proj_symm' hL hr hr2 hu]

theorem K_adj : ContinuousLinearMap.adjoint (Kmat L κ (u : ℝ → ℂ) n r) = Kmat L κ (u : ℝ → ℂ) n r := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  change ⟪(ContinuousLinearMap.adjoint (embed L n)) (dressedIntegral L κ (u : ℝ → ℂ) n r (embed L n v)), w⟫_ℂ =
    ⟪v, (ContinuousLinearMap.adjoint (embed L n)) (dressedIntegral L κ (u : ℝ → ℂ) n r (embed L n w))⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, dressed_symm' hL hr hr2 hu]

theorem Bmat_herm (hS : ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1) (v w : E2) :
    ⟪Bmat L κ (u : ℝ → ℂ) n r v, w⟫_ℂ = ⟪v, Bmat L κ (u : ℝ → ℂ) n r w⟫_ℂ := by
  have hI : ContinuousLinearMap.adjoint (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) =
      invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, QuantumNLS.Local003Isometry.star_invSqrtM hS,
      ContinuousLinearMap.star_eq_adjoint, S_adj hL hr hr2 hu]
  have hB : ContinuousLinearMap.adjoint (Bmat L κ (u : ℝ → ℂ) n r) = Bmat L κ (u : ℝ → ℂ) n r := by
    unfold Bmat
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, hI, K_adj hL hr hr2 hu]
    rfl
  rw [← ContinuousLinearMap.adjoint_inner_right, hB]

theorem Bmat_swap (hS : ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1) (v : E2) :
    Bmat L κ (u : ℝ → ℂ) n r (swapConj v) = swapConj (Bmat L κ (u : ℝ → ℂ) n r v) := by
  have hI := invSqrtM_swap (compressionMatrix L κ (u : ℝ → ℂ) n r) hS (S_swap hL hr hr2 hu)
  unfold Bmat
  simp only [ContinuousLinearMap.mul_apply]
  rw [hI, K_swap hL hr hr2 hu, hI]

/-- **Doublet form** `B_n − p_n = [[a, b̄],[b, a]]`, `a ∈ ℝ`, on arbitrary real fields at square-small labels. -/
theorem Bmat_form (hS : ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1) :
    ∃ (a : ℝ) (b : ℂ), ∀ v : E2,
      Bmat L κ (u : ℝ → ℂ) n r v = vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1) :=
  form_of_herm_swap _ (Bmat_swap hL hr hr2 hu hS) (Bmat_herm hL hr hr2 hu hS)

end Ops

end QuantumNLS.RB01SpecForm

#print axioms QuantumNLS.RB01SpecForm.proj_symm'
#print axioms QuantumNLS.RB01SpecForm.dressed_symm'
#print axioms QuantumNLS.RB01SpecForm.pair_mem'
#print axioms QuantumNLS.RB01SpecForm.eigen_P'
#print axioms QuantumNLS.RB01SpecForm.eigen_D'
#print axioms QuantumNLS.RB01SpecForm.Bmat_form
