import Mathlib
import QuantumNLS.Local002Discharge
import QuantumNLS.TerraMultiRound25Contour
import QuantumNLS.TerraMultiRound27Ball
import QuantumNLS.TerraMultiRound27SwapBall

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage S1: Hermiticity of the actual
dressed contour integral and of the actual reduced map `reducedMatrix2`, and the matrix form `[[a, b̄],[b, a]]`.

Source (proof, line 106): "Hence `B_n` is Hermitian and commutes with `(z₁,z₂) ↦ (z̄₂,z̄₁)`.  A direct calculation gives the
displayed matrix form."

* `graph_symm`: `𝓛_u` is symmetric on `LuGraph` (Local002SA `Gu_symm`, with the free resolvents at `p_n ± i r` supplied by
  the PROVED LOCAL-001 `Local002Discharge.free_resolvent_hyp`, so no hypothesis).
* `resolvent_adjoint_rel`: `⟪R_z φ, ψ⟫ = ⟪φ, R_{z̄} ψ⟫` for the perturbed resolvents (also at the two real points).
* `dressedIntegral_symm`: `D = (2πi)⁻¹∮(z-p_n)(z-𝓛_u)⁻¹dz` is Hermitian (the contour is conjugation symmetric; the
  orientation sign is cancelled by `conj (2πi)⁻¹ = -(2πi)⁻¹`, via Terra's `Round24.circle_swap_normalized` with `J = conj` on `ℂ`).
* `reducedMatrix2_hermitian`, and `reducedMatrix_form`: with the swap symmetry (Terra r27, read-only) the entries are
  `a = B₀₀ ∈ ℝ`, `b = B₁₀`, `B₀₁ = b̄`, `B₁₁ = a`, on the explicit uniform ball `‖u‖ < compressionRadius κ L r`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Hermitian
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Circle
open QuantumNLS.LocalSpectral.Round23 QuantumNLS.LocalSpectral.Round24 QuantumNLS.LocalSpectral.Round25
  QuantumNLS.LocalSpectral.Round27

variable {L κ r : ℝ}

/-- `⟪p₁, q₂⟫ = ⟪p₂, q₁⟫` on the graph of `𝓛_u` (symmetry), for any potential `u`. -/
lemma graph_symm (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : ℝ → ℂ)
    {p q : H2 L × H2 L} (hp : p ∈ LuGraph L κ u (parity n)) (hq : q ∈ LuGraph L κ u (parity n)) :
    ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = (pm L n : ℂ) + (r : ℂ) * Complex.I := ⟨_, rfl⟩
  have hz : ‖z - (pm L n : ℂ)‖ = r := by rw [hzdef]; simp [abs_of_pos hr]
  have hzc : ‖conj z - (pm L n : ℂ)‖ = r := by
    have : conj z - (pm L n : ℂ) = conj (z - (pm L n : ℂ)) := by simp [Complex.conj_ofReal]
    rw [this, RCLike.norm_conj, hz]
  have him : z.im ≠ 0 := by rw [hzdef]; simpa using hr.ne'
  obtain ⟨R0, hR0, -⟩ := hyp.res r n z hr hr2 hz
  obtain ⟨R0', hR0', -⟩ := hyp.res r n (conj z) hr hr2 hzc
  exact Gu_symm hL him hR0 hR0' hp hq

/-- Perturbed resolvents: `⟪R_z φ, ψ⟫ = ⟪φ, R_{z̄} ψ⟫`. -/
lemma resolvent_adjoint_rel {u : ℝ → ℂ} {σ : ℤˣ} {z : ℂ} {R R' : H2 L →L[ℂ] H2 L}
    (hsym : ∀ p ∈ LuGraph L κ u σ, ∀ q ∈ LuGraph L κ u σ, ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ)
    (hR : IsResolvent L κ u σ z R) (hR' : IsResolvent L κ u σ (conj z) R') (φ ψ : H2 L) :
    ⟪R φ, ψ⟫_ℂ = ⟪φ, R' ψ⟫_ℂ := by
  have h := hsym _ (hR.1 φ) _ (hR'.1 ψ)
  simp only at h
  rw [inner_sub_right, inner_smul_right, inner_sub_left, inner_smul_left] at h
  linear_combination -h

lemma center_eq (n : ℤ) : center L n = ((pm L n : ℝ) : ℂ) := rfl

lemma sphere_conj {n : ℤ} {z : ℂ} (hz : z ∈ sphere (center L n) r) : conj z ∈ sphere (center L n) r := by
  rw [mem_sphere_iff_norm] at hz ⊢
  change ‖conj z - (pm L n : ℂ)‖ = r
  change ‖z - (pm L n : ℂ)‖ = r at hz
  rw [← Complex.conj_ofReal (pm L n), ← map_sub, Complex.norm_conj]
  exact hz

/-- The scalar kernel `z ↦ (z - p_n) ⟪φ, R(z) ψ⟫` and `⟪φ, D ψ⟫` as a scalar contour integral. -/
lemma inner_dressed (hyp : FreeResolventHyp L κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) (φ ψ : H2 L) :
    ⟪φ, dressedIntegral L κ (u : ℝ → ℂ) n r ψ⟫_ℂ =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) *
        ∮ z in C(((pm L n : ℝ) : ℂ), r), (z - (pm L n : ℂ)) *
          ⟪φ, resolvent L κ (u : ℝ → ℂ) (parity n) z ψ⟫_ℂ := by
  have hpos : 0 < 1 - qpar κ L r u := by linarith
  have hcont : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (sphere (center L n) r) :=
    continuousOn_resolvent _ (M := r⁻¹ * (1 - qpar κ L r u)⁻¹) (by positivity)
      (contour_resolvent hyp hr hr2 n u hq)
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

lemma apply_one_circle {c : ℂ} {g : ℂ → ℂ} (hr : 0 ≤ r) (hg : ContinuousOn g (sphere c r)) :
    (circleIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) c r) 1 = ∮ z in C(c, r), g z := by
  have hF : CircleIntegrable (fun z => g z • ContinuousLinearMap.id ℂ ℂ) c r :=
    (hg.smul continuousOn_const).circleIntegrable hr
  have := clm_circleIntegral (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) hF
  simpa using this

/-- **The dressed contour integral is Hermitian.** -/
theorem dressedIntegral_symm (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) (φ ψ : H2 L) :
    ⟪dressedIntegral L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ = ⟪φ, dressedIntegral L κ (u : ℝ → ℂ) n r ψ⟫_ℂ := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hpos : 0 < 1 - qpar κ L r u := by linarith
  have hcont : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (sphere (center L n) r) :=
    continuousOn_resolvent _ (M := r⁻¹ * (1 - qpar κ L r u)⁻¹) (by positivity)
      (contour_resolvent hyp hr hr2 n u hq)
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
      have h2 := hrel z hz' ψ φ
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
  have e1 := inner_dressed hyp hr hr2 n u hq φ ψ
  have e2 := inner_dressed hyp hr hr2 n u hq ψ φ
  calc ⟪dressedIntegral L κ (u : ℝ → ℂ) n r φ, ψ⟫_ℂ
      = conj ⟪ψ, dressedIntegral L κ (u : ℝ → ℂ) n r φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f ψ φ z) := by rw [e2]
    _ = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(((a : ℝ) : ℂ), r), f φ ψ z := by
        simpa [hJapply, smul_eq_mul] using hkey.symm
    _ = _ := e1.symm

/-- **The actual reduced map `B_n` is Hermitian.** -/
theorem reducedMatrix2_hermitian (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) (h : SmallCompression L κ (u : ℝ → ℂ) n r)
    (v w : E2) :
    ⟪reducedMatrix2 L κ (u : ℝ → ℂ) n r h v, w⟫_ℂ = ⟪v, reducedMatrix2 L κ (u : ℝ → ℂ) n r h w⟫_ℂ := by
  unfold reducedMatrix2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    dressedIntegral_symm hL hr hr2 n u hq]

/-- **Matrix form `B_n = [[a, b̄],[b, a]]`** (`a ∈ ℝ`) on the explicit uniform ball, from Hermiticity and the swap
symmetry (Terra r27). -/
theorem reducedMatrix_form (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hu : ‖u‖ < compressionRadius κ L r)
    (h : SmallCompression L κ (u : ℝ → ℂ) n r) :
    ∃ (a : ℝ) (b : ℂ), ∀ v : E2, reducedMatrix2 L κ (u : ℝ → ℂ) n r h v =
      vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1) := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hq : qpar κ L r u < 1 := by
    have := qpar_lt_half_of_norm_lt_radius u hu
    linarith
  set B := reducedMatrix2 L κ (u : ℝ → ℂ) n r h with hB
  have hsw : ∀ v : E2, B (swapConj v) = swapConj (B v) := fun v =>
    reducedMatrix_swap_on_ball hL hyp hr hr2 u hu n v
  have hherm := reducedMatrix2_hermitian hL hr hr2 n u hq h
  let e0 : E2 := vec2 1 0
  let e1 : E2 := vec2 0 1
  have hs0 : swapConj e0 = e1 := by ext i; fin_cases i <;> simp [swapConj, e0, e1, vec2]
  have hs1 : swapConj e1 = e0 := by ext i; fin_cases i <;> simp [swapConj, e0, e1, vec2]
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

end QuantumNLS.Local003Hermitian
#print axioms QuantumNLS.Local003Hermitian.dressedIntegral_symm
#print axioms QuantumNLS.Local003Hermitian.reducedMatrix2_hermitian
#print axioms QuantumNLS.Local003Hermitian.reducedMatrix_form
