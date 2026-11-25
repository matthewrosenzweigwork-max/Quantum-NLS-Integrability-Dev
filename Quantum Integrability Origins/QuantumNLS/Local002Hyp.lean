import Mathlib
import QuantumNLS.Local002Neumann

/-! LOCAL-002 `lem:reset-analytic-projections` (spectral_reduction.tex:57), stage B: the contour
estimate `‖P_n(u) - P_n(0)‖ ≤ q/(1-q)` and the resolvent set, from LOCAL-001 as ONE explicit named
hypothesis.

`FreeResolventHyp L κ` records the printed `lem:reset-free-resolvent` (spectral_reduction.tex:36-50),
for every `0 < r < d/2 = 2π/L` and every `Γ_n = {|z - p_n| = r}` in parity `(-1)^n`: the free
resolvent `R_{0,n}(z) = (z - 𝓛_0)^{-1}` (an `IsResolvent` of `𝓛_0` on `D_{(-1)^n}`) exists with
* `‖R_{0,n}(z)‖ ≤ 1/r`,
* `‖R_{0,n}(z) f‖_{L^∞(ℂ²)} ≤ C_{L,r} ‖f‖₂`  (almost-everywhere bound),
* `‖V_u R_{0,n}(z)‖_{2→2} ≤ 2√κ C_{L,r} ‖u‖₂` (stated as: `V_u R_{0,n}(z) f ∈ L²`, with that norm bound),
`C_{L,r}² = L⁻¹ (r⁻² + 2 Σ_{k≥1} (dk - r)⁻²)`, `d = 4π/L`. Nothing from LOCAL-001's proof is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002
open QuantumNLS.LocalSpectral

variable {L κ : ℝ}

/-- `C_{L,r}` of the printed lemma. -/
def Cconst (L r : ℝ) : ℝ :=
  Real.sqrt (L⁻¹ * (r⁻¹ ^ 2 + 2 * ∑' k : ℕ, ((4 * Real.pi / L) * ((k : ℝ) + 1) - r)⁻¹ ^ 2))

lemma Cconst_nonneg (L r : ℝ) : 0 ≤ Cconst L r := Real.sqrt_nonneg _

/-- **LOCAL-001 (`lem:reset-free-resolvent`) as one explicit named hypothesis.** -/
structure FreeResolventHyp (L κ : ℝ) : Prop where
  res : ∀ (r : ℝ) (n : ℤ) (z : ℂ), 0 < r → r < 2 * Real.pi / L → ‖z - (pm L n : ℂ)‖ = r →
    ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r
  sup : ∀ (r : ℝ) (n : ℤ) (z : ℂ) (R : H2 L →L[ℂ] H2 L), 0 < r → r < 2 * Real.pi / L →
    ‖z - (pm L n : ℂ)‖ = r → IsResolvent L κ (fun _ => 0) (parity n) z R → ∀ φ : H2 L,
      ∀ᵐ x ∂(μI L), ‖(R φ : ℝ → E2) x‖ ≤ Cconst L r * ‖φ‖
  pot : ∀ (r : ℝ) (n : ℤ) (z : ℂ) (R : H2 L →L[ℂ] H2 L), 0 < r → r < 2 * Real.pi / L →
    ‖z - (pm L n : ℂ)‖ = r → IsResolvent L κ (fun _ => 0) (parity n) z R →
      ∀ (u : Lp ℂ 2 (μI L)) (φ : H2 L),
        ∃ hm : MemLp (fun x => Vpt κ ((u : ℝ → ℂ) x) ((R φ : ℝ → E2) x)) 2 (μI L),
          ‖hm.toLp _‖ ≤ 2 * Real.sqrt κ * Cconst L r * ‖u‖ * ‖φ‖

lemma Vpt_add (κ : ℝ) (w : ℂ) (g g' : E2) : Vpt κ w (g + g') = Vpt κ w g + Vpt κ w g' := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2] <;> ring

lemma Vpt_smul (κ : ℝ) (w : ℂ) (c : ℂ) (g : E2) : Vpt κ w (c • g) = c • Vpt κ w g := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2] <;> ring

/-- The multiplication operator `T = V_u R0` as a bounded operator. -/
lemma exists_T (R : H2 L →L[ℂ] H2 L) (u : ℝ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ φ : H2 L, ∃ hm : MemLp (fun x => Vpt κ (u x) ((R φ : ℝ → E2) x)) 2 (μI L),
      ‖hm.toLp _‖ ≤ K * ‖φ‖) :
    ∃ T : H2 L →L[ℂ] H2 L, ‖T‖ ≤ K ∧
      ∀ φ, (T φ : ℝ → E2) =ᵐ[μI L] fun x => Vpt κ (u x) ((R φ : ℝ → E2) x) := by
  choose hm hb using h
  let f : H2 L →ₗ[ℂ] H2 L :=
    { toFun := fun φ => (hm φ).toLp _
      map_add' := fun φ ψ => by
        show (hm (φ + ψ)).toLp _ = (hm φ).toLp _ + (hm ψ).toLp _
        apply Lp.ext
        have h4 : ((R (φ + ψ) : H2 L) : ℝ → E2) =ᵐ[μI L]
            fun x => (R φ : ℝ → E2) x + (R ψ : ℝ → E2) x := by
          rw [map_add]; exact Lp.coeFn_add _ _
        filter_upwards [(hm (φ + ψ)).coeFn_toLp, (hm φ).coeFn_toLp, (hm ψ).coeFn_toLp, h4,
          Lp.coeFn_add ((hm φ).toLp _) ((hm ψ).toLp _)] with x a1 a2 a3 a4 a5
        rw [a5, Pi.add_apply, a1, a2, a3, a4, Vpt_add]
      map_smul' := fun c φ => by
        show (hm (c • φ)).toLp _ = c • (hm φ).toLp _
        apply Lp.ext
        have h4 : ((R (c • φ) : H2 L) : ℝ → E2) =ᵐ[μI L] fun x => c • (R φ : ℝ → E2) x := by
          rw [map_smul]; exact Lp.coeFn_smul _ _
        filter_upwards [(hm (c • φ)).coeFn_toLp, (hm φ).coeFn_toLp, h4,
          Lp.coeFn_smul c ((hm φ).toLp _)] with x a1 a2 a4 a5
        rw [a5, Pi.smul_apply, a1, a2, a4, Vpt_smul] }
  refine ⟨LinearMap.mkContinuous f K (fun φ => hb φ), ?_, fun φ => ?_⟩
  · exact LinearMap.mkContinuous_norm_le f hK (fun φ => hb φ)
  · exact (hm φ).coeFn_toLp

/-! ### Resolvent identities and uniqueness -/

lemma resolvent_eq {u : ℝ → ℂ} {σ : ℤˣ} {z : ℂ} {R : H2 L →L[ℂ] H2 L}
    (h : IsResolvent L κ u σ z R) : QuantumNLS.LocalSpectral.resolvent L κ u σ z = R := by
  classical
  unfold QuantumNLS.LocalSpectral.resolvent
  rw [dif_pos ⟨R, h⟩]
  exact IsResolvent.unique (Classical.choose_spec (⟨R, h⟩ : ∃ R, IsResolvent L κ u σ z R)) h

/-- The resolvent identity `R_z - R_w = (w - z) R_z R_w`. -/
lemma resolvent_identity {u : ℝ → ℂ} {σ : ℤˣ} {z w : ℂ} {Rz Rw : H2 L →L[ℂ] H2 L}
    (hz : IsResolvent L κ u σ z Rz) (hw : IsResolvent L κ u σ w Rw) :
    Rz - Rw = (w - z) • (Rz * Rw) := by
  ext1 φ
  have h1 := hz.2 (Rw φ, w • Rw φ - φ) (hw.1 φ)
  simp only at h1
  have h2 : z • Rw φ - (w • Rw φ - φ) = (z - w) • Rw φ + φ := by
    rw [sub_smul]; abel
  rw [h2, map_add, map_smul] at h1
  simp only [sub_apply, smul_apply]
  have h3 : Rw φ - Rz φ = (z - w) • Rz (Rw φ) := sub_eq_of_eq_add h1.symm
  rw [← neg_sub, h3, ← neg_smul, neg_sub]
  rfl

lemma continuousOn_resolvent {u : ℝ → ℂ} {σ : ℤˣ} (S : Set ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ S, ∃ R, IsResolvent L κ u σ z R ∧ ‖R‖ ≤ M) :
    ContinuousOn (fun z => QuantumNLS.LocalSpectral.resolvent L κ u σ z) S := by
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (M * M)) ?_).continuousOn
  intro z hz w hw
  obtain ⟨Rz, hRz, hz'⟩ := hM z hz
  obtain ⟨Rw, hRw, hw'⟩ := hM w hw
  simp only [resolvent_eq hRz, resolvent_eq hRw, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hM0 hM0)]
  rw [resolvent_identity hRz hRw, norm_smul]
  calc ‖w - z‖ * ‖Rz * Rw‖ ≤ ‖w - z‖ * (‖Rz‖ * ‖Rw‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖w - z‖ * (M * M) := by gcongr
    _ = M * M * ‖z - w‖ := by rw [norm_sub_rev]; ring

/-! ### The perturbed resolvent on `Γ_n` and the projection estimate -/

/-- The common small parameter `q = 2 √κ C_{L,r} ‖u‖₂`. -/
def qpar (κ L r : ℝ) (u : Lp ℂ 2 (μI L)) : ℝ := 2 * Real.sqrt κ * Cconst L r * ‖u‖

lemma qpar_nonneg (κ L r : ℝ) (u : Lp ℂ 2 (μI L)) : 0 ≤ qpar κ L r u := by
  unfold qpar
  have := Cconst_nonneg L r
  positivity

theorem perturbed_resolvent (hyp : FreeResolventHyp L κ) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) {z : ℂ} (hz : ‖z - (pm L n : ℂ)‖ = r)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) :
    ∃ R0 R : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R0 ∧
      IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧ ‖R0‖ ≤ 1 / r ∧
      ‖R‖ ≤ r⁻¹ * (1 - qpar κ L r u)⁻¹ ∧
      ‖R - R0‖ ≤ r⁻¹ * qpar κ L r u * (1 - qpar κ L r u)⁻¹ := by
  obtain ⟨R0, h0, hR0⟩ := hyp.res r n z hr hr2 hz
  have hK := qpar_nonneg κ L r u
  obtain ⟨T, hTn, hTa⟩ := exists_T (κ := κ) R0 (u : ℝ → ℂ) hK (fun φ => by
    obtain ⟨hm, hb⟩ := hyp.pot r n z R0 hr hr2 hz h0 u φ
    exact ⟨hm, by unfold qpar; exact hb⟩)
  have hT1 : ‖T‖ < 1 := lt_of_le_of_lt hTn hq
  obtain ⟨S, R, -, -, -, hR, hRn, hRd⟩ := resolvent_of_neumann h0 hTa hT1
  refine ⟨R0, R, h0, hR, hR0, ?_, ?_⟩
  · have h1 : (1 - ‖T‖)⁻¹ ≤ (1 - qpar κ L r u)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    calc ‖R‖ ≤ ‖R0‖ * (1 - ‖T‖)⁻¹ := hRn
      _ ≤ r⁻¹ * (1 - qpar κ L r u)⁻¹ := by
        have hR0' : ‖R0‖ ≤ r⁻¹ := by simpa [one_div] using hR0
        exact mul_le_mul hR0' h1 (inv_nonneg.2 (by linarith)) (inv_nonneg.2 hr.le)
  · have hpos : 0 < 1 - qpar κ L r u := by linarith
    have h1 : ‖T‖ * (1 - ‖T‖)⁻¹ ≤ qpar κ L r u * (1 - qpar κ L r u)⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) hpos]
      nlinarith [norm_nonneg T]
    calc ‖R - R0‖ ≤ ‖R0‖ * ‖T‖ * (1 - ‖T‖)⁻¹ := hRd
      _ = ‖R0‖ * (‖T‖ * (1 - ‖T‖)⁻¹) := by ring
      _ ≤ (1 / r) * (qpar κ L r u * (1 - qpar κ L r u)⁻¹) := by gcongr
      _ = r⁻¹ * qpar κ L r u * (1 - qpar κ L r u)⁻¹ := by rw [one_div]; ring

theorem proj_diff_bound (hyp : FreeResolventHyp L κ) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) :
    ‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ ≤
      qpar κ L r u / (1 - qpar κ L r u) := by
  have hK := qpar_nonneg κ L r u
  have hpos : 0 < 1 - qpar κ L r u := by linarith
  have hsph : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    simpa [QuantumNLS.LocalSpectral.center, mem_sphere_iff_norm] using hz
  have hb : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r, ∃ R0 R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R0 ∧ IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧
      ‖R0‖ ≤ 1 / r ∧ ‖R‖ ≤ r⁻¹ * (1 - qpar κ L r u)⁻¹ ∧
      ‖R - R0‖ ≤ r⁻¹ * qpar κ L r u * (1 - qpar κ L r u)⁻¹ :=
    fun z hz => perturbed_resolvent hyp hr hr2 n (hsph z hz) u hq
  have hc1 : ContinuousOn (fun z => QuantumNLS.LocalSpectral.resolvent L κ (u : ℝ → ℂ) (parity n) z)
      (sphere (QuantumNLS.LocalSpectral.center L n) r) :=
    continuousOn_resolvent _ (M := r⁻¹ * (1 - qpar κ L r u)⁻¹) (by positivity)
      (fun z hz => by
        obtain ⟨R0, R, -, hR, -, hRn, -⟩ := hb z hz
        exact ⟨R, hR, hRn⟩)
  have hc0 : ContinuousOn (fun z => QuantumNLS.LocalSpectral.resolvent L κ (fun _ => 0) (parity n) z)
      (sphere (QuantumNLS.LocalSpectral.center L n) r) :=
    continuousOn_resolvent _ (M := 1 / r) (by positivity)
      (fun z hz => by
        obtain ⟨R0, R, h0, -, h0n, -⟩ := hb z hz
        exact ⟨R0, h0, h0n⟩)
  unfold perturbedProj freeProj rieszProj
  have key := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (c := QuantumNLS.LocalSpectral.center L n)
    (R := r) (C := r⁻¹ * qpar κ L r u * (1 - qpar κ L r u)⁻¹)
    (f := fun z => QuantumNLS.LocalSpectral.resolvent L κ (u : ℝ → ℂ) (parity n) z -
      QuantumNLS.LocalSpectral.resolvent L κ (fun _ => 0) (parity n) z) hr.le
    (fun z hz => by
      obtain ⟨R0, R, h0, hR, -, -, hd⟩ := hb z hz
      simp only [resolvent_eq h0, resolvent_eq hR]
      exact hd)
  rw [circleIntegral.integral_sub (hc1.circleIntegrable hr.le) (hc0.circleIntegrable hr.le),
    smul_sub] at key
  refine key.trans (le_of_eq ?_)
  field_simp

end QuantumNLS.Local002
#print axioms QuantumNLS.Local002.proj_diff_bound
#print axioms QuantumNLS.Local002.perturbed_resolvent
