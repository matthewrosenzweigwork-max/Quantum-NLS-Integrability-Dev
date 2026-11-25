import Mathlib
import QuantumNLS.Local002Free
import QuantumNLS.Local002Hyp
import QuantumNLS.Local002Neumann
import QuantumNLS.Local002Basis

/-! LOCAL-002 stage G: self-adjointness of `𝓛_u` on `D_{(-1)^n}` (frozen DEF-049 graph encoding).

`IsSelfAdjointGraph G`: the domain is dense and `G` equals its adjoint graph
`{(g,ψ) : ∀ (f,φ) ∈ G, ⟨g,φ⟩ = ⟨ψ,f⟩}`.  Route (no `H¹` integration by parts): symmetric from the free
resolvent symmetry (`Local002Free.free_symm`) plus the pointwise Hermitian property of `V_u`;
the adjoint graph is contained in `G` by the two Neumann resolvents at `z = p_n + i r` and `z̄`;
the domain contains the range of `R_u(z) = R_0 (1-T)^{-1}`, which contains every `χ_{m,j}`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002SA
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Basis

variable {L κ : ℝ}

/-- Domain of a graph. -/
def domOf (G : Set (H2 L × H2 L)) : Set (H2 L) := {f | ∃ φ, (f, φ) ∈ G}

/-- Adjoint graph. -/
def adjGraph (G : Set (H2 L × H2 L)) : Set (H2 L × H2 L) :=
  {q | ∀ p ∈ G, ⟪q.1, p.2⟫_ℂ = ⟪q.2, p.1⟫_ℂ}

/-- The graph `G` is that of a self-adjoint operator. -/
structure IsSelfAdjointGraph (G : Set (H2 L × H2 L)) : Prop where
  dense : Dense (domOf G)
  eq : G = adjGraph G

lemma adj_subset {G : Set (H2 L × H2 L)}
    (hsym : ∀ p ∈ G, ∀ q ∈ G, ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ) {z : ℂ} (R R' : H2 L →L[ℂ] H2 L)
    (hR : ∀ y, (R y, z • R y - y) ∈ G) (hR' : ∀ w, (R' w, conj z • R' w - w) ∈ G) :
    adjGraph G ⊆ G := by
  rintro ⟨g, ψ⟩ hq
  have hq' : ∀ p ∈ G, ⟪g, p.2⟫_ℂ = ⟪ψ, p.1⟫_ℂ := hq
  obtain ⟨w, hw⟩ : ∃ w, w = conj z • g - ψ := ⟨_, rfl⟩
  obtain ⟨f0, hf0⟩ : ∃ f0, f0 = R' w := ⟨_, rfl⟩
  have hmem : (f0, conj z • f0 - w) ∈ G := by rw [hf0]; exact hR' w
  have key : ∀ y, ⟪g - f0, y⟫_ℂ = 0 := by
    intro y
    have hp := hR y
    have h1 := hq' _ hp
    have h2 := hsym _ hmem _ hp
    simp only at h1 h2
    have h3 : ⟪g - f0, z • R y - y⟫_ℂ = ⟪ψ - (conj z • f0 - w), R y⟫_ℂ := by
      rw [inner_sub_left, inner_sub_left, h1, h2]
    have h4 : ψ - (conj z • f0 - w) = conj z • (g - f0) := by
      rw [hw, smul_sub]; abel
    rw [h4, inner_smul_left, inner_sub_right, inner_smul_right] at h3
    simp only [Complex.conj_conj] at h3
    -- h3 : z * ⟪k, R y⟫ - ⟪k, y⟫ = z * ⟪k, R y⟫
    have : ⟪g - f0, y⟫_ℂ = 0 := by
      have := h3
      linear_combination -this
    exact this
  have hk : g - f0 = 0 := inner_self_eq_zero.1 (key _)
  have hg : g = f0 := sub_eq_zero.1 hk
  have hψ : ψ = conj z • f0 - w := by
    rw [hw, ← hg]; abel
  show (g, ψ) ∈ G
  rw [hg, hψ]
  exact hmem

lemma Vpt_explicit (κ : ℝ) (w : ℂ) (g : E2) :
    Vpt κ w g = vec2 (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj w * g 1)
      ((2 * Complex.I) * (Real.sqrt κ : ℂ) * w * g 0) := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2]

lemma Vpt_herm (κ : ℝ) (w : ℂ) (a b : E2) : ⟪a, Vpt κ w b⟫_ℂ = ⟪Vpt κ w a, b⟫_ℂ := by
  rw [Vpt_explicit, Vpt_explicit]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, vec2_zero, vec2_one, RCLike.inner_apply,
    map_mul, map_neg, Complex.conj_conj, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

lemma split_graph {u : ℝ → ℂ} {σ : ℤˣ} {p : H2 L × H2 L} (hp : p ∈ LuGraph L κ u σ) :
    ∃ φ0 : H2 L, (p.1, φ0) ∈ LuGraph L κ (fun _ => 0) σ ∧
      ((p.2 - φ0 : H2 L) : ℝ → E2) =ᵐ[μI L] fun x => Vpt κ (u x) ((p.1 : ℝ → E2) x) := by
  obtain ⟨g, h, hrep, hbd, hae⟩ := hp
  have hmem : MemLp (fun x => (2 * Complex.I) • Jm (h x)) 2 (μI L) := by
    have := (Jcl.comp_memLp' hrep.2.1).const_smul (2 * Complex.I)
    convert this using 1
    funext x
    simp [Jcl_apply]
  refine ⟨hmem.toLp _, ⟨g, h, hrep, hbd, ?_⟩, ?_⟩
  · filter_upwards [hmem.coeFn_toLp] with x hx
    simp only [lopPt_zero_pot]
    exact hx
  · filter_upwards [Lp.coeFn_sub p.2 (hmem.toLp _), hmem.coeFn_toLp, hae, hrep.1] with x a1 a2 a3 a4
    rw [a1, Pi.sub_apply, a2, a3, lopPt_split, ← a4]
    abel

lemma Gu_symm (hL : 0 < L) {u : ℝ → ℂ} {n : ℤ} {z : ℂ} (hz : z.im ≠ 0) {R R' : H2 L →L[ℂ] H2 L}
    (hR : IsResolvent L κ (fun _ => 0) (parity n) z R)
    (hR' : IsResolvent L κ (fun _ => 0) (parity n) (conj z) R')
    {p q : H2 L × H2 L} (hp : p ∈ LuGraph L κ u (parity n)) (hq : q ∈ LuGraph L κ u (parity n)) :
    ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ := by
  obtain ⟨φ0, hp0, hpa⟩ := split_graph hp
  obtain ⟨ψ0, hq0, hqa⟩ := split_graph hq
  have hfree := free_symm hL hz hR hR' hp0 hq0
  simp only at hfree
  have hv : ⟪p.1, q.2 - ψ0⟫_ℂ = ⟪p.2 - φ0, q.1⟫_ℂ := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hqa, hpa] with x h1 h2
    rw [h1, h2]
    exact Vpt_herm κ (u x) _ _
  have e1 : ⟪p.1, q.2⟫_ℂ = ⟪p.1, ψ0⟫_ℂ + ⟪p.1, q.2 - ψ0⟫_ℂ := by
    rw [← inner_add_right]; congr 1; abel
  have e2 : ⟪p.2, q.1⟫_ℂ = ⟪φ0, q.1⟫_ℂ + ⟪p.2 - φ0, q.1⟫_ℂ := by
    rw [← inner_add_left]; congr 1; abel
  rw [e1, e2, hfree, hv]

theorem local_selfadjoint (hyp : FreeResolventHyp L κ) (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) :
    IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n)) := by
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = (pm L n : ℂ) + (r : ℂ) * Complex.I := ⟨_, rfl⟩
  have hz : ‖z - (pm L n : ℂ)‖ = r := by
    rw [hzdef]; simp [abs_of_pos hr]
  have hzc : ‖conj z - (pm L n : ℂ)‖ = r := by
    have : conj z - (pm L n : ℂ) = conj (z - (pm L n : ℂ)) := by simp [Complex.conj_ofReal]
    rw [this, RCLike.norm_conj, hz]
  have him : z.im ≠ 0 := by
    rw [hzdef]; simpa using hr.ne'
  obtain ⟨R0, R, hR0, hR, -, -, -⟩ := perturbed_resolvent hyp hr hr2 n hz u hq
  obtain ⟨R0', R', hR0', hR', -, -, -⟩ := perturbed_resolvent hyp hr hr2 n hzc u hq
  have hsym : ∀ p ∈ LuGraph L κ (u : ℝ → ℂ) (parity n), ∀ q ∈ LuGraph L κ (u : ℝ → ℂ) (parity n),
      ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ := fun p hp q hq => Gu_symm hL him hR0 hR0' hp hq
  refine ⟨?_, ?_⟩
  · have hK : 0 ≤ qpar κ L r u := qpar_nonneg κ L r u
    obtain ⟨T, hTn, hTa⟩ := exists_T (κ := κ) R0 (u : ℝ → ℂ) hK (fun φ => by
      obtain ⟨hm, hb⟩ := hyp.pot r n z R0 hr hr2 hz hR0 u φ
      exact ⟨hm, by unfold qpar; exact hb⟩)
    obtain ⟨S, R2, h1, h2, hR2, hRes2, -, -⟩ := resolvent_of_neumann hR0 hTa (lt_of_le_of_lt hTn hq)
    have hS2' : ∀ x : H2 L, S ((1 - T) x) = x := fun x => by
      have := congrArg (fun A : H2 L →L[ℂ] H2 L => A x) h2
      simpa using this
    have hchi : ∀ m : ℤ, ∀ j : Fin 2, parity m = parity n → ∃ y, R2 y = chi L m j := by
      intro m j hm
      have hne : z - (pm L m : ℂ) ≠ 0 := sub_ne_zero.2 (ne_pm_of_im him L m)
      refine ⟨(1 - T) ((z - (pm L m : ℂ)) • chi L m j), ?_⟩
      rw [hR2]
      show R0 (S ((1 - T) ((z - (pm L m : ℂ)) • chi L m j))) = _
      rw [hS2', map_smul, res_chi hL j hR0 hm (ne_pm_of_im him L m), smul_smul,
        mul_inv_cancel₀ hne, one_smul]
    have hsub : ((Submodule.span ℂ (chiSet L n) : Submodule ℂ (H2 L)) : Set (H2 L)) ⊆
        domOf (LuGraph L κ (u : ℝ → ℂ) (parity n)) := by
      have hle : Submodule.span ℂ (chiSet L n) ≤ LinearMap.range (R2 : H2 L →ₗ[ℂ] H2 L) := by
        rw [Submodule.span_le]
        rintro _ ⟨m, j, hm, rfl⟩
        obtain ⟨y, hy⟩ := hchi m j hm
        exact ⟨y, hy⟩
      intro v hv
      obtain ⟨y, rfl⟩ := hle hv
      exact ⟨_, hRes2.1 y⟩
    exact (dense_span_chi hL n).mono hsub
  · apply Set.Subset.antisymm
    · intro p hp q hq
      exact hsym p hp q hq
    · exact adj_subset hsym R R' hR.1 hR'.1

end QuantumNLS.Local002SA
#print axioms QuantumNLS.Local002SA.local_selfadjoint
