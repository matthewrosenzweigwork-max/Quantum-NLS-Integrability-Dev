import Mathlib

/-!
# R-36C23346 Part 4a: a bounded operator diagonal in a Hilbert basis commutes with a selfadjoint diagonal operator

Generic statement (no physical content). Let `B` be a Hilbert basis of a complex Hilbert space `H`, let `A` be a selfadjoint
linear partial map with `B i ∈ dom A` and `A (B i) = e i • B i` for real eigenvalues `e i`, and let `T` be a bounded
operator with `T (B i) = lam i • B i`. Then for every `ψ ∈ dom A`: `T ψ ∈ dom A` and `A (T ψ) = T (A ψ)`.

Proof: `A` is symmetric on its domain and closed. The coefficients of `A ψ` are `e i · ⟨B i, ψ⟩`. The truncations
`ψ_F = Σ_{i∈F} ⟨B i,ψ⟩ B i` lie in `dom A`, with `A (T ψ_F) = T (A ψ_F)` by finite linearity. Passing to the limit along
finsets, closedness of the graph gives the claim.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Filter Topology Finset

namespace QuantumNLS.DiagSelfAdjointCommute

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A selfadjoint partial map is symmetric on its domain. -/
theorem symmetric_of_selfAdjoint (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x y : A.domain) :
    ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have key := (LinearPMap.adjoint_isFormalAdjoint (T := A)) hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at key
  exact key x y

/-- Finite linear combinations of the eigenvectors lie in the domain, with the expected image. -/
theorem finite_comb_mem {ι : Type*} [DecidableEq ι] (B : HilbertBasis ι ℂ H) (A : H →ₗ.[ℂ] H)
    (e : ι → ℝ) (hmem : ∀ i, B i ∈ A.domain) (hval : ∀ i, A ⟨B i, hmem i⟩ = (e i : ℂ) • B i)
    (F : Finset ι) (c : ι → ℂ) :
    ∃ h : (∑ i ∈ F, c i • B i) ∈ A.domain,
      A ⟨∑ i ∈ F, c i • B i, h⟩ = ∑ i ∈ F, (c i * (e i : ℂ)) • B i := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp only [Finset.sum_empty]
    exact LinearPMap.map_zero A
  | @insert a F ha ih =>
    obtain ⟨h1, hv1⟩ := ih
    have hca : c a • B a ∈ A.domain := A.domain.smul_mem _ (hmem a)
    have hS : (∑ i ∈ insert a F, c i • B i) = c a • B a + ∑ i ∈ F, c i • B i :=
      Finset.sum_insert ha
    have hsum : (c a • B a + ∑ i ∈ F, c i • B i) ∈ A.domain := A.domain.add_mem hca h1
    have hmemS : (∑ i ∈ insert a F, c i • B i) ∈ A.domain := by rw [hS]; exact hsum
    refine ⟨hmemS, ?_⟩
    have hxy : (⟨∑ i ∈ insert a F, c i • B i, hmemS⟩ : A.domain) =
        (⟨c a • B a, hca⟩ : A.domain) + ⟨∑ i ∈ F, c i • B i, h1⟩ :=
      Subtype.ext hS
    have hadd := LinearPMap.map_add A (⟨c a • B a, hca⟩ : A.domain) ⟨∑ i ∈ F, c i • B i, h1⟩
    have e2 : A ⟨c a • B a, hca⟩ = c a • A ⟨B a, hmem a⟩ := LinearPMap.map_smul A (c a) ⟨B a, hmem a⟩
    rw [hxy, hadd, e2, hval a, hv1, Finset.sum_insert ha, smul_smul]

/-- **Generic commutation.** A bounded operator diagonal in a Hilbert basis commutes (on the domain) with a
selfadjoint partial map diagonal in the same basis with real eigenvalues. -/
theorem diag_selfAdjoint_commute {ι : Type*} [DecidableEq ι] (B : HilbertBasis ι ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (e : ι → ℝ) (hmem : ∀ i, B i ∈ A.domain)
    (hval : ∀ i, A ⟨B i, hmem i⟩ = (e i : ℂ) • B i) (T : H →L[ℂ] H) (lam : ι → ℂ)
    (hT : ∀ i, T (B i) = lam i • B i) (ψ : H) (hψ : ψ ∈ A.domain) :
    ∃ h : T ψ ∈ A.domain, A ⟨T ψ, h⟩ = T (A ⟨ψ, hψ⟩) := by
  -- coordinates of `A ψ`
  have hcoord : ∀ i, B.repr (A ⟨ψ, hψ⟩) i = (e i : ℂ) * B.repr ψ i := by
    intro i
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
    have hs : ⟪A ⟨B i, hmem i⟩, ψ⟫_ℂ = ⟪B i, A ⟨ψ, hψ⟩⟫_ℂ :=
      symmetric_of_selfAdjoint A hA ⟨B i, hmem i⟩ ⟨ψ, hψ⟩
    rw [← hs, hval i, inner_smul_left, Complex.conj_ofReal]
  set c : ι → ℂ := fun i => B.repr ψ i with hc_def
  -- truncations of `ψ` and of `A ψ`
  have hψF : Tendsto (fun F : Finset ι => ∑ i ∈ F, c i • B i) atTop (𝓝 ψ) := B.hasSum_repr ψ
  have hAψF : Tendsto (fun F : Finset ι => ∑ i ∈ F, ((e i : ℂ) * c i) • B i) atTop
      (𝓝 (A ⟨ψ, hψ⟩)) := by
    have hs := B.hasSum_repr (A ⟨ψ, hψ⟩)
    have hfun : (fun i => B.repr (A ⟨ψ, hψ⟩) i • B i) = fun i => ((e i : ℂ) * c i) • B i := by
      funext i
      rw [hcoord i]
    rw [hfun] at hs
    exact hs
  -- `T` on truncations
  have hTψF : ∀ F : Finset ι, T (∑ i ∈ F, c i • B i) = ∑ i ∈ F, (c i * lam i) • B i := by
    intro F
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hT i, smul_smul]
  have hcomm : ∀ F : Finset ι, ∑ i ∈ F, ((c i * lam i) * (e i : ℂ)) • B i =
      T (∑ i ∈ F, ((e i : ℂ) * c i) • B i) := by
    intro F
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hT i, smul_smul]
    congr 1
    ring
  -- domain and values of `A` on the truncations of `T ψ`
  have hdomF : ∀ F : Finset ι, ∃ h : (∑ i ∈ F, (c i * lam i) • B i) ∈ A.domain,
      A ⟨∑ i ∈ F, (c i * lam i) • B i, h⟩ = ∑ i ∈ F, ((c i * lam i) * (e i : ℂ)) • B i :=
    fun F => finite_comb_mem B A e hmem hval F (fun i => c i * lam i)
  choose hdF hvalF using hdomF
  have hdF' : ∀ F : Finset ι, T (∑ i ∈ F, c i • B i) ∈ A.domain := fun F => by
    rw [hTψF F]
    exact hdF F
  have hval' : ∀ F : Finset ι, A ⟨T (∑ i ∈ F, c i • B i), hdF' F⟩ =
      T (∑ i ∈ F, ((e i : ℂ) * c i) • B i) := by
    intro F
    have hsub : (⟨T (∑ i ∈ F, c i • B i), hdF' F⟩ : A.domain) =
        ⟨∑ i ∈ F, (c i * lam i) • B i, hdF F⟩ := Subtype.ext (hTψF F)
    rw [hsub, hvalF F, hcomm F]
  have hgraph : ∀ F : Finset ι, (T (∑ i ∈ F, c i • B i),
      T (∑ i ∈ F, ((e i : ℂ) * c i) • B i)) ∈ A.graph := by
    intro F
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨_, hdF' F⟩, rfl, hval' F⟩
  -- closedness of the graph
  have hlim : Tendsto (fun F : Finset ι => (T (∑ i ∈ F, c i • B i),
      T (∑ i ∈ F, ((e i : ℂ) * c i) • B i))) atTop (𝓝 (T ψ, T (A ⟨ψ, hψ⟩))) :=
    ((T.continuous.tendsto ψ).comp hψF).prodMk_nhds ((T.continuous.tendsto _).comp hAψF)
  have hcl : IsClosed (A.graph : Set (H × H)) := hA.isClosed
  have hres : (T ψ, T (A ⟨ψ, hψ⟩)) ∈ A.graph :=
    hcl.mem_of_tendsto hlim (Eventually.of_forall hgraph)
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff A).mp hres
  have hy1' : (y : H) = T ψ := hy1
  have hy2' : A y = T (A ⟨ψ, hψ⟩) := hy2
  have hmemψ : T ψ ∈ A.domain := by
    rw [← hy1']
    exact y.2
  refine ⟨hmemψ, ?_⟩
  have hyeq : (⟨T ψ, hmemψ⟩ : A.domain) = y := Subtype.ext hy1'.symm
  rw [hyeq]
  exact hy2'

end QuantumNLS.DiagSelfAdjointCommute

#print axioms QuantumNLS.DiagSelfAdjointCommute.diag_selfAdjoint_commute
