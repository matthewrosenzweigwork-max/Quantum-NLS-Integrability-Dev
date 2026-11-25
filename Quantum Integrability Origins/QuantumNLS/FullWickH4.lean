import Mathlib

/-! FullWickH4 (haiku_inventory, R-140AE34B `thm:full-wick`, Stage 3, generic telescoping bridge).

The printed strong-symbol clause (wick_calculus.tex:82-89, 182-202) reduces, for products of
operators with uniformly controlled norms, to the telescoping identity
  A_1 ⋯ A_d − s_1 ⋯ s_d = Σ_l A_1 ⋯ A_{l−1} (A_l − s_l) s_{l+1} ⋯ s_d.
This file proves the two-factor case exactly (`uniform_mul`), together with the adjoint pairing
needed for the printed "strong symbol and its adjoint" clause (`pair_mul`). Longer ordered products
follow by induction on the number of factors from `pair_mul`.

Deviation from StrongSymbolDef: the symbol here may depend on the time-box point as well as on the
profile (`a : X → Θ → ℂ`), because the printed symbol f(w(u)) depends on the time parameter through
w(u). StrongSymbolDef.HasUniformStrongSymbol has a profile-only symbol and is the special case with
a constant time dependence.

Standard axioms only.
-/

noncomputable section
open Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH4

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]

/-- Uniform strong symbol over a profile class `S` and time set `Tb`, with symbol `a u t`:
`‖(A_N − a(u,t)) ψ_{u,t,N}‖ → 0` uniformly, in ε–N₀ form. -/
def HasUniformStrongT {X Θ : Type*} (A : ∀ N, H N →L[ℂ] H N) (S : Set X) (Tb : Set Θ)
    (ψ : X → Θ → ∀ N, H N) (a : X → Θ → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb,
    ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ ≤ ε

/-- The operator `A` with companion family `A'` (the adjoint clause): `A` has symbol `a`, and `A'`
has the conjugate symbol `conj a`. -/
def HasUniformPairT {X Θ : Type*} (A A' : ∀ N, H N →L[ℂ] H N) (S : Set X) (Tb : Set Θ)
    (ψ : X → Θ → ∀ N, H N) (a : X → Θ → ℂ) : Prop :=
  HasUniformStrongT A S Tb ψ a ∧
    HasUniformStrongT A' S Tb ψ (fun u t => (starRingEnd ℂ) (a u t))

/-- Vector identity behind the telescoping step:
`PQx − pqx = P((Q − q)x) + q((P − p)x)`. -/
lemma key_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P Q : E →L[ℂ] E) (p q : ℂ) (x : E) :
    (P * Q - (p * q) • ContinuousLinearMap.id ℂ E) x
      = P ((Q - q • ContinuousLinearMap.id ℂ E) x) + q • ((P - p • ContinuousLinearMap.id ℂ E) x) := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul,
    smul_sub, smul_smul, mul_comm q p]
  abel

/-- **Telescoping product (two factors).** If `P` and `Q` have uniformly bounded norms and
uniform strong symbols `p`, `q` (bounded by `K`) on a common preparation, then `PQ` has the uniform
strong symbol `c = p q` (any function equal to `p q`). -/
theorem uniform_mul {X Θ : Type*} {P Q : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ}
    {ψ : X → Θ → ∀ N, H N} {p q c : X → Θ → ℂ} {C K : ℝ}
    (hP : ∀ᶠ N in atTop, ‖P N‖ ≤ C)
    (hq : ∀ u ∈ S, ∀ t ∈ Tb, ‖q u t‖ ≤ K)
    (hPs : HasUniformStrongT P S Tb ψ p) (hQs : HasUniformStrongT Q S Tb ψ q)
    (hc : ∀ u t, c u t = p u t * q u t) :
    HasUniformStrongT (fun N => P N * Q N) S Tb ψ c := by
  intro ε hε
  set D : ℝ := |C| + |K| + 1 with hD
  have hDpos : 0 < D := by positivity
  set δ : ℝ := ε / D with hδ
  have hδpos : 0 < δ := div_pos hε hDpos
  have hDne : D ≠ 0 := hDpos.ne'
  have hδD : D * δ = ε := by
    rw [hδ]; field_simp
  filter_upwards [hP, hPs δ hδpos, hQs δ hδpos] with N hPN hPs' hQs'
  intro u hu t ht
  have hcomp : (P N * Q N - c u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)
      = P N ((Q N - q u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))
        + q u t • ((P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)) := by
    rw [hc u t]
    exact key_identity (P N) (Q N) (p u t) (q u t) (ψ u t N)
  rw [hcomp]
  have hv1 : ‖P N ((Q N - q u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖ ≤ |C| * δ :=
    (ContinuousLinearMap.le_opNorm (P N) _).trans
      (mul_le_mul ((hPN).trans (le_abs_self C)) (hQs' u hu t ht) (norm_nonneg _) (abs_nonneg C))
  have hv2 : ‖q u t • ((P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖ ≤ |K| * δ := by
    rw [norm_smul]
    exact mul_le_mul ((hq u hu t ht).trans (le_abs_self K)) (hPs' u hu t ht)
      (norm_nonneg _) (abs_nonneg K)
  calc ‖P N ((Q N - q u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))
        + q u t • ((P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖
      ≤ ‖P N ((Q N - q u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖
        + ‖q u t • ((P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖ := norm_add_le _ _
    _ ≤ |C| * δ + |K| * δ := add_le_add hv1 hv2
    _ ≤ D * δ := by
        rw [hD]
        have : 0 ≤ δ := hδpos.le
        nlinarith [abs_nonneg C, abs_nonneg K]
    _ = ε := hδD

/-- **Adjoint pairing for a product.** If `(P, P')` and `(Q, Q')` are uniform strong-symbol pairs,
then `(PQ, Q'P')` is a uniform strong-symbol pair with symbol `p q` (the adjoint of `PQ` being
`Q' P'`, with conjugate symbol `conj(p q) = conj q · conj p`). -/
theorem pair_mul {X Θ : Type*} {P P' Q Q' : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ}
    {ψ : X → Θ → ∀ N, H N} {p q : X → Θ → ℂ} {C K : ℝ}
    (hP : ∀ᶠ N in atTop, ‖P N‖ ≤ C) (hQ' : ∀ᶠ N in atTop, ‖Q' N‖ ≤ C)
    (hp : ∀ u ∈ S, ∀ t ∈ Tb, ‖p u t‖ ≤ K) (hq : ∀ u ∈ S, ∀ t ∈ Tb, ‖q u t‖ ≤ K)
    (hPp : HasUniformPairT P P' S Tb ψ p) (hQq : HasUniformPairT Q Q' S Tb ψ q) :
    HasUniformPairT (fun N => P N * Q N) (fun N => Q' N * P' N) S Tb ψ (fun u t => p u t * q u t) := by
  refine ⟨uniform_mul hP hq hPp.1 hQq.1 (fun u t => rfl), ?_⟩
  refine uniform_mul (K := K) (C := C) (P := Q') (Q := P') (p := fun u t => (starRingEnd ℂ) (q u t))
    (q := fun u t => (starRingEnd ℂ) (p u t)) hQ' ?_ hQq.2 hPp.2 ?_
  · intro u hu t ht
    rw [Complex.norm_conj]
    exact hp u hu t ht
  · intro u t
    simp only [map_mul]
    ring

end QuantumNLS.FullWickH4

#print axioms QuantumNLS.FullWickH4.key_identity
#print axioms QuantumNLS.FullWickH4.uniform_mul
#print axioms QuantumNLS.FullWickH4.pair_mul
