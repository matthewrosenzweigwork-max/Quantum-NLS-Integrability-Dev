import Mathlib
import QuantumNLS.Prop022CMain

/-! PROP-022 route A, round 5, stage D3: the pure quasifree predicate, symplectic AUTOMORPHISMS, and the
Heisenberg (field) form.

Printed meaning (fluctuations.tex, sha256 148307137b27...e51ab7).  The print never defines "pure quasifree" by a
displayed formula.  It uses it as follows:
* l.109-111: "The quadratic Hamiltonian `𝕢(t)` has a unitary propagator `𝕍(t,s)` implementing `S(t,s)`.  In
  particular `ξ_t = 𝕍(t,0)Ω` is pure quasifree and `⟨ξ_t, Num ξ_t⟩ = ‖β(t,0)‖²_HS`.";
* l.178-184: "On that common domain the canonical commutation relations show that `𝕍(t,s)` implements the solution
  of (linearized).  ... Equivalently, differentiate Weyl matrix elements and use uniqueness of the bounded linear
  equation.  The implementability criterion and squeezed-vacuum formula are [BD, Theorem 4.2].";
* l.193-206 (PROP-023): "a normalized pure quasifree vacuum ... The squeezed-vacuum formula of [BD, Theorem 4.2]
  writes `ξ`, up to a phase, as `det(1-K*K)^{1/4} exp(-a*(K)/2)Ω`".
So in the print, "pure quasifree" = "image of the vacuum under a unitary that IMPLEMENTS a symplectic
automorphism `S` of the one-particle space" (Weyl matrix elements / CCR form); the squeezed-vacuum formula is a
cited THEOREM about such vectors, not their definition.  `S(t,s)` is `DΦ` of an invertible flow, i.e. a symplectic
AUTOMORPHISM (it is invertible with inverse `S(s,t)`).

This module:
* `IsSymplecticAut S`: `S` is bijective and preserves `Im ⟪·,·⟫`.  `SH_symplecticAut`, `SJ_symplecticAut`: every
  in-scope `S(t,s)` is a symplectic automorphism (`SH_inv`, `SJ_inv`: `S(t,s) S(s,t) = 1`).
* `PureQuasifreeG ξ`: the GROUP form of the Bogoliubov implementer: `ξ = VΩ`, `Ω` a vacuum, `V` unitary,
  `S` a bounded real-linear symplectic automorphism, and for every `v` the Weyl GROUPS (Stone, generator the
  closure of `a*(v) - a(v)`, `a*`, `a` the intrinsic creation/annihilation operators) satisfy
  `V W_v(r) V⁻¹ = W_{Sv}(r)` for all real `r`.  `PureQuasifreeG ξ → PureQuasifreeH ξ` (`PureQuasifreeG.toH`).
* `heis_of_groups`: the group relation implies the HEISENBERG (field) form: `V⁻¹ (a*(Sv) - a(Sv)) V = a*(v) - a(v)`
  weakly on the finite-particle core (`⟪Z_{Sv} y, V x⟫ + ⟪y, V Z_v x⟫ = 0`, `Z_v = a*(v) - a(v)`), proved by Stone's
  theorem (the derivative at `0` of `r ↦ V W_v(r) x = W_{Sv}(r) V x` puts `(Vx, V Z_v x)` in the closed generator
  graph of `Sv`, and the closed graph is skew).
* `QFAut V S Ω` packages these for a propagator family; `QFAut_of_data` derives it from the frozen implementation
  relation and `QFAut_U`, `QFAut_J` instantiate it for the in-scope `VH, SH, vacH` / `VJ, SJ, vacJ`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
open Filter
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022DQuasi
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1
open QuantumNLS.Prop022CWeyl QuantumNLS.Prop022CStone QuantumNLS.Prop022CIntrinsic
open QuantumNLS.Prop022AFock
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GAntiHS Prop022GClassical Prop022GLinear Prop022BClass1 Prop022BClass2 Prop022BFock2
open Prop022BFock3 Prop022FactorialCoefficientsR115 Prop022PositiveDataR126

/-! ### Symplectic automorphisms -/

section Aut
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symplectic AUTOMORPHISM of `E` (with the original complex structure): a bijective bounded real-linear map
preserving the symplectic form `Im ⟪·,·⟫`. -/
def IsSymplecticAut (S : E →L[ℝ] E) : Prop :=
  Function.Bijective S ∧ ∀ x y : E, (⟪S x, S y⟫_ℂ).im = (⟪x, y⟫_ℂ).im

lemma isSymplecticAut_of_inv {S S' : E →L[ℝ] E} (h1 : ∀ x, S (S' x) = x) (h2 : ∀ x, S' (S x) = x)
    (hs : ∀ x y : E, (⟪S x, S y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) : IsSymplecticAut S :=
  ⟨⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩, hs⟩

end Aut

section InScopeAut
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The cocycle identity `S(t,s) S(s,t) = 1` for the transported variational flow. -/
theorem SH_inv (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t s : ℝ) (x : H) :
    SH U K M A hA hK hs u₀ hu₀ t s (SH U K M A hA hK hs u₀ hu₀ s t x) = x := by
  rw [SH_apply, SH_apply, LinearIsometryEquiv.apply_symm_apply,
    Prop022VariationalR123.flow_comp, Prop022VariationalR123.flow_self,
    LinearIsometryEquiv.symm_apply_apply]

/-- **Every in-scope `S_H(t,s)` is a symplectic automorphism** (bijective, with inverse `S_H(s,t)`). -/
theorem SH_symplecticAut (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t s : ℝ) :
    IsSymplecticAut (SH U K M A hA hK hs u₀ hu₀ t s) :=
  isSymplecticAut_of_inv (SH_inv U K M A hA hK hs u₀ hu₀ t s) (SH_inv U K M A hA hK hs u₀ hu₀ s t)
    (fun x y => Prop022CMain.SH_symplectic U K M A hA hK hs u₀ hu₀ t s x y)

/-- The cocycle identity for the compressed variational flow of the finite-dimensional case. -/
theorem SJ_inv (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t s : ℝ) (x : H) :
    SJ J K M A hA hK hs u₀ hu₀ t s (SJ J K M A hA hK hs u₀ hu₀ s t x) = x := by
  apply J.injective
  rw [← S_embed J K M A hA hK hs u₀ hu₀ t s, ← S_embed J K M A hA hK hs u₀ hu₀ s t]
  exact SH_inv (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t s (J x)

/-- **Every in-scope `S_J(t,s)` is a symplectic automorphism.** -/
theorem SJ_symplecticAut (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t s : ℝ) :
    IsSymplecticAut (SJ J K M A hA hK hs u₀ hu₀ t s) :=
  isSymplecticAut_of_inv (SJ_inv J K M A hA hK hs u₀ hu₀ t s) (SJ_inv J K M A hA hK hs u₀ hu₀ s t)
    (fun x y => Prop022CMain.SJ_symplectic J K M A hA hK hs u₀ hu₀ t s x y)

end InScopeAut

/-! ### Group-level implementer, Heisenberg form -/

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Pure quasifree, group form**: `ξ = VΩ` with `Ω` a vacuum, `V` a unitary of `Fock(E)` implementing the
symplectic AUTOMORPHISM `S` on the intrinsic Weyl GROUPS (`V W_v(r) V⁻¹ = W_{Sv}(r)`, all real `r`). -/
def PureQuasifreeG (ξ : FockSpace E) : Prop :=
  ∃ (Ω : FockSpace E) (S : E →L[ℝ] E) (V : FockSpace E ≃ₗᵢ[ℂ] FockSpace E),
    IsVacuum Ω ∧ IsSymplecticAut S ∧
    (∀ v : E, ∃ G G' : ℝ → FockSpace E ≃ₗᵢ[ℂ] FockSpace E, IsWeylGroup v G ∧ IsWeylGroup (S v) G' ∧
      ∀ r x, V (G r x) = G' r (V x)) ∧ ξ = V Ω

/-- The group form implies the time-one (`PureQuasifreeH`) form used in the round-4 headline. -/
theorem PureQuasifreeG.toH {ξ : FockSpace E} (h : PureQuasifreeG ξ) : PureQuasifreeH ξ := by
  obtain ⟨Ω, S, V, hΩ, ⟨-, hS⟩, hW, rfl⟩ := h
  refine ⟨Ω, S, V, hΩ, hS, fun v => ?_, rfl⟩
  obtain ⟨G, G', hG, hG', hV⟩ := hW v
  exact ⟨G 1, G' 1, ⟨G, hG, rfl⟩, ⟨G', hG', rfl⟩, fun x => hV 1 x⟩

/-- **Heisenberg (field) form of the Bogoliubov implementation.**  If `V W_v(r) = W_w(r) V` for the Weyl groups of
`v` and `w`, then `V⁻¹ (a*(w) - a(w)) V = a*(v) - a(v)` in the weak sense on the finite-particle core:
`⟪Z_w y, V x⟫ + ⟪y, V Z_v x⟫ = 0` for `x, y ∈ Dfin E`, where `Z_f = a*(f) - a(f)` (`Prop022CCanon.Zgen`). -/
theorem heis_of_groups {v w : E} {G G' : ℝ → FockSpace E ≃ₗᵢ[ℂ] FockSpace E}
    (hG : IsWeylGroup v G) (hG' : IsWeylGroup w G') (V : FockSpace E ≃ₗᵢ[ℂ] FockSpace E)
    (hV : ∀ r x, V (G r x) = G' r (V x)) (x y : Dfin E) :
    ⟪(Zgen w y : FockSpace E), V (x : FockSpace E)⟫_ℂ + ⟪(y : FockSpace E), V (Zgen v x : FockSpace E)⟫_ℂ = 0 := by
  have hmem : ((x : FockSpace E), (Zgen v x : FockSpace E)) ∈ gcl E v := subset_closure ⟨x, rfl⟩
  have hd : HasDerivAt (fun s : ℝ => G s (x : FockSpace E)) (Zgen v x : FockSpace E) 0 :=
    (hG.gen _ _).mpr hmem
  have hd1 : HasDerivAt (fun s : ℝ => G' s (V (x : FockSpace E))) (V (Zgen v x : FockSpace E)) 0 := by
    have h1 := hasDerivAt_clm V.toContinuousLinearEquiv.toContinuousLinearMap hd
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (hV s _).symm)
  have hmem' : (V (x : FockSpace E), V (Zgen v x : FockSpace E)) ∈ gcl E w := (hG'.gen _ _).mp hd1
  have hy : ((y : FockSpace E), (Zgen w y : FockSpace E)) ∈ gcl E w := subset_closure ⟨y, rfl⟩
  have hskew : ⟪(Zgen w y : FockSpace E), V (x : FockSpace E)⟫_ℂ +
      ⟪(y : FockSpace E), V (Zgen v x : FockSpace E)⟫_ℂ = 0 :=
    gcl_skew w ((y : FockSpace E), (Zgen w y : FockSpace E)) hy
      (V (x : FockSpace E), V (Zgen v x : FockSpace E)) hmem'
  exact hskew

end Generic

/-- Package: for a family of propagators `V t s`, symplectic maps `S t s` and a vacuum `Ω`. -/
structure QFAut {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (V : ℝ → ℝ → FockSpace E ≃ₗᵢ[ℂ] FockSpace E) (S : ℝ → ℝ → E →L[ℝ] E) (Ω : FockSpace E) : Prop where
  /-- every `S t s` is a symplectic automorphism -/
  aut : ∀ t s, IsSymplecticAut (S t s)
  /-- `S t s ∘ S s t = 1` -/
  inv : ∀ t s x, S t s (S s t x) = x
  /-- the evolved vacuum is pure quasifree (group form) -/
  quasifree : ∀ t, PureQuasifreeG (V t 0 Ω)
  /-- Heisenberg (field) form: `V⁻¹ Z_{S(t,s)v} V = Z_v` weakly on the finite-particle core -/
  heis : ∀ s t (v : E) (x y : Dfin E),
    ⟪(Zgen (S t s v) y : FockSpace E), V t s (x : FockSpace E)⟫_ℂ +
      ⟪(y : FockSpace E), V t s (Zgen v x : FockSpace E)⟫_ℂ = 0

section Data
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem QFAut_of_data (V : ℝ → ℝ → FockSpace E ≃ₗᵢ[ℂ] FockSpace E) (S : ℝ → ℝ → E →L[ℝ] E)
    (Ω : FockSpace E) (Wf : E → FockSpace E ≃ₗᵢ[ℂ] FockSpace E)
    (hW : ∀ v : E, IsWeylGroup v (fun r : ℝ => Wf ((r : ℂ) • v)))
    (himpl : ∀ s t (v : E) (x : FockSpace E), V t s (Wf v ((V t s).symm x)) = Wf (S t s v) x)
    (hΩ : IsVacuum Ω) (haut : ∀ t s, IsSymplecticAut (S t s))
    (hinv : ∀ t s x, S t s (S s t x) = x) : QFAut V S Ω := by
  have hgrp : ∀ s t (v : E), ∀ (r : ℝ) (x : FockSpace E), V t s (Wf ((r : ℂ) • v) x) =
      Wf ((r : ℂ) • S t s v) (V t s x) := by
    intro s t v r x
    have h := himpl s t ((r : ℂ) • v) (V t s x)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    rw [h]
    have e : ∀ u : E, ((r : ℂ) • u) = r • u := fun u => rfl
    rw [e v, map_smul, ← e (S t s v)]
  refine ⟨haut, hinv, fun t => ?_, fun s t v x y => ?_⟩
  · refine ⟨Ω, S t 0, V t 0, hΩ, haut t 0, fun v => ⟨_, _, hW v, hW (S t 0 v), hgrp 0 t v⟩, rfl⟩
  · exact heis_of_groups (hW v) (hW (S t s v)) (V t s) (hgrp s t v) x y

end Data

/-! ### The in-scope instances -/

section InScope
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

theorem QFAut_U [TopologicalSpace.SeparableSpace H] (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H)
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H)
    (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    let hM0 : 0 ≤ M := by linarith
    QFAut (VH U K M A hA.le hK hs u₀ hu₀ hM0) (SH U K M A hA.le hK hs u₀ hu₀) (vacH U) := by
  intro hM0
  have h := PROP022_fock_transport U K M A hM hA hK hs u₀ hu₀ T P hP e
  obtain ⟨-, -, -, -, himpl, -⟩ := h
  exact QFAut_of_data _ _ _ (WH U) (fun v => WH_isWeylGroup U v) (fun s t v x => himpl s t v x)
    (Prop022CMain.isVacuum_vacH U) (SH_symplecticAut U K M A hA.le hK hs u₀ hu₀)
    (SH_inv U K M A hA.le hK hs u₀ hu₀)

theorem QFAut_J [TopologicalSpace.SeparableSpace H] (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H)
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H)
    (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    QFAut (VJ J K M A hM hA hK hs u₀ hu₀) (SJ J K M A hA.le hK hs u₀ hu₀) (vacJ J) := by
  have h := PROP022_fock_J J K M A hM hA hK hs u₀ hu₀ e T P hP
  obtain ⟨-, -, -, -, himpl, -⟩ := h
  exact QFAut_of_data _ _ _ (WJ J) (fun v => WJ_isWeylGroup J v) (fun s t v x => himpl s t v x)
    (Prop022CMain.isVacuum_vacJ J) (SJ_symplecticAut J K M A hA.le hK hs u₀ hu₀)
    (SJ_inv J K M A hA.le hK hs u₀ hu₀)

end InScope

end QuantumNLS.Prop022DQuasi

#print axioms QuantumNLS.Prop022DQuasi.SH_symplecticAut
#print axioms QuantumNLS.Prop022DQuasi.SJ_symplecticAut
#print axioms QuantumNLS.Prop022DQuasi.heis_of_groups
#print axioms QuantumNLS.Prop022DQuasi.PureQuasifreeG.toH
#print axioms QuantumNLS.Prop022DQuasi.QFAut_U
#print axioms QuantumNLS.Prop022DQuasi.QFAut_J
