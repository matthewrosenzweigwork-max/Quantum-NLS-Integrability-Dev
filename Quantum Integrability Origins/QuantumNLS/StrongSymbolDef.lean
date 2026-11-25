import Mathlib
import QuantumNLS.StrongSymbols

/-!
# DEF-028: strong scalar symbols and norm-close preparations

Source: `source/chapters/definitions.tex` lines 169–171 (DEF-028, label `def:report-28`): a uniformly
bounded observable `A_N` has strong scalar symbol `a(u)` on a preparation `ψ_N` if
`‖(A_N − a(u))ψ_N‖ → 0`; uniform versions specify the profile class and time box in the supremum;
norm-close preparations satisfy `‖ψ_N − u^{⊗N}‖ → 0` and are normalized; bounded observables transfer
their strong symbols to such preparations by the triangle inequality.

Contents (definitions and transfer only; no new physics claim):

* `HasStrongSymbol A ψ a`: pointwise DEF-028, `‖(A_N − a·1)ψ_N‖ → 0` (the operator `A_N − a·1` is
  written literally).
* `HasUniformStrongSymbol A S Tb ψ a`: uniform version. For every `ε > 0`, eventually in `N`, every
  profile `u ∈ S` and time-box parameter `t ∈ Tb` satisfies `‖(A_N − a(u))ψ_{u,t,N}‖ ≤ ε`. This is the
  ε–N₀ form of "the supremum over `S × Tb` tends to `0`", so no `sSup` of an unbounded family is used.
* `IsNormalized ψ` (`‖ψ_N‖ = 1` for all `N`) and `IsNormClosePrep ψ φ` (normalized, and
  `‖ψ_N − φ_N‖ → 0`).
* `hasStrongSymbol_of_normClose`, `hasUniformStrongSymbol_of_normClose`: the triangle-inequality transfer.
  Only an eventual bound `‖A_N‖ ≤ C` is used; the transfer does not use normalization.
* `physical_strongSymbol_normClose`: one instance on the physical Fourier sector. For balanced `f` and a
  unit `u ∈ L²(𝕋_L)`, the physical Wick operators `physicalWick L N f` have the strong symbol `f(û)` of
  `StrongSymbols.strong_symbol_physical` on every norm-close preparation of `u^{⊗N}`. The uniform bound
  is `WickBounds.WHil_norm_le`, transported by `PhysicalWickLimit.norm_eq_of_intertwine`.

Qualifications: Fourier occupation realisation, as in `StrongSymbols` (no Bethe chart, no U5, no
selected gauge). The uniform-in-profile physical instance is not stated here: `StrongSymbols.strong_symbol_uniform`
is a uniform statement in the occupation realisation only.
-/

namespace QuantumNLS.StrongSymbolDef

open Filter Topology
open QuantumNLS.WickSymbols QuantumNLS.WickBounds QuantumNLS.PhysicalWickLimit
open QuantumNLS.OccupationUnitary

section General

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]

/-- DEF-028 (pointwise): `A` has strong scalar symbol `a` on the preparation `ψ`, i.e.
`‖(A_N − a)ψ_N‖ → 0`. -/
def HasStrongSymbol (A : ∀ N, H N →L[ℂ] H N) (ψ : ∀ N, H N) (a : ℂ) : Prop :=
  Tendsto (fun N => ‖(A N - a • ContinuousLinearMap.id ℂ (H N)) (ψ N)‖) atTop (𝓝 0)

/-- DEF-028 (uniform): over a profile class `S` and a time box `Tb`, the supremum of
`‖(A_N − a(u))ψ_{u,t,N}‖` tends to `0`, stated in ε–N₀ form. -/
def HasUniformStrongSymbol {X Θ : Type*} (A : ∀ N, H N →L[ℂ] H N) (S : Set X) (Tb : Set Θ)
    (ψ : X → Θ → ∀ N, H N) (a : X → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb,
    ‖(A N - a u • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ ≤ ε

/-- Normalized preparation: `‖ψ_N‖ = 1` for every `N`. -/
def IsNormalized (ψ : ∀ N, H N) : Prop := ∀ N, ‖ψ N‖ = 1

/-- Norm-close preparation of a reference sequence `φ` (DEF-028: `‖ψ_N − φ_N‖ → 0` and normalized). -/
def IsNormClosePrep (ψ φ : ∀ N, H N) : Prop :=
  IsNormalized ψ ∧ Tendsto (fun N => ‖ψ N - φ N‖) atTop (𝓝 0)

/-- Operator-norm estimate `‖(T − a·1)x‖ ≤ (‖T‖ + ‖a‖)‖x‖`. -/
lemma norm_sub_smul_id_apply_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (a : ℂ) (x : E) :
    ‖(T - a • ContinuousLinearMap.id ℂ E) x‖ ≤ (‖T‖ + ‖a‖) * ‖x‖ := by
  refine (ContinuousLinearMap.le_opNorm _ x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  have hsm : ‖a • ContinuousLinearMap.id ℂ E‖ ≤ ‖a‖ * ‖ContinuousLinearMap.id ℂ E‖ :=
    norm_smul_le a (ContinuousLinearMap.id ℂ E)
  have hid : ‖ContinuousLinearMap.id ℂ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hid' : ‖a‖ * ‖ContinuousLinearMap.id ℂ E‖ ≤ ‖a‖ :=
    mul_le_of_le_one_right (norm_nonneg a) hid
  calc ‖T - a • ContinuousLinearMap.id ℂ E‖
      ≤ ‖T‖ + ‖a • ContinuousLinearMap.id ℂ E‖ := norm_sub_le _ _
    _ ≤ ‖T‖ + ‖a‖ := by linarith

/-- **Transfer (pointwise, triangle inequality).** A uniformly bounded observable transfers a strong
symbol from `φ` to any `ψ` with `‖ψ_N − φ_N‖ → 0`. Only the eventual bound `‖A_N‖ ≤ C` is used. -/
theorem hasStrongSymbol_of_normClose {A : ∀ N, H N →L[ℂ] H N} {ψ φ : ∀ N, H N} {a : ℂ} {C : ℝ}
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ C)
    (hφ : HasStrongSymbol A φ a) (hψφ : Tendsto (fun N => ‖ψ N - φ N‖) atTop (𝓝 0)) :
    HasStrongSymbol A ψ a := by
  unfold HasStrongSymbol at hφ ⊢
  have hlim := hφ.add (hψφ.const_mul (C + ‖a‖))
  rw [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [hA] with N hN
  have hsplit : (A N - a • ContinuousLinearMap.id ℂ (H N)) (ψ N)
      = (A N - a • ContinuousLinearMap.id ℂ (H N)) (φ N)
        + (A N - a • ContinuousLinearMap.id ℂ (H N)) (ψ N - φ N) := by
    rw [← map_add]
    congr 1
    abel
  have h2 := norm_sub_smul_id_apply_le (A N) a (ψ N - φ N)
  have h3 : (‖A N‖ + ‖a‖) * ‖ψ N - φ N‖ ≤ (C + ‖a‖) * ‖ψ N - φ N‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  rw [hsplit]
  have h1 := norm_add_le ((A N - a • ContinuousLinearMap.id ℂ (H N)) (φ N))
    ((A N - a • ContinuousLinearMap.id ℂ (H N)) (ψ N - φ N))
  linarith

/-- **Transfer (uniform).** Uniform strong symbols over `S × Tb` transfer to any uniformly norm-close
family, provided the symbols are bounded on `S` (`‖a(u)‖ ≤ K`) and the operators are eventually bounded. -/
theorem hasUniformStrongSymbol_of_normClose {X Θ : Type*} {A : ∀ N, H N →L[ℂ] H N} {S : Set X}
    {Tb : Set Θ} {ψ φ : X → Θ → ∀ N, H N} {a : X → ℂ} {C K : ℝ}
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ C) (hK : ∀ u ∈ S, ‖a u‖ ≤ K)
    (hφ : HasUniformStrongSymbol A S Tb φ a)
    (hψφ : ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N - φ u t N‖ ≤ ε) :
    HasUniformStrongSymbol A S Tb ψ a := by
  intro ε hε
  have hDpos : 0 < |C| + |K| + 1 := by positivity
  have h1 := hφ (ε / 2) (by positivity)
  have h2 := hψφ (ε / (2 * (|C| + |K| + 1))) (by positivity)
  filter_upwards [h1, h2, hA] with N hN1 hN2 hNA
  intro u hu t ht
  have hsplit : (A N - a u • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)
      = (A N - a u • ContinuousLinearMap.id ℂ (H N)) (φ u t N)
        + (A N - a u • ContinuousLinearMap.id ℂ (H N)) (ψ u t N - φ u t N) := by
    rw [← map_add]
    congr 1
    abel
  have hbd := norm_sub_smul_id_apply_le (A N) (a u) (ψ u t N - φ u t N)
  have hsum : ‖A N‖ + ‖a u‖ ≤ |C| + |K| + 1 := by
    linarith [le_abs_self C, le_abs_self K, abs_nonneg C, abs_nonneg K, hK u hu]
  have h3 : (‖A N‖ + ‖a u‖) * ‖ψ u t N - φ u t N‖
      ≤ (|C| + |K| + 1) * ‖ψ u t N - φ u t N‖ :=
    mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have h4 : (|C| + |K| + 1) * ‖ψ u t N - φ u t N‖
      ≤ (|C| + |K| + 1) * (ε / (2 * (|C| + |K| + 1))) :=
    mul_le_mul_of_nonneg_left (hN2 u hu t ht) hDpos.le
  have h5 : (|C| + |K| + 1) * (ε / (2 * (|C| + |K| + 1))) = ε / 2 := by
    field_simp
  have h6 := hN1 u hu t ht
  rw [hsplit]
  have h7 := norm_add_le ((A N - a u • ContinuousLinearMap.id ℂ (H N)) (φ u t N))
    ((A N - a u • ContinuousLinearMap.id ℂ (H N)) (ψ u t N - φ u t N))
  linarith

end General

section Physical

/-- Uniform bound for the physical Wick operators: for balanced `f` and `N ≥ 1`,
`‖physicalWick L N f‖ = ‖W_N(f)‖ ≤ coeffNorm f` (`WHil_norm_le` transported by the unitary
`physicalOccupation`). -/
theorem physicalWick_norm_le (L : ℝ) [Fact (0 < L)] {f : Sym} (hb : Balanced f) :
    ∀ᶠ N in atTop, ‖physicalWick L N f‖ ≤ coeffNorm f := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [norm_eq_of_intertwine (physicalOccupation L N) (physicalWick L N f) (WHil N f)
    (fun v => physicalOccupation_physicalWick L N f v)]
  exact WHil_norm_le hN hb

/-- **One instance (physical Fourier sector).** For balanced `f` and unit `u ∈ L²(𝕋_L)`, the physical
Wick operators have strong symbol `f(û)` on every norm-close normalized preparation `ψ_N` of the product
state `u^{⊗N}`. The product-state limit is `StrongSymbols.strong_symbol_physical`, used unchanged. -/
theorem physical_strongSymbol_normClose (L : ℝ) [Fact (0 < L)] {f : Sym} (hb : Balanced f)
    {u : QuantumNLS.PhysicalTensor.L2T L} (hu : ‖u‖ = 1)
    {ψ : ∀ N, QuantumNLS.PhysicalTensor.physSector L N}
    (hψ : IsNormClosePrep ψ (fun N => QuantumNLS.PhysicalWickLimit.productState L N u)) :
    HasStrongSymbol (H := fun N => QuantumNLS.PhysicalTensor.physSector L N)
      (fun N => physicalWick L N f) ψ
      (QuantumNLS.WickSpectralBridge.evalSym
        ((QuantumNLS.Fourier.fourierL2 L u : QuantumNLS.OccupationUnitary.OneParticle) : ℤ → ℂ) f) := by
  refine hasStrongSymbol_of_normClose (C := coeffNorm f) (physicalWick_norm_le L hb) ?_ hψ.2
  refine Tendsto.congr (fun N => ?_) (QuantumNLS.StrongSymbols.strong_symbol_physical L hb u hu)
  simp

end Physical

/-! Axiom audit (printed at compile time). -/
#print axioms norm_sub_smul_id_apply_le
#print axioms hasStrongSymbol_of_normClose
#print axioms hasUniformStrongSymbol_of_normClose
#print axioms physicalWick_norm_le
#print axioms physical_strongSymbol_normClose

end QuantumNLS.StrongSymbolDef
