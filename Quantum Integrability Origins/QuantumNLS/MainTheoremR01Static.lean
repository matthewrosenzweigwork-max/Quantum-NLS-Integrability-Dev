import QuantumNLS.FullWickO2

/-!
# MainTheoremR01Static: part (ii) of R-AF8F7562 `thm:main`, persistence of the uniform static symbols

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex`, line 31: "The strong symbols, support and
projective conclusions persist under uniformly norm-close normalized preparations."

The strong-symbol half is derived here from the accepted R-D2F4CE8F statement `UniformStaticR49b.UniformStatic`
(the uniform Cartesian and unit-phase limits at the product states, simultaneously over the active set), by the
operator-norm bounds `‖E^q‖, ‖W^q‖ ≤ 1` and `|c_{ab}|, |ζ_{ab}| ≤ 1` (FullWickO2): for unit `y` and the product
state `x`, each residual changes by at most `2‖y - x‖`. This is the triangle-inequality argument of the printed
proof of `thm:reconstruction` ("For completeness, the strong-symbol statement itself transfers to the same
preparations"), applied uniformly over the class and the active set. The projective half is the accepted
R-98833BEE statement (used directly in the headline). The support half is NOT derived (see the review record: the
support probabilities are defined only for the product law).

No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.MainTheoremR01Static

open QuantumNLS.UniformStaticR49b (SectorGauge UniformStatic pairs eligible symbol phase cartesianError phaseError
  supMax)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)

variable {L κ : ℝ} [Fact (0 < L)]

/-- A residual of a contraction at a scalar of modulus at most one moves by at most `2‖y - x‖`. -/
theorem residual_shift {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V)
    (hA : ‖A‖ ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) (x y : V) :
    ‖A y - z • y‖ ≤ ‖A x - z • x‖ + 2 * ‖y - x‖ := by
  have hsplit : A y - z • y = (A x - z • x) + (A (y - x) - z • (y - x)) := by
    rw [map_sub, smul_sub]
    abel
  have h2 : ‖A (y - x) - z • (y - x)‖ ≤ 2 * ‖y - x‖ := by
    calc ‖A (y - x) - z • (y - x)‖ ≤ ‖A (y - x)‖ + ‖z • (y - x)‖ := norm_sub_le _ _
      _ ≤ ‖A‖ * ‖y - x‖ + ‖z‖ * ‖y - x‖ := add_le_add (A.le_opNorm _) (norm_smul_le _ _)
      _ ≤ 1 * ‖y - x‖ + 1 * ‖y - x‖ := by gcongr
      _ = 2 * ‖y - x‖ := by ring
  rw [hsplit]
  calc ‖(A x - z • x) + (A (y - x) - z • (y - x))‖
      ≤ ‖A x - z • x‖ + ‖A (y - x) - z • (y - x)‖ := norm_add_le _ _
    _ ≤ ‖A x - z • x‖ + 2 * ‖y - x‖ := by linarith

/-- The operator and adjoint residual pair moves by at most `4‖y - x‖`. -/
theorem pair_shift {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (hA : ‖A‖ ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) (x y : V) :
    ‖A y - z • y‖ + ‖A.adjoint y - conj z • y‖ ≤
      (‖A x - z • x‖ + ‖A.adjoint x - conj z • x‖) + 4 * ‖y - x‖ := by
  have hA' : ‖A.adjoint‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hA
  have hz' : ‖conj z‖ ≤ 1 := by rw [Complex.norm_conj]; exact hz
  have h1 := residual_shift A hA z hz x y
  have h2 := residual_shift A.adjoint hA' (conj z) hz' x y
  linarith

/-- **Persistence of the uniform static strong symbols** (part (ii)). For every fixed `R > 0` and every family
of normalized preparations `ψ'(u)` with `sup_{u ∈ 𝒰_R} ‖ψ'_N(u) - u^{⊗N}‖ → 0`, the Cartesian residuals and
their adjoints vanish uniformly on `𝒰_R`, simultaneously over the active set `I_{j(N)}²`; for every `α > 0` the
unit-phase residuals and their adjoints vanish uniformly over the distinct pairs with both actions `≥ α`. -/
def StaticPersistence (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge) : Prop :=
  ∀ R > 0, ∀ ψ' : L2T L → ∀ n : ℕ, HN L (n + 1),
    (∀ u ∈ RetargetRoughR48b.unitBall (L := L) R, ∀ n, ‖ψ' u n‖ = 1) →
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ‖ψ' u n - UniformStaticR49b.product n u‖ ≤ ε) →
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R, ∀ p ∈ pairs (j (n + 1)),
      ‖UniformStaticR49b.E hκ q n p (ψ' u n) - symbol hκ u p • ψ' u n‖ +
        ‖(UniformStaticR49b.E hκ q n p).adjoint (ψ' u n) - conj (symbol hκ u p) • ψ' u n‖ ≤ ε) ∧
    (∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ p ∈ eligible hκ (j (n + 1)) α u,
      ‖UniformStaticR49b.W hκ q n p (ψ' u n) - (phase hκ u p).1 • ψ' u n‖ +
        ‖(UniformStaticR49b.W hκ q n p).adjoint (ψ' u n) - conj (phase hκ u p).1 • ψ' u n‖ ≤ ε)

theorem static_persistence (hκ : 0 < κ) {j : ℕ → ℕ} {q : SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) : StaticPersistence (L := L) hκ j q := by
  obtain ⟨-, -, -, hcart, hph⟩ := hU
  intro R hR ψ' _ hclose
  constructor
  · intro ε hε
    have hsup := hcart R hR
    filter_upwards [hsup.eventually (gt_mem_nhds (half_pos hε)), hclose (ε / 8) (by positivity)]
      with n hn hc
    intro u hu p hp
    have hu1 : ‖u‖ = 1 := hu.1
    have hle : cartesianError hκ q n u p ≤ supMax (RetargetRoughR48b.unitBall (L := L) R)
        (fun _ => pairs (j (n + 1))) (cartesianError hκ q n) :=
      FullWickO2.le_supMax _ _ _ (by norm_num : (0 : ℝ) ≤ 4)
        (fun v hv p _ => FullWickO2.cartesianError_le_four hκ q n v hv.1 p) hu hp
    have hs := pair_shift (UniformStaticR49b.E hκ q n p) (FullWickO2.norm_E_le hκ q n p) (symbol hκ u p)
      (FullWickO2.norm_symbol_le hκ u hu1 p) (UniformStaticR49b.product n u) (ψ' u n)
    have hc' := hc u hu
    have h0 : cartesianError hκ q n u p ≤ ε / 2 := hle.trans hn.le
    unfold cartesianError at h0
    linarith
  · intro α hα ε hε
    have hsup := (hph R hR α hα).1
    filter_upwards [hsup.eventually (gt_mem_nhds (half_pos hε)), hclose (ε / 8) (by positivity)]
      with n hn hc
    intro u hu p hp
    have hle : phaseError hκ q n u p ≤ supMax (RetargetRoughR48b.unitBall (L := L) R)
        (eligible hκ (j (n + 1)) α) (phaseError hκ q n) :=
      FullWickO2.le_supMax _ _ _ (by norm_num : (0 : ℝ) ≤ 4)
        (fun v hv p _ => FullWickO2.phaseError_le_four hκ q n v hv.1 p) hu hp
    have hs := pair_shift (UniformStaticR49b.W hκ q n p) (FullWickO2.norm_W_le hκ q n p) (phase hκ u p).1
      (FullWickO2.norm_phase hκ u p).le (UniformStaticR49b.product n u) (ψ' u n)
    have hc' := hc u hu
    have h0 : phaseError hκ q n u p ≤ ε / 2 := hle.trans hn.le
    unfold phaseError at h0
    linarith

end QuantumNLS.MainTheoremR01Static

#print axioms QuantumNLS.MainTheoremR01Static.static_persistence
