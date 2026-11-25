import QuantumNLS.TerraMultiRound23GraphSymmetry

/-! Resolvent consequences of the DEF-049 graph symmetries. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round23

theorem liftFiber_sub (L : ℝ) (T : E2 →ₗᵢ[ℝ] E2) (f g : H2 L) :
    liftFiber L T (f - g) = liftFiber L T f - liftFiber L T g := by
  exact map_sub (T.toContinuousLinearMap.compLpₗ 2 (μI L)) f g

theorem liftFiber_swap_smul (L : ℝ) (z : ℂ) (f : H2 L) :
    liftFiber L swapConjIsometry (z • f) = conj z • liftFiber L swapConjIsometry f := by
  rw [Lp.ext_iff]
  filter_upwards [swapConjIsometry.toContinuousLinearMap.coeFn_compLp (z • f),
    swapConjIsometry.toContinuousLinearMap.coeFn_compLp f,
    Lp.coeFn_smul z f, Lp.coeFn_smul (conj z) (liftFiber L swapConjIsometry f)] with x h1 h2 h3 h4
  change (swapConjIsometry.toContinuousLinearMap.compLp (z • f)) x = _
  rw [h1, h4, h3]
  change swapConj (z • (f : ℝ → E2) x) =
    conj z • (swapConjIsometry.toContinuousLinearMap.compLp f) x
  rw [h2]
  ext i
  fin_cases i <;> simp [swapConjIsometry, swapConj, vec2, map_mul]

/-- Whenever the two indicated resolvents exist, the graph involution
intertwines their action at conjugate spectral parameters. -/
theorem resolvent_swap_intertwines (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (z : ℂ)
    (R S : H2 L →L[ℂ] H2 L)
    (hR : IsResolvent L κ u σ z R) (hS : IsResolvent L κ u σ (conj z) S)
    (φ : H2 L) :
    S (liftFiber L swapConjIsometry φ) = liftFiber L swapConjIsometry (R φ) := by
  have hp := graph_swapConj L κ u σ (hR.1 φ)
  rw [liftFiber_sub, liftFiber_swap_smul] at hp
  have hs := hS.2 _ hp
  simpa using hs

end QuantumNLS.LocalSpectral.Round23
#print axioms QuantumNLS.LocalSpectral.Round23.liftFiber_sub
#print axioms QuantumNLS.LocalSpectral.Round23.liftFiber_swap_smul
#print axioms QuantumNLS.LocalSpectral.Round23.resolvent_swap_intertwines
