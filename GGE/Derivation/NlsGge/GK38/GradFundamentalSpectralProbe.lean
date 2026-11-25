import NlsGge.GK38.GradFundamentalSpectralSeq

/-! # K1 scalar regression probes, including complex and shifted spectral inputs. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem antiDiscrim_zero38 (z : ℂ) : antiDiscrim 0 z = 0 := by
  simp [antiDiscrim, monodromyPair_zero_potential, freeE]

theorem antiDiscrimDeriv_zero38 (z : ℂ) : deriv (antiDiscrim 0) z = 0 := by
  rw [show antiDiscrim 0 = fun _ => (0 : ℂ) from funext antiDiscrim_zero38]
  exact deriv_const z 0

theorem k1_discrimDeriv_zero38 (z : ℂ) : deriv (discrim 0) z = -2 * Complex.sin z := by
  rw [show discrim 0 = fun w => 2 * Complex.cos w from funext discrim_zero]
  convert ((Complex.hasDerivAt_cos z).const_mul 2).deriv using 1 <;> ring

/-- Every shifted complex sequence has identically zero free scalar error. -/
theorem probe_k1_free_shifted_square38 (υ : ℤ → ℂ) :
    k1SquareBound38 (fun n =>
      ‖deriv (discrim 0) (υ n) + 2 * Complex.sin (υ n)‖ ^ 2) 0 ∧
    k1SquareBound38 (fun n => ‖deriv (antiDiscrim 0) (υ n)‖ ^ 2) 0 := by
  constructor <;> apply k1SquareBound38_of_finite
  · intro n; positivity
  · intro T; simp [k1_discrimDeriv_zero38]
  · intro n; positivity
  · intro T; simp [antiDiscrimDeriv_zero38]

/-- The free derivative formula holds on a half-lattice shift with imaginary displacement. -/
theorem probe_k1_nonreal_half_shift38 (n : ℤ) :
    deriv (discrim 0) ((n : ℂ) * Real.pi + Real.pi / 2 + Complex.I) =
      -2 * Complex.sin ((n : ℂ) * Real.pi + Real.pi / 2 + Complex.I) ∧
    deriv (antiDiscrim 0) ((n : ℂ) * Real.pi + Real.pi / 2 + Complex.I) = 0 :=
  ⟨k1_discrimDeriv_zero38 _, antiDiscrimDeriv_zero38 _⟩

end
end NlsGge.GK38
