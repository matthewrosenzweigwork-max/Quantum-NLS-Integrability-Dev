import NlsGge.GK38.GradFundamental
import NlsGge.GK38.DirichletRealAnalytic
import NlsGge.GK38.NeumannLabels

/-! K2 concrete state and independently integrated gradient data.
Private source anchors: GK I.4 Proposition 4.6; I.7 Proposition 7.5,
Lemmas 7.8/7.9 and Proposition 7.10; I.8 Lemma 8.7.
Complex phases use the bilinear Q denominator; energy requires real symmetry. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

abbrev Time := Icc (0 : ℝ) 1

def t0 : Time := ⟨0, le_rfl, zero_le_one⟩

def t1 : Time := ⟨1, zero_le_one, le_rfl⟩

abbrev Normal := ℝ × ℝ

def state (φ : PotPair) (z : ℂ) (a : PairVec38) : PairKernelCont38 :=
  ⟨fun t => a 0 • fundColumn38 φ z t 0 + a 1 • fundColumn38 φ z t 1,
    (((continuous_fundColumn38 φ z 0).const_smul (a 0)).add
      ((continuous_fundColumn38 φ z 1).const_smul (a 1))).comp continuous_subtype_val⟩

def square (w : PairKernelCont38) : PairKernelCont38 :=
  ⟨fun t => starProd38 (w t) (w t), by
    simpa only [starProd38] using
      (show Continuous (fun t : Time => ![(w t 1) * (w t 1), (w t 0) * (w t 0)]) by
        fun_prop)⟩

def Q (w : PairKernelCont38) : ℂ :=
  2 * ∫ s in (0 : ℝ)..1, pairKernelExt38 w s 0 * pairKernelExt38 w s 1

def energy (w : PairKernelCont38) : ℝ :=
  ∫ s in (0 : ℝ)..1, ‖pairKernelExt38 w s 0‖ ^ 2 + ‖pairKernelExt38 w s 1‖ ^ 2

def bilinearGradient (w : PairKernelCont38) : PotPair →L[ℂ] ℂ :=
  (Q w)⁻¹ • integralPairCLM38 (square w) t1

def realEnergyGradient (w : PairKernelCont38) : PhysicalL2 →L[ℝ] ℝ :=
  (energy w)⁻¹ •
    (Complex.reCLM.comp ((integralPairCLM38 (square w) t1).restrictScalars ℝ)).comp realSlice

def dirState (u : PhysicalL2) (n : ℤ) : PairKernelCont38 :=
  state (realSlice u) (gkMu u n : ℂ) ![1, 1]

def nu (u : PhysicalL2) (n : ℤ) : ℝ := gkMu (-u) n

def neuState (u : PhysicalL2) (n : ℤ) : PairKernelCont38 :=
  state (realSlice u) (nu u n : ℂ) ![Complex.I, -Complex.I]

def dirCLM (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  (2 * Complex.I)⁻¹ •
    (fundamentalEntryCLM38 φ z t1 1 0 + fundamentalEntryCLM38 φ z t1 1 1 -
      fundamentalEntryCLM38 φ z t1 0 0 - fundamentalEntryCLM38 φ z t1 0 1)

def dirImplicitGradient (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  -(deriv (dirichletChar φ) z)⁻¹ • dirCLM φ z

def perImplicitGradient (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  -(deriv (discrim φ) z)⁻¹ • gradDiscrimCLM φ z

def parity (n : ℤ) : ℂ := (-1 : ℂ) ^ n

def endpoint (u : PhysicalL2) (n : ℤ) (upper : Bool) : ℝ :=
  if upper then actualGapUpperAllE02_38 u n else actualGapLowerAllE02_38 u n

def Z (n : ℤ) : Set PhysicalL2 :=
  {u | actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n}

def closedEquations (n : ℤ) (u : PhysicalL2) : Normal :=
  (gkMu u n - nu u n, (antiDiscrim (realSlice u) (gkMu u n : ℂ)).re)

def closedDerivative (n : ℤ) (u : PhysicalL2) : PhysicalL2 →L[ℝ] Normal :=
  fderiv ℝ (closedEquations n) u

def potentialInclusion : PotPair →L[ℂ] PotPair × ℂ :=
  ContinuousLinearMap.inl ℂ PotPair ℂ

def floquetSeed01 (φ : PotPair) (z ξ : ℂ) : PairVec38 :=
  ![1, (ξ - monodromyPair φ z 0 0) / monodromyPair φ z 0 1]

def floquetSeed10 (φ : PotPair) (z ξ : ℂ) : PairVec38 :=
  ![(ξ - monodromyPair φ z 1 1) / monodromyPair φ z 1 0, 1]

def normingFactor (φ : PotPair) (z : ℂ) : ℂ :=
  (monodromyPair φ z 0 0 + monodromyPair φ z 0 1 +
    monodromyPair φ z 1 0 + monodromyPair φ z 1 1) / 2

def terminalSeed (φ : PotPair) (z : ℂ) : PairVec38 :=
  ![monodromyPair φ z 0 1 + monodromyPair φ z 1 1,
    -(monodromyPair φ z 0 0 + monodromyPair φ z 1 0)]

def mixedSquare (v w : PairKernelCont38) : PairKernelCont38 :=
  ⟨fun t => starProd38 (v t) (w t), by
    simpa only [starProd38] using
      (show Continuous (fun t : Time => ![(v t 1) * (w t 1), (v t 0) * (w t 0)]) by
        fun_prop)⟩

def normalizedSquare (w : PairKernelCont38) : PairKernelCont38 :=
  (energy w : ℂ)⁻¹ • square w

def closedKernel1 (u : PhysicalL2) (n : ℤ) : PairKernelCont38 :=
  normalizedSquare (dirState u n) - normalizedSquare (neuState u n)

def closedKernel2 (u : PhysicalL2) (n : ℤ) : PairKernelCont38 :=
  spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ) •
    normalizedSquare (dirState u n) + gradAntiDiscrimCont38 (realSlice u) (gkMu u n : ℂ)

def realKernelCLM (w : PairKernelCont38) : PhysicalL2 →L[ℝ] ℝ :=
  (Complex.reCLM.comp ((integralPairCLM38 w t1).restrictScalars ℝ)).comp realSlice

def phasedSeed (upper : Bool) : PairVec38 :=
  if upper then ![1 + Complex.I, 1 - Complex.I] else ![1 - Complex.I, 1 + Complex.I]

end
end NlsGge.GK38.GradEigen38
