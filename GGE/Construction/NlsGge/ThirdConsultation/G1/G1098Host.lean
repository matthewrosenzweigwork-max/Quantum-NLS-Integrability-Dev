import NlsGge.Atomic.G1.G1062
import NlsGge.Sobolev.PeriodicBridge

                                                                                                             
                                                                                                       
                                                                                                                
                                                                                                                            
                                                                                             
                                                                                                        
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open scoped BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

def terminalState (u : PhysicalL2) (n : ℤ) : PairKernelCont38 :=
  state (realSlice u) (gkMu u n : ℂ)
    (terminalSeed (realSlice u) (gkMu u n : ℂ))

def mixedKernel (u v : PhysicalL2) (n : ℤ) (minus : Bool) : PairKernelCont38 :=
  if minus then Complex.I •
    (mixedSquare (dirState u n) (terminalState v n) +
      mixedSquare (dirState v n) (terminalState u n))
  else mixedSquare (dirState u n) (dirState v n)

def mixedReference (n : ℤ) (minus : Bool) : PhysicalL2 :=
  reflectedFourierL2.symm
    (lp.single 2 (-n) (if minus then 2*Complex.I*parity n else -1))

def mixedColumn (u v : PhysicalL2) (n : ℤ) (minus : Bool) : PhysicalL2 :=
  (pairKernelL2Class38 (mixedKernel u v n minus)).1

def mixedSquaredOperator (u v : PhysicalL2) : PhysicalL2 →L[ℝ] PhysicalL2 :=
  if h : ∃ A : PhysicalL2 →L[ℝ] PhysicalL2,
      ∀ n : ℤ, ∀ minus : Bool, A (mixedReference n minus) = mixedColumn u v n minus
  then Classical.choose h else 0

def complexTerminalState (φ : PotPair) (n : ℤ) :
    PairKernelCont38 :=
  state φ (muSeq φ n) (terminalSeed φ (muSeq φ n))

def complexMixedKernel (φ ψ : PotPair) (n : ℤ)
    (minus : Bool) : PairKernelCont38 :=
  if minus then Complex.I •
    (mixedSquare (complexDirState φ n) (complexTerminalState ψ n) +
      mixedSquare (complexDirState ψ n) (complexTerminalState φ n))
  else mixedSquare (complexDirState φ n) (complexDirState ψ n)

def complexMixedColumn (φ ψ : PotPair) (n : ℤ)
    (minus : Bool) : PhysicalL2 :=
  (pairKernelL2Class38 (complexMixedKernel φ ψ n minus)).1

end
end NlsGge.GKDefinitionDesign
