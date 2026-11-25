module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneAdr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dilV (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) : Fin n ⊕ Fin n → AE F E :=
  haveI := h.1
  Sum.elim (fun j => if j = i₀ then algebraMap (AF F) (AE F E) (adr w (Real.exp τ)) else 1)
    (fun j => if j = i₀ then algebraMap (AF F) (AE F E) (adr w (Real.exp (-τ))) else 1)

theorem piInf_dilV (h : IsCMExt F E σ) (τ' : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (w u : InfinitePlace F) (i₀ : Fin n)
    (τ : ℝ) (k : Fin n ⊕ Fin n) :
    piInf (τ' u) (dilV h w i₀ τ k) = if u = w then Sum.elim (fun j => ((Real.exp (τ * Pi.single (M := fun _ => ℝ) i₀ 1 j) : ℝ) : ℂ))
      (fun j => ((Real.exp (-(τ * Pi.single (M := fun _ => ℝ) i₀ 1 j)) : ℝ) : ℂ)) k else 1 := by
  have := h.1
  rcases k with j | j
  · simp only [dilV, Sum.elim_inl]
    by_cases h1 : j = i₀
    · subst h1
      rw [ite_eq_left rfl, piInf_adr h τ']
      by_cases h2 : u = w
      · rw [ite_eq_left h2, ite_eq_left h2]; simp
      · rw [ite_eq_right h2, ite_eq_right h2]; simp
    · rw [ite_eq_right h1, map_one]
      split_ifs <;> simp [h1]
  · simp only [dilV, Sum.elim_inr]
    by_cases h1 : j = i₀
    · subst h1
      rw [ite_eq_left rfl, piInf_adr h τ']
      by_cases h2 : u = w
      · rw [ite_eq_left h2, ite_eq_left h2]; simp
      · rw [ite_eq_right h2, ite_eq_right h2]; simp
    · rw [ite_eq_right h1, map_one]
      split_ifs <;> simp [h1]

theorem finOne_dilV (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (k : Fin n ⊕ Fin n) :
    finOne F • dilV h w i₀ τ k = finOne F • (1 : AE F E) := by
  have := h.1
  rcases k with j | j <;> simp only [dilV, Sum.elim_inl, Sum.elim_inr] <;> split_ifs
  · exact finOne_smul_adr h w _
  · rfl
  · exact finOne_smul_adr h w _
  · rfl

end PositivityTheory.SiegelWeilFormula.AStep

end
