module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneDilV
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dilV_off (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (k : Fin n ⊕ Fin n)
    (hk : k ∉ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))) : dilV h w i₀ τ k = 1 := by
  have := h.1
  rcases k with j | j
  · have hj : j ≠ i₀ := fun hj => hk (by subst hj; simp)
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [ite_eq_right hj]
  · have hj : j ≠ i₀ := fun hj => hk (by subst hj; simp)
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [ite_eq_right hj]

theorem dilV_mul (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (j : Fin n) :
    dilV h w i₀ τ (Sum.inl j) * dilV h w i₀ τ (Sum.inr j) = 1 := by
  have := h.1
  show (if j = i₀ then _ else (1 : AE F E)) * (if j = i₀ then _ else (1 : AE F E)) = 1
  by_cases hj : j = i₀
  · rw [ite_eq_left hj, ite_eq_left hj, ← map_mul, adr_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      adr_one, map_one]
  · rw [ite_eq_right hj, ite_eq_right hj, mul_one]

theorem dilV_mul' (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (j : Fin n) :
    dilV h w i₀ τ (Sum.inr j) * dilV h w i₀ τ (Sum.inl j) = 1 := by
  rw [mul_comm]
  exact dilV_mul h w i₀ τ j

def dilT (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) : GL (Fin n) (AE F E) :=
  ⟨Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inl j), Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inr j), by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j; exact dilV_mul h w i₀ τ j, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j; exact dilV_mul' h w i₀ τ j⟩

theorem det_dilT (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) :
    haveI := h.1
    Matrix.GeneralLinearGroup.det (dilT h w i₀ τ) = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
  have := h.1
  apply Units.ext
  show (Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inl j)).det =
    algebraMap (AF F) (AE F E) (adr w (Real.exp τ))
  rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
  · show (if i₀ = i₀ then _ else (1 : AE F E)) = _
    rw [ite_eq_left rfl]
  · intro j _ hj
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [ite_eq_right hj]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

end PositivityTheory.SiegelWeilFormula.AStep

end
