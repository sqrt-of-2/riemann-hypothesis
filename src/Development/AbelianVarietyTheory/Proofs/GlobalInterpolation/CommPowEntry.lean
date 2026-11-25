module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

namespace GlobalTheory.CommutatorPowerEntry

open Finset

theorem comm_pow_entry (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) :
    ∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b =
      (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A) := by
  induction k with
  | zero =>
    intro a b c d
    simp only [pow_zero, Matrix.one_apply]
    by_cases hcd : c = d <;> by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp_all [eq_comm]
  | succ k ih =>
    intro a b c d
    have h' : ∀ c d : Fin N, E a b * E c d - E c d * E a b =
        (if b = c then E a d else 0) - (if d = a then E c b else 0) := h a b
    have key : ∀ x y : A, E a b * (x * y) - (x * y) * E a b =
        (E a b * x - x * E a b) * y + x * (E a b * y - y * E a b) := by
      intro x y; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key, ih, h']
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, ite_true, ite_false,
      Finset.sum_const_zero] <;> abel

theorem comm_trace_pow (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) (a b : Fin N) :
    E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    comm_pow_entry A N E h k]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem main : ∀ (A : Type) [inst : Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlobalTheory.Alc.GlRel E → ∀ (k : ℕ), (∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A)) ∧ ∀ (a b : Fin N), E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  intro A _ N E h k
  exact ⟨comm_pow_entry A N E h k, comm_trace_pow A N E h k⟩

end GlobalTheory.CommutatorPowerEntry
