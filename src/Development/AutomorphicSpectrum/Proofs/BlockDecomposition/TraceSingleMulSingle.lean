module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.TopClass

open PositivityTheory.RgTw

variable {n : ℕ}

theorem trace_single_mul_single (a b c e : Fin n) :
    trace (Matrix.single a b (1 : ℂ) * Matrix.single c e 1) = if a = e ∧ b = c then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : a = e <;> by_cases h2 : b = c <;> simp [h1, h2, ite_and]

theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem trace_hb_mul_hb (p q : Fin n × Fin n) : trace (hb p * hb q) = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, e⟩ := q
  have hs := sqrt_two_inv_sq
  simp only [hb]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 <;>
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_sub, trace_smul, trace_single_mul_single, smul_eq_mul, Prod.mk.injEq] at * <;> (simp only [Fin.ext_iff, Fin.lt_def] at * ; split_ifs at * <;> (try omega)) <;>
  (generalize ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = s at hs ⊢
   have hs2 : s ^ 2 = 1 / 2 := by rw [sq]; exact hs
   first | ring1 | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf))

theorem hb_linInd : LinearIndependent ℂ (hb (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun X => trace (X * hb q)) hg
  simpa [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, trace_hb_mul_hb] using h

def hbB (n : ℕ) : Module.Basis (Fin n × Fin n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' hb hb_linInd (by simp [Module.finrank_matrix])

theorem hbB_apply (p : Fin n × Fin n) : hbB n p = hb p := by
  simp [hbB]

theorem hbB_repr (X : Mat n) (q : Fin n × Fin n) : (hbB n).repr X q = trace (X * hb q) := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp [Finset.sum_mul, Matrix.trace_sum, trace_smul, hbB_apply, trace_hb_mul_hb]

theorem det_of_trace (L : Mat n →ₗ[ℂ] Mat n) :
    (Matrix.of fun p q : Fin n × Fin n => trace (L (hb p) * hb q)).det = LinearMap.det L := by
  rw [← LinearMap.det_toMatrix (hbB n) L, ← Matrix.det_transpose (LinearMap.toMatrix (hbB n) (hbB n) L)]
  congr 1
  ext p q
  simp [LinearMap.toMatrix_apply, hbB_repr, hbB_apply]

end GlobalTheory.CompanionTheory.TopClass
