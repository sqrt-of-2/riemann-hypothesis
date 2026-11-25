module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem gram_core {R : Type} [CommRing R] (Q : M4 R) (hQ : IsUp Q) (a' d' : R)
    (ha : Q 0 0 * a' = 1) (hd : Q 1 1 * d' = 1)
    (h33 : Q 3 3 = Q 0 0) (h22 : Q 2 2 = Q 1 1) (h23 : Q 2 3 = Q 0 1) (h13 : Q 1 3 = - Q 0 2)
    (h03 : Q 0 3 = 0) (h12 : Q 1 2 = 0) :
    ∃ t : M4 R, IsUp t ∧ adj t * Q * t = 1 := by
  have h10 := hQ 1 0 (by decide)
  have h20 := hQ 2 0 (by decide)
  have h21 := hQ 2 1 (by decide)
  have h30 := hQ 3 0 (by decide)
  have h31 := hQ 3 1 (by decide)
  have h32 := hQ 3 2 (by decide)
  refine ⟨!![a', -(a' * (Q 0 1 * d')), -(a' * Q 0 2), 0; 0, d', 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, h10, h20, h21, h30, h31, h32,
        h33, h22, h23, h13, h03, h12]
    all_goals first
      | linear_combination ha
      | linear_combination hd
      | linear_combination (-(Q 0 1 * d')) * ha
      | linear_combination (-Q 0 2) * ha
      | linear_combination (Q 0 2) * ha

theorem UpperTheory.V.Ws.Pp.gram :
    ∀ {R : Type} [CommRing R] (k : (M4 R)ˣ), IsUp (adj (k : M4 R) * (k : M4 R)) → ∃ t : (M4 R)ˣ, IsUp (t : M4 R) ∧ IsGSp (1 : R) ((k : M4 R) * (t : M4 R)) := by
  intro R _ k hQ
  have hinv : adj (k : M4 R) * adj ((k⁻¹ : (M4 R)ˣ) : M4 R) = 1 := by
    rw [← (grp R).1, Units.inv_mul, (grp R).2.2.2.2.1]
  have hdet : IsUnit (adj (k : M4 R) * (k : M4 R)).det := by
    apply Matrix.isUnit_det_of_right_inverse
      (B := ((k⁻¹ : (M4 R)ˣ) : M4 R) * adj ((k⁻¹ : (M4 R)ˣ) : M4 R))
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (k : M4 R), Units.mul_inv, Matrix.one_mul, hinv]
  rw [Matrix.det_of_isUpperTriangular (fun i j h => hQ i j h), Fin.prod_univ_four] at hdet
  obtain ⟨a', ha⟩ := (isUnit_of_mul_isUnit_left
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))).exists_right_inv
  obtain ⟨d', hd⟩ := (isUnit_of_mul_isUnit_right
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))).exists_right_inv
  obtain ⟨t, ht, htQ⟩ := gram_core _ hQ a' d' ha hd
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn]; ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn]; ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn]; ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn]; ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn]; ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn]; ring)
  refine ⟨⟨t, adj t * (adj (k : M4 R) * (k : M4 R)), mul_eq_one_comm.mp htQ, htQ⟩, ht, ?_⟩
  show adj ((k : M4 R) * t) * ((k : M4 R) * t) = (1 : R) • 1
  rw [(grp R).1, one_smul, ← htQ]
  simp only [Matrix.mul_assoc]
