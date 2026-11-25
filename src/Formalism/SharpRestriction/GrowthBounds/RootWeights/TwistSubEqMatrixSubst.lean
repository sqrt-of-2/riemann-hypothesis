module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G


open Classical in
def matrixSubst {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) :
    MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) B :=
  open Classical in
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v

section basic

variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

theorem twistSub_eq_matrixSubst (j : Fin n) :
    twistSub (R := R) LL S j = matrixSubst LL S (coefL R n) (twistMat R n j 1) (twistMat R n j (-1)) := rfl

theorem matrixSubst_C (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (c : R) :
    matrixSubst LL S φ m m' (C c) = C (φ c) := by
  simp [matrixSubst]

open Classical in
theorem matrixSubst_X (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (v : ι × Fin n) :
    matrixSubst LL S φ m m' (X v) = if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v := by
  simp [matrixSubst]

theorem matrixSubst_comp (φ : R →+* B) (m1 m1' m2 m2' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m1 m1' (matrixSubst LL S φ m2 m2' F) = matrixSubst LL S φ (m1 * m2) (m2' * m1') F := by
  classical
  have : (matrixSubst LL S (RingHom.id B) m1 m1').comp (matrixSubst LL S φ m2 m2') =
      matrixSubst LL S φ (m1 * m2) (m2' * m1') := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      rw [RingHom.comp_apply, matrixSubst_X, matrixSubst_X]
      by_cases hS : v.1 ∈ S
      · by_cases hv : LL.vec v.1 = true
        · rw [ite_eq_left hS, ite_eq_left hv, ite_eq_left hS, ite_eq_left hv, map_sum]
          have h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2 b v.2) * X (v.1, b)) =
              ∑ a : Fin n, C (m1 a b * m2 b v.2) * X (v.1, a) := by
            intro b
            rw [map_mul, matrixSubst_C, matrixSubst_X, ite_eq_left hS, ite_eq_left hv, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [RingHom.id_apply, map_mul]; ring
          simp only [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_

          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
        · rw [ite_eq_left hS, ite_eq_right hv, ite_eq_left hS, ite_eq_right hv, map_sum]
          have h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2' v.2 b) * X (v.1, b)) =
              ∑ a : Fin n, C (m2' v.2 b * m1' b a) * X (v.1, a) := by
            intro b
            rw [map_mul, matrixSubst_C, matrixSubst_X, ite_eq_left hS, ite_eq_right hv, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [RingHom.id_apply, map_mul]; ring
          simp only [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_

          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      · rw [ite_eq_right hS, ite_eq_right hS, matrixSubst_X, ite_eq_right hS]
  exact congrArg (fun f => f F) this

theorem map_matrixSubst (φ : R →+* B) (ψ : B →+* B') (m m' : Matrix (Fin n) (Fin n) B)
    (F : MvPolynomial (ι × Fin n) R) :
    MvPolynomial.map ψ (matrixSubst LL S φ m m' F) = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) F := by
  classical
  refine congrArg (fun f : MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) B' => f F) (show (MvPolynomial.map ψ).comp (matrixSubst LL S φ m m') = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) from ?_)
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [matrixSubst_C]
  · intro v
    simp only [RingHom.comp_apply, matrixSubst_X]
    split_ifs <;> simp

theorem matrixSubst_one (φ : R →+* B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S φ 1 1 F = MvPolynomial.map φ F := by
  classical
  refine congrArg (fun f : MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) B => f F) ?_
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [matrixSubst_C]
  · intro v
    simp only [matrixSubst_X, map_X]
    split_ifs <;> simp [Matrix.one_apply]

theorem matrixSubst_map (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m m' (MvPolynomial.map φ F) = matrixSubst LL S φ m m' F := by
  rw [← matrixSubst_one LL S, matrixSubst_comp, mul_one, one_mul]

end basic

def TransvectionExpansion : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (a b : Fin n), a ≠ b → ∀ (t : B) (F : MvPolynomial (ι × Fin n) R) (N : ℕ), F.totalDegree < N →
      matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) F =
        ∑ k ∈ Finset.range N, C (t ^ k) * MvPolynomial.map φ (divPow R LL S a b k F)

end Formalism.MainNotions.G.GLWeightTheory
