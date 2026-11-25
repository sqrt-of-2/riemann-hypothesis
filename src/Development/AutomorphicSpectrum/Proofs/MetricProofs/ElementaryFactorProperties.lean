module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
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

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear

variable {N : ℕ}

theorem shear_above {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {x y : Fin N} (hxy : x < y) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y = 0 := by
  rw [SchurCalc.elem_apply, ite_eq_right hxy.ne, ite_eq_right, add_zero]
  rintro ⟨rfl, rfl⟩
  exact lt_asymm hab hxy

theorem shear_diag {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (x : Fin N) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x x = 1 := by
  rw [SchurCalc.elem_apply, ite_eq_left rfl, ite_eq_right, add_zero]
  rintro ⟨rfl, h⟩
  exact hab.ne h

theorem det_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (fun x y h => shear_above hab t h)]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t x

theorem minor_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (S : Finset (Fin N)) :
    minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  have ht : ((1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).submatrix (S.orderEmbOfFin rfl)
      (S.orderEmbOfFin rfl)).BlockTriangular OrderDual.toDual :=
    fun x y h => shear_above hab t ((S.orderEmbOfFin rfl).strictMono h)
  rw [MinorCalc.minorIJ_eq_det _ S S _ rfl rfl, Matrix.det_of_isLowerTriangular _ ht]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t _

theorem support_shear {ca cb : Fin N} (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S) (k c : Fin N)
    (hc : c ∈ S) (hk : k ∉ S) : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) k c = 0 := by
  have hne : k ≠ c := fun e => hk (e ▸ hc)
  rw [SchurCalc.elem_apply, ite_eq_right hne, ite_eq_right, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hk (hS hc)

theorem minor_mul_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (A : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I S = minorIJ A I S := by
  rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ (support_shear t hS), minor_shear hab, mul_one]

theorem minor_gram_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (G h : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ ((h * (1 + Matrix.single cb ca t))ᴴ * G * (h * (1 + Matrix.single cb ca t))) S S =
      minorIJ (hᴴ * G * h) S S := by
  obtain ⟨H, hH⟩ : ∃ H, H = hᴴ * G * h := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℂ, U = 1 + Matrix.single cb ca t := ⟨_, rfl⟩
  have e : (h * U)ᴴ * G * (h * U) = (Uᴴ * H) * U := by
    rw [hH]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← hU, ← hH, e, hU, minor_mul_shear hab t hS, ← hU]
  apply star_injective
  rw [← SchurCalc.minor_conjTranspose, ← SchurCalc.minor_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hU, minor_mul_shear hab t hS]

theorem shear_main : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  intro N j a b ca cb t hj hb hcase hca hcb
  have hab : ca < cb := Fin.lt_def.2 (by omega)
  have ha2 := a.2
  have hb2 := b.2
  have hcb2 := cb.2
  unfold lastCol at hca
  have hblock : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    rcases hcase with h | h
    · rw [ite_eq_left (by omega)] at hca
      omega
    · rw [ite_eq_right (by omega)] at hca
      omega
  have hw : ca ∈ wIdx N j → cb ∈ wIdx N j := by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have ho : ca ∈ omIdx N j → cb ∈ omIdx N j := by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hstep : ∀ i : Fin N, i ≠ a → ca ∈ stepCols N j i → cb ∈ stepCols N j i := by
    intro i hi
    have hia : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
    have hi2 := i.2
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcase with h | h
    · rw [ite_eq_left (by omega)] at hca
      split_ifs <;> omega
    · rw [ite_eq_right (by omega)] at hca
      split_ifs <;> omega
  refine ⟨?_, det_shear hab t, ?_, ?_⟩
  · intro p q hpq
    rw [SchurCalc.elem_apply, ite_eq_right (fun e => hpq (by rw [e])), ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hpq hblock.symm
  · intro h i
    unfold facOf
    rw [minor_mul_shear hab t hw, minor_mul_shear hab t ho]
  · intro G h i hi
    unfold blockPot
    rw [minor_gram_shear hab t (hstep i hi)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear
