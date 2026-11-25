module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.GenDegAlg

theorem isAlgebraic_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (letI := (π.appLE U V h).hom.toAlgebra; Algebra.IsAlgebraic Γ(X, U) Γ(Y, V)) := by
  intro X Y _ _ π hgen hdeg U V hU hV h
  have hη : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hx : π (genericPoint Y) ∈ U := h hη
  let : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V h).hom.toAlgebra
  let : Algebra Γ(X, U) (X.residueField (π (genericPoint Y))) :=
    (X.evaluation U _ hx).hom.toAlgebra
  let : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  let : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hη).hom.toAlgebra
  let : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' rfl
  have hnat : π.appLE U V h ≫ Y.evaluation V _ hη =
      X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y) := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  have : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  have := GlobalTheory.ProjFin.isFractionRing_evaluation X hU hgen hx
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  have : Module.Finite (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  have : Algebra.IsAlgebraic (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (π (genericPoint Y)))).2 inferInstance
  have hinj : Function.Injective (Y.evaluation V _ hη).hom := by
    have h1 := germ_injective_of_isIntegral Y (genericPoint Y) hη
    have h2 : Function.Injective (Y.residue (genericPoint Y)).hom :=
      RingHom.injective (show Y.functionField →+* Y.residueField (genericPoint Y) from
        (Y.residue (genericPoint Y)).hom)
    exact h2.comp h1
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V)
    (Y.residueField (genericPoint Y))) hinj

end GlobalTheory.GenDegAlg
