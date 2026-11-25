module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation, Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution, Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta, Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation", "h": "module\n\npublic import Mathlib.GroupTheory.SemidirectProduct\npublic import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, hb]
  · simp

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat]
  refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro rfl <;> simp

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g) = g := by
  intro m R _ g
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl]
  rw [mul_assoc, mul_assoc, mul_assoc, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, mul_one, ← mul_assoc,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g * UpperTheory.Reformulated.B.AntidiagonalConjugation.theta h := by
  intro m R _ g h
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m), UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact ite_eq_left rfl

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left *
          ((UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h * r g * (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h)⁻¹).left = _
  rw [← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, one_mul,
    MulAut.one_apply]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation =====

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution", "h": "module\n\npublic import Mathlib.GroupTheory.SemidirectProduct\npublic import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m * UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, hb]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m, inv := UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m, val_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m,
        inv_val := UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux4 g,
        inv_val := UpperTheory.Reformulated.B.ConjugationByInvolution.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m * UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g * UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m * UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m)

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (g * h) = UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g * UpperTheory.Reformulated.B.ConjugationByInvolution.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose
    = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g) = g :=
  Units.ext rfl

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m) = UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m).transpose = UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m
  ext i j
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> (rintro rfl; simp)
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, this]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.ConjugationByInvolution.theta (UpperTheory.Reformulated.B.ConjugationByInvolution.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.ConjugationByInvolution.theta
  rw [UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul, UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul, UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_Jgl,
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_trInv, ← mul_assoc, ← mul_assoc, UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, one_mul,
    mul_assoc, UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, mul_one]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.ConjugationByInvolution.theta (g * h) = UpperTheory.Reformulated.B.ConjugationByInvolution.theta g * UpperTheory.Reformulated.B.ConjugationByInvolution.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.ConjugationByInvolution.theta
  rw [UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m) (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m), UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, one_mul]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.ConjugationByInvolution.theta, invFun := UpperTheory.Reformulated.B.ConjugationByInvolution.theta, left_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux8,
        right_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux8, map_mul' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact ite_eq_left rfl

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R * UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.ConjugationByInvolution.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux11 m R, map_mul' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.ConjugationByInvolution.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) → G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R → MulAut (UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R))
              ((UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy_right :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy h r : G → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) g).right = ((r : G → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) g).right := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL h * r g * (UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL h)⁻¹ : UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R).right = _
  rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    SemidirectProduct.right_inl, inv_one, one_mul, mul_one]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution =====

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta", "h": "module\n\npublic import Mathlib.GroupTheory.SemidirectProduct\npublic import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.SignActionTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.SignActionTheta.Jmat R m * UpperTheory.Reformulated.B.SignActionTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [UpperTheory.Reformulated.B.SignActionTheta.Jmat, Matrix.mul_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.rev_rev, Matrix.one_apply]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, inv := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.SignActionTheta.J_mul_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.SignActionTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (g * h) = UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.SignActionTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.SignActionTheta.Jmat]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl <;> rw [h, Fin.rev_rev]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.SignActionTheta.theta (UpperTheory.Reformulated.B.SignActionTheta.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv,
    UpperTheory.Reformulated.B.SignActionTheta.trInv_J]
  simp only [← mul_assoc]
  rw [UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul, mul_assoc, UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, mul_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.SignActionTheta.theta (g * h) = UpperTheory.Reformulated.B.SignActionTheta.theta g * UpperTheory.Reformulated.B.SignActionTheta.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.trInv h * _),
    UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.SignActionTheta.theta, invFun := UpperTheory.Reformulated.B.SignActionTheta.theta, left_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact ite_eq_left rfl

theorem UpperTheory.Reformulated.B.SignActionTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · rw [ite_eq_left (by simp), ite_eq_right hne]
    ext1 g
    exact (UpperTheory.Reformulated.B.SignActionTheta.aux8 g).symm

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.SignActionTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R] ℤˣ

private theorem UpperTheory.Reformulated.B.SignActionTheta.map_theta {m : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.theta g) =
      UpperTheory.Reformulated.B.SignActionTheta.theta (Matrix.GeneralLinearGroup.map f g) := by
  have hJ : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl S m := by
    ext i j
    change f (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m i j) = UpperTheory.Reformulated.B.SignActionTheta.Jmat S m i j
    unfold UpperTheory.Reformulated.B.SignActionTheta.Jmat
    split_ifs <;> simp
  have hT : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.trInv g) =
      UpperTheory.Reformulated.B.SignActionTheta.trInv (Matrix.GeneralLinearGroup.map f g) := by
    ext i j
    rfl
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [map_mul, map_mul, hJ, hT]

theorem UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm.{u_1, u_2} :
    ∀ {m : ℕ} {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S) (s : ℤˣ),
      (Matrix.GeneralLinearGroup.map f).comp
          (MulEquiv.toMonoidHom ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) s)) =
        (MulEquiv.toMonoidHom
              ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S : ℤˣ → MulAut (GL (Fin m) S)) ((MonoidHom.id ℤˣ : ℤˣ → ℤˣ) s))).comp
          (Matrix.GeneralLinearGroup.map f) := by
  intro m R S _ _ f s
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · ext1 g
    simp
  · have h1 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R :=
      ite_eq_right (t := (1 : MulAut (GL (Fin m) R))) hne
    have h2 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m S :=
      ite_eq_right (t := (1 : MulAut (GL (Fin m) S))) hne
    rw [MonoidHom.id_apply, h1, h2]
    refine MonoidHom.ext fun g => ?_
    exact UpperTheory.Reformulated.B.SignActionTheta.map_theta f g

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.map.{u_1, u_2} :
    {m : ℕ} →
      {R : Type u_1} →
        {S : Type u_2} →
          [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → UpperTheory.Reformulated.B.SignActionTheta.GG m R →* UpperTheory.Reformulated.B.SignActionTheta.GG m S :=
    fun {m : ℕ} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] (f : R →+* S) ↦
      SemidirectProduct.map (Matrix.GeneralLinearGroup.map f) (MonoidHom.id ℤˣ) (UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm f)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) → G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.SignActionTheta.GG m R → MulAut (UpperTheory.Reformulated.B.SignActionTheta.GG m R))
              ((UpperTheory.Reformulated.B.SignActionTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.SignActionTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.SignActionTheta.map_conjBy :
    ∀ {G R S : Type} [inst : Group G] [inst_1 : CommRing R] [inst_2 : CommRing S] {m : ℕ} (f : R →+* S) (h : GL (Fin m) R)
      (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R),
      (UpperTheory.Reformulated.B.SignActionTheta.map f).comp (UpperTheory.Reformulated.B.SignActionTheta.conjBy h r) =
        UpperTheory.Reformulated.B.SignActionTheta.conjBy ((Matrix.GeneralLinearGroup.map f : GL (Fin m) R → GL (Fin m) S) h)
          ((UpperTheory.Reformulated.B.SignActionTheta.map f).comp r) := by
  intro G R S _ _ _ m f h r
  refine MonoidHom.ext fun x => ?_
  have hi : UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h) =
      UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) :=
    SemidirectProduct.map_inl _ _ _ h
  change UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h * r x * (UpperTheory.Reformulated.B.SignActionTheta.ofGL h)⁻¹) =
    UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) * UpperTheory.Reformulated.B.SignActionTheta.map f (r x) *
      (UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h))⁻¹
  rw [map_mul, map_mul, map_inv, hi]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.Padics.LocalField\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Topology

namespace UpperTheory.V.Loc.OrdinaryDeformation

section Group

variable {G R S T U : Type} [Group G] [CommRing R] [CommRing S] [CommRing T] [CommRing U] {m : ℕ}

theorem map_conjBy (f : R →+* S) (h : GL (Fin m) R) (r : G →* GG (m := m) (R := R)) :
    (GG.map f).comp (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) :=
  _root_.UpperTheory.Reformulated.B.SignActionTheta.map_conjBy f h r

theorem conjBy_one (r : G →* GG (m := m) (R := R)) : conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy]

theorem conjBy_inv_conjBy (h : GL (Fin m) R) (r : G →* GG (m := m) (R := R)) :
    conjBy h⁻¹ (conjBy h r) = r := by
  refine MonoidHom.ext fun g => ?_
  change GG.ofGL h⁻¹ * (GG.ofGL h * r g * (GG.ofGL h)⁻¹) * (GG.ofGL h⁻¹)⁻¹ = r g
  rw [map_inv]
  group

theorem conjBy_right (h : GL (Fin m) R) (r : G →* GG (m := m) (R := R)) (g : G) :
    (conjBy h r g).right = (r g).right :=
  _root_.UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy_right h r g

theorem conjBy_left (h : GL (Fin m) R) (r : G →* GG (m := m) (R := R)) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left h r g

theorem gg_ext (f₁ : R →+* S) (f₂ : R →+* T) (hf : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    {x y : GG (m := m) (R := R)}
    (h₁ : GG.map f₁ x = GG.map f₁ y) (h₂ : GG.map f₂ x = GG.map f₂ y) : x = y :=
  SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => hf _ _
    (congrFun (congrFun (congrArg GG.mat h₁) a) b) (congrFun (congrFun (congrArg GG.mat h₂) a) b)))
    (congrArg SemidirectProduct.right h₁ :)

theorem glue_GL (f₁ : R →+* S) (f₂ : R →+* T) (q₁ : S →+* U) (q₂ : T →+* U)
    (hf : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    (hq : ∀ s t, q₁ s = q₂ t → ∃ x, f₁ x = s ∧ f₂ x = t) (n₁ : GL (Fin m) S) (n₂ : GL (Fin m) T)
    (h : Matrix.GeneralLinearGroup.map q₁ n₁ = Matrix.GeneralLinearGroup.map q₂ n₂) :
    ∃ n : GL (Fin m) R, Matrix.GeneralLinearGroup.map f₁ n = n₁ ∧ Matrix.GeneralLinearGroup.map f₂ n = n₂ := by
  have h' : Matrix.GeneralLinearGroup.map q₁ n₁⁻¹ = Matrix.GeneralLinearGroup.map q₂ n₂⁻¹ := by
    rw [map_inv, map_inv, h]
  choose X hX1 hX2 using fun a b => hq ((n₁ : Matrix (Fin m) (Fin m) S) a b) ((n₂ : Matrix (Fin m) (Fin m) T) a b)
    (congrArg (fun x : GL (Fin m) U => (x : Matrix (Fin m) (Fin m) U) a b) h)
  choose Y hY1 hY2 using fun a b => hq (((n₁⁻¹ : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) a b)
    (((n₂⁻¹ : GL (Fin m) T) : Matrix (Fin m) (Fin m) T) a b)
    (congrArg (fun x : GL (Fin m) U => (x : Matrix (Fin m) (Fin m) U) a b) h')
  have x1 : (Matrix.of X).map f₁ = n₁ := Matrix.ext hX1
  have x2 : (Matrix.of X).map f₂ = n₂ := Matrix.ext hX2
  have y1 : (Matrix.of Y).map f₁ = (n₁⁻¹ : GL (Fin m) S) := Matrix.ext hY1
  have y2 : (Matrix.of Y).map f₂ = (n₂⁻¹ : GL (Fin m) T) := Matrix.ext hY2
  have hM : ∀ A B : Matrix (Fin m) (Fin m) R, A.map f₁ = B.map f₁ → A.map f₂ = B.map f₂ → A = B :=
    fun A B h1 h2 => Matrix.ext fun a b => hf _ _ (congrFun (congrFun h1 a) b) (congrFun (congrFun h2 a) b)
  refine ⟨⟨Matrix.of X, Matrix.of Y, hM _ _ ?_ ?_, hM _ _ ?_ ?_⟩, Units.ext x1, Units.ext x2⟩
  · rw [Matrix.map_mul, x1, y1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, x2, y2, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, x1, y1, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, x2, y2, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem glue_hom (f₁ : R →+* S) (f₂ : R →+* T) (q₁ : S →+* U) (q₂ : T →+* U)
    (hf : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    (hq : ∀ s t, q₁ s = q₂ t → ∃ x, f₁ x = s ∧ f₂ x = t)
    (r₁ : G →* GG (m := m) (R := S)) (r₂ : G →* GG (m := m) (R := T))
    (h : (GG.map q₁).comp r₁ = (GG.map q₂).comp r₂) :
    ∃ r : G →* GG (m := m) (R := R), (GG.map f₁).comp r = r₁ ∧ (GG.map f₂).comp r = r₂ := by
  have hg : ∀ g, GG.map q₁ (r₁ g) = GG.map q₂ (r₂ g) := fun g => DFunLike.congr_fun h g
  choose n h1 h2 using fun g => glue_GL f₁ f₂ q₁ q₂ hf hq (r₁ g).left (r₂ g).left
    (congrArg SemidirectProduct.left (hg g))
  let x : G → GG (m := m) (R := R) := fun g => ⟨n g, (r₁ g).right⟩
  have e1 : ∀ g, GG.map f₁ (x g) = r₁ g := fun g => SemidirectProduct.ext (h1 g) rfl
  have e2 : ∀ g, GG.map f₂ (x g) = r₂ g := fun g =>
    SemidirectProduct.ext (h2 g) (congrArg SemidirectProduct.right (hg g) :)
  refine ⟨MonoidHom.mk' x fun g g' => gg_ext f₁ f₂ hf ?_ ?_, MonoidHom.ext e1, MonoidHom.ext e2⟩
  · rw [map_mul, e1, e1, e1, map_mul]
  · rw [map_mul, e2, e2, e2, map_mul]

theorem congOne_iff (f : R →+* S) (n : GL (Fin m) R) :
    CongOne (RingHom.ker f) n ↔ Matrix.GeneralLinearGroup.map f n = 1 := by
  have e : ∀ a b, f (((n : Matrix (Fin m) (Fin m) R) - 1) a b) =
      (Matrix.GeneralLinearGroup.map f n : Matrix (Fin m) (Fin m) S) a b - (1 : Matrix (Fin m) (Fin m) S) a b := by
    intro a b
    rw [Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    congr 1
    split_ifs <;> simp
  refine ⟨fun h => Units.ext (Matrix.ext fun a b => sub_eq_zero.1 ((e a b).symm.trans (h a b))), fun h a b => ?_⟩
  rw [RingHom.mem_ker, e, h, Units.val_one, sub_self]

theorem map_sub_one (f : R →+* S) (n : GL (Fin m) R) (a b : Fin m) :
    ((Matrix.GeneralLinearGroup.map f n : Matrix (Fin m) (Fin m) S) - 1) a b =
      f (((n : Matrix (Fin m) (Fin m) R) - 1) a b) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
  congr 1
  split_ifs <;> simp

theorem lift_lower (f : R →+* S) (hf : Function.Surjective f)
    (n' : GL (Fin 3) S) (hn : ∀ a b, 0 ≤ wt a b → ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b = 0) :
    ∃ n : GL (Fin 3) R, (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) R) - 1) a b = 0) ∧
      Matrix.GeneralLinearGroup.map f n = n' := by
  have hX : ∀ a b, ∃ x : R, (0 ≤ wt a b → x = 0) ∧ f x = ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b := by
    intro a b
    by_cases h : 0 ≤ wt a b
    · exact ⟨0, fun _ => rfl, by rw [map_zero, hn a b h]⟩
    · obtain ⟨x, hx⟩ := hf (((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b)
      exact ⟨x, fun h' => absurd h' h, hx⟩
  choose X h0 hX using hX
  have hd : (Matrix.of X + 1).det = 1 := by
    have h00 := h0 0 0 (by decide)
    have h01 := h0 0 1 (by decide)
    have h02 := h0 0 2 (by decide)
    have h11 := h0 1 1 (by decide)
    have h12 := h0 1 2 (by decide)
    have h22 := h0 2 2 (by decide)
    simp [Matrix.det_fin_three, h00, h01, h02, h11, h12, h22]
  refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.of X + 1) (by rw [hd]; exact isUnit_one), fun a b h => ?_, ?_⟩
  · change (Matrix.of X + 1 - 1) a b = 0
    rw [add_sub_cancel_right]
    exact h0 a b h
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change f ((Matrix.of X + 1) a b) = _
    rw [Matrix.add_apply, map_add (f := _), Matrix.of_apply, hX, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end Group

section Cont

variable {l : ℕ} [Fact l.Prime] {X : Type} [TopologicalSpace X]

theorem qcont_map {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W] [Module ℚ_[l] W]
    (f : V →ₗ[ℚ_[l]] W) {c : X → V} (h : QCont l c) : QCont l fun x => f (c x) := by
  let : TopologicalSpace V := moduleTopology ℚ_[l] V
  have : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  let : TopologicalSpace W := moduleTopology ℚ_[l] W
  have : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  have : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp h

theorem qcont_pair {V W W' : Type} [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W] [Module ℚ_[l] W]
    [AddCommGroup W'] [Module ℚ_[l] W'] (f : V →ₗ[ℚ_[l]] W) (f' : V →ₗ[ℚ_[l]] W')
    (hf : ∀ x y, f x = f y → f' x = f' y → x = y) {c : X → V} (h : QCont l fun x => f (c x))
    (h' : QCont l fun x => f' (c x)) : QCont l c := by
  obtain ⟨L, hL⟩ := (f.prod f').exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun x y e =>
    hf x y (congrArg Prod.fst e) (congrArg Prod.snd e))
  have h1 := qcont_map (L.comp (LinearMap.inl _ _ _)) h
  have h2 := qcont_map (L.comp (LinearMap.inr _ _ _)) h'
  let : TopologicalSpace V := moduleTopology ℚ_[l] V
  have : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h3 := Continuous.add (M := V) h1 h2
  have e : (fun x => (L.comp (LinearMap.inl _ _ _)) (f (c x)) + (L.comp (LinearMap.inr _ _ _)) (f' (c x))) = c := by
    funext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_add (f := _)]
    simpa using LinearMap.congr_fun hL (c x)
  rw [← e]
  exact h3

theorem cont_col {G B : Type} [Group G] [TopologicalSpace G] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (r : G →* GL (Fin 3) B) (h : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b) :
    ContAction (colRep r) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_pi fun a => ?_
  change Continuous fun p : G × (Fin 3 → B) => ∑ b, (r p.1 : Matrix (Fin 3) (Fin 3) B) a b * p.2 b
  exact continuous_finsetSum _ fun b _ => ((h a b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd)

end Cont

section Cr

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)

theorem eta_open : IsOpen (D.η.ker : Set (GQ l)) := by
  have e : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
  have := D.Kv.2
  rw [e]
  exact IntermediateField.fixingSubgroup_isOpen D.Kv.1

theorem eta_lc : IsLocallyConstant D.η := by
  refine IsLocallyConstant.iff_isOpen_fiber_apply.2 fun x => ?_
  have e : D.η ⁻¹' {D.η x} = (fun g => x⁻¹ * g) ⁻¹' (D.η.ker : Set (GQ l)) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      inv_mul_eq_one]
    exact eq_comm
  rw [e]
  exact (eta_open D).preimage (continuous_const.mul continuous_id)

theorem HL_emb : IsOpenEmbedding D.HL.subtype :=
  IsOpen.isOpenEmbedding_subtypeVal ((eta_open D).inter D.τ_open)

variable {D} {B B' C E : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
  [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C]
  [CommRing E] {r₁ : GQ l →* GG (m := 3) (R := E)}

theorem dcr_map (f : B →ₐ[ℚ_[l]] B') (hf : Function.Surjective f) {π : B →+* E} {π' : B' →+* E}
    (hπ : π'.comp (f : B →+* B') = π) {r : GQ l →* GG (m := 3) (R := B)} (hr : D.InDcrAt π r₁ r) :
    D.InDcrAt π' r₁ ((GG.map (f : B →+* B')).comp r) := by
  have hc : ∀ a b, QCont l fun g => (((GG.map (f : B →+* B')).comp r) g).mat a b := fun a b =>
    qcont_map f.toLinearMap (hr.cont a b)
  refine ⟨hr.mult, ?_, hc, ?_⟩
  · rw [← hr.red, ← hπ]; rfl
  obtain ⟨ρ, hρ, hcr⟩ := hr.cr
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  let : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  have : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  have : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  refine ⟨(Matrix.GeneralLinearGroup.map (f : B →+* B')).comp ρ, fun g => by rw [MonoidHom.comp_apply, hρ]; rfl, ?_⟩
  refine ((isCrys_isDR_sub_quot _ (HL_emb D) (colRep ρ) _ (cont_col _ fun a b => ?_) (cont_col _ fun a b => ?_)
    (f.toLinearMap.compLeft (Fin 3)) fun g x => ?_).2 (fun y => ?_)).1 hcr
  · simp only [hρ]
    exact Continuous.comp (hr.cont a b) continuous_subtypeVal
  · simp only [MonoidHom.comp_apply, hρ]
    exact (Continuous.comp (hc a b) (continuous_subtypeVal (p := fun g => g ∈ D.HL)) :)
  · funext a
    exact RingHom.map_mulVec (f : B →+* B') _ x a
  · choose x hx using fun a => hf (y a)
    exact ⟨x, funext hx⟩

theorem dcr_pair (f : C →ₐ[ℚ_[l]] B) (f' : C →ₐ[ℚ_[l]] B') (hf : ∀ x y, f x = f y → f' x = f' y → x = y)
    {π : B →+* E} {π' : B' →+* E} {r : GQ l →* GG (m := 3) (R := C)}
    (hr : D.InDcrAt π r₁ ((GG.map (f : C →+* B)).comp r))
    (hr' : D.InDcrAt π' r₁ ((GG.map (f' : C →+* B')).comp r)) : D.InDcrAt (π.comp (f : C →+* B)) r₁ r := by
  have hc : ∀ a b, QCont l fun g => (r g).mat a b := fun a b =>
    qcont_pair f.toLinearMap f'.toLinearMap hf (hr.cont a b) (hr'.cont a b)
  have hm : HasMult D.η r := hr.mult
  refine ⟨hm, hr.red, hc, ?_⟩
  obtain ⟨ρ, hρ, hcr⟩ := hr.cr
  obtain ⟨ρ', hρ', hcr'⟩ := hr'.cr
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  let : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  have : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  have : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  let : TopologicalSpace C := moduleTopology ℚ_[l] C
  have : IsModuleTopology ℚ_[l] C := ⟨rfl⟩
  have : IsTopologicalRing C := IsModuleTopology.isTopologicalRing ℚ_[l] C
  have c1 : ContAction (resCoef ℚ_[l] (colRep ρ)) := cont_col ρ fun a b => by
    simp only [hρ]
    exact (Continuous.comp (hr.cont a b) (continuous_subtypeVal (p := fun g => g ∈ D.HL)) :)
  have c2 : ContAction (resCoef ℚ_[l] (colRep ρ')) := cont_col ρ' fun a b => by
    simp only [hρ']
    exact (Continuous.comp (hr'.cont a b) (continuous_subtypeVal (p := fun g => g ∈ D.HL)) :)
  have c3 : ContAction ((resCoef ℚ_[l] (colRep ρ)).prod (resCoef ℚ_[l] (colRep ρ'))) :=
    (Continuous.comp c1 (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (Continuous.comp c2 (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hp := (isCrys_isDR_prod _ (HL_emb D) _ _ c1 c2).1 hcr hcr'
  refine ⟨(glPart D.η r hm).comp (Subgroup.inclusion inf_le_left), fun g => rfl, ?_⟩
  refine ((isCrys_isDR_sub_quot _ (HL_emb D) _ _ (cont_col _ fun a b => ?_) c3
    ((f.toLinearMap.compLeft (Fin 3)).prod (f'.toLinearMap.compLeft (Fin 3))) fun g x => ?_).1
    (fun x y h => ?_)).1 hp
  · exact Continuous.comp (hc a b) continuous_subtypeVal
  · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · change _ = Matrix.mulVec (ρ g : Matrix (Fin 3) (Fin 3) B) _ a
      rw [hρ]
      exact RingHom.map_mulVec (f : C →+* B) _ x a
    · change _ = Matrix.mulVec (ρ' g : Matrix (Fin 3) (Fin 3) B') _ a
      rw [hρ']
      exact RingHom.map_mulVec (f' : C →+* B') _ x a
  · exact funext fun a => hf _ _ (congrFun (congrArg Prod.fst h) a) (congrFun (congrArg Prod.snd h) a)

theorem dcr_conj {π : B →+* E} {r : GQ l →* GG (m := 3) (R := B)} (hr : D.InDcrAt π r₁ r) (n : GL (Fin 3) B)
    (hn : Matrix.GeneralLinearGroup.map π n = 1) : D.InDcrAt π r₁ (conjBy n r) := by
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  have hm : HasMult D.η (conjBy n r) := fun g => (conjBy_right n r g).trans (hr.mult g)
  have h0 : Continuous fun g => (r g).mat := continuous_matrix fun a b => hr.cont a b
  have hc : Continuous fun g => (conjBy n r g).mat := by
    have e : (fun g => (conjBy n r g).mat) = fun g => (n : Matrix (Fin 3) (Fin 3) B) * (r g).mat *
        ((sgnAct 3 B (D.η g) n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) := by
      funext g
      rw [GG.mat, conjBy_left, hr.mult g]
      rfl
    rw [e]
    exact (continuous_const.mul h0).mul (IsLocallyConstant.comp (eta_lc D)
      fun s => ((sgnAct 3 B s n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).continuous
  refine ⟨hm, by rw [map_conjBy, hn, conjBy_one, hr.red], fun a b => hc.matrix_elem a b, ?_⟩
  obtain ⟨ρ, hρ, hcr⟩ := hr.cr
  have hv : ∀ g : D.HL, conjGL n ρ g = (conjBy n r g).left := fun g => by
    rw [conjBy_left, hr.mult g, show D.η g = 1 from g.2.1, sgnAct_one, ← hρ]
    rfl
  refine ⟨conjGL n ρ, hv, ?_⟩
  refine ((isCrys_isDR_sub_quot _ (HL_emb D) (colRep ρ) _ (cont_col _ fun a b => ?_) (cont_col _ fun a b => ?_)
    ((Matrix.toLin' (n : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) fun g x => ?_).2 (fun y => ?_)).1 hcr
  · simp only [hρ]
    exact Continuous.comp (hr.cont a b) continuous_subtypeVal
  · simp only [hv]
    exact Continuous.comp (hc.matrix_elem a b) continuous_subtypeVal
  · change Matrix.mulVec (n : Matrix (Fin 3) (Fin 3) B) (Matrix.mulVec (ρ g : Matrix (Fin 3) (Fin 3) B) x) =
      Matrix.mulVec ((n * ρ g * n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
        (Matrix.mulVec (n : Matrix (Fin 3) (Fin 3) B) x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  · refine ⟨Matrix.mulVec ((n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) y, ?_⟩
    change Matrix.mulVec (n : Matrix (Fin 3) (Fin 3) B) (Matrix.mulVec _ y) = y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

variable [Algebra O E]

theorem dcr_of_dord {π : B →+* E} {r : GQ l →* GG (m := 3) (R := B)} (hr : D.InDord π r) : D.InDcr π r := by
  obtain ⟨u, n, hu, hn, -, rfl⟩ := hr
  exact dcr_conj hu.toInDcrAt n ((congOne_iff π n).1 hn)

theorem dord_map (f : B →ₐ[ℚ_[l]] B') (hf : Function.Surjective f) {π : B →+* E} {π' : B' →+* E}
    (hπ : π'.comp (f : B →+* B') = π) {r : GQ l →* GG (m := 3) (R := B)} (hr : D.InDord π r) :
    D.InDord π' ((GG.map (f : B →+* B')).comp r) := by
  obtain ⟨u, n, hu, hn, hn', rfl⟩ := hr
  refine ⟨(GG.map (f : B →+* B')).comp u, Matrix.GeneralLinearGroup.map (f : B →+* B') n,
    ⟨dcr_map f hf hπ hu.toInDcrAt, fun g a b h => ?_⟩, fun a b => ?_, fun a b h => ?_, map_conjBy _ n u⟩
  · change (f : B →+* B') ((u g).mat a b) = 0
    rw [hu.tri g a b h, map_zero]
  · rw [map_sub_one, RingHom.mem_ker, ← RingHom.comp_apply, hπ]
    exact hn a b
  · rw [map_sub_one, hn' a b h, map_zero]

end Cr

end UpperTheory.V.Loc.OrdinaryDeformation
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation =====
