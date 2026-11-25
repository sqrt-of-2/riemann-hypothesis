module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option autoImplicit false

private theorem isIntegral_map_iff {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (B : Subalgebra ℂ K) (y : L) :
    IsIntegral (B.map (IsScalarTower.toAlgHom ℂ K L)) y ↔ IsIntegral B y := by
  let j := IsScalarTower.toAlgHom ℂ K L
  let e : B →+* B.map j := (B.equivMapOfInjective j j.toRingHom.injective).toAlgHom.toRingHom
  let : Algebra B (B.map j) := e.toAlgebra
  have : IsScalarTower B (B.map j) L := .of_algebraMap_eq fun a => rfl
  have : Algebra.IsIntegral B (B.map j) := ⟨fun b => by
    obtain ⟨a, rfl⟩ := (B.equivMapOfInjective j j.toRingHom.injective).surjective b
    exact isIntegral_algebraMap (x := a)⟩
  exact ⟨fun h => isIntegral_trans y h, fun h => h.tower_top⟩

private theorem dualNumberPoint_preimage_top_of_reduction {d : ℕ} {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] {c : Y ⟶ Z} (hc : c ≫ s = s') [IsFinite c] [Etale c]
    [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s')
    (j : Z.functionField →ₐ[ℂ] Y.functionField)
    (hj : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      j ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g))
    {F : Type} [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField]
    (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x)
    (hU : IsAffCover s U (rB ℂ Z.functionField x)) :
    IsAffCover s' (fun i => c ⁻¹ᵁ U i) (R2 x j) := by
  let : Algebra Z.functionField Y.functionField := j.toRingHom.toAlgebra
  let : Algebra F Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  have : IsScalarTower ℂ Z.functionField Y.functionField := .of_algebraMap_eq fun r => (j.commutes r).symm
  have : IsScalarTower F Z.functionField Y.functionField := .of_algebraMap_eq fun r => rfl
  have : IsScalarTower ℂ F Y.functionField := .of_algebraMap_eq fun r => by
    change algebraMap ℂ Y.functionField r = j (algebraMap F Z.functionField (algebraMap ℂ F r))
    rw [← IsScalarTower.algebraMap_apply ℂ F Z.functionField, j.commutes]
  have hjeq : IsScalarTower.toAlgHom ℂ Z.functionField Y.functionField = j := AlgHom.ext fun _ => rfl
  have e : rB ℂ Y.functionField x = R2 x j := by
    funext I
    ext y
    change IsIntegral (rA ℂ x I) y ↔ IsIntegral ((rB ℂ Z.functionField x I).map j) y
    rw [UpperTheory.A.isIntegral_rB_iff (K := Z.functionField) x I y, ← hjeq, isIntegral_map_iff]
  rw [← e]
  exact (UpperTheory.A.isFinCover_pull hc hK hL (fun V hV hV' g => (hj V hV hV' g).symm) hx hU).2

theorem UpperTheory.etaleCorrespondence_functionField_statement_one :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsAffCover s' (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU
  exact dualNumberPoint_preimage_top_of_reduction h2 hK hL j2 g2 x U hx hU
