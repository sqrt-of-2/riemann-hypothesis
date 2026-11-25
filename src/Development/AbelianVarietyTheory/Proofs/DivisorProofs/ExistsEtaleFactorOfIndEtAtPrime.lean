module

public import Aesop.BuiltinRules
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleModelOfIsColimit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtFactorLoc

def constColim (R : Type) [CommRing R] :
    IsColimit (Cocone.mk (CommRingCat.of R)
      (𝟙 ((Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)))) where
  desc c := c.ι.app ⟨⟨⟩⟩
  fac c j := by rcases j with ⟨⟨⟩⟩; simp
  uniq c m hm := by simpa using hm ⟨⟨⟩⟩

theorem exists_etale_factor_of_indEt_atPrime : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  intro R O _ _ _ P _ φ hφ hind Z _ _ _ g
  let L := Localization.AtPrime P
  let : Algebra L O := φ.toAlgebra
  have : IsScalarTower R L O :=
    IsScalarTower.of_algebraMap_eq (fun r => (congrArg (fun f => f r) hφ).symm)
  let g1 : L ⊗[R] Z →ₐ[L] O :=
    Algebra.TensorProduct.lift (Algebra.ofId L O) g (fun _ _ => Commute.all _ _)
  obtain ⟨C, _, _, _, ψ, χ, hψχ⟩ := GlobalTheory.EtC.exists_etale_factor_of_indEt L O hind (L ⊗[R] Z) g1
  let M := P.primeCompl
  let D0 := (Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)
  let s0 : D0 ⟶ (Functor.const _).obj (CommRingCat.of R) := 𝟙 _
  have hs0 : IsColimit (Cocone.mk _ s0) := constColim R
  obtain ⟨j, Aj, _, instA, hAj, ⟨e⟩⟩ := GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit
    (GlobalTheory.IndEtaleLoc.Idx D0 s0 M) (GlobalTheory.IndEtaleLoc.diag D0 s0 M)
    (Cocone.mk _ (GlobalTheory.IndEtaleLoc.toLoc (s := s0) (M := M) L))
    (GlobalTheory.IndEtaleLoc.isColimitToLoc L hs0) C

  let Re : Type := Localization.Away j.e
  let : Algebra R Re := (inferInstance : Algebra (D0.obj j.j) (Localization.Away j.e))
  let : Algebra Re L := (GlobalTheory.IndEtaleLoc.leg L j).toAlgebra
  let : Algebra Re Aj := instA
  have : Algebra.Etale Re Aj := hAj
  let e0 : R := j.e
  have he0 : e0 ∈ M := j.mem
  have : IsLocalization (Submonoid.powers e0) Re :=
    (inferInstance : IsLocalization (Submonoid.powers j.e) (Localization.Away j.e))
  have : IsScalarTower R Re L := IsScalarTower.of_algebraMap_eq (fun r =>
    (GlobalTheory.IndEtaleLoc.leg_algebraMap (s := s0) (M := M) L j r).symm)
  have hLoc : IsLocalization (M.map (algebraMap R Re)) L :=
    IsLocalization.isLocalization_of_submonoid_le Re L (Submonoid.powers e0) M
      (Submonoid.powers_le.2 he0)
  let e' : L ⊗[Re] Aj ≃ₐ[L] C := e
  let rA : Algebra Aj (L ⊗[Re] Aj) := Algebra.TensorProduct.rightAlgebra
  have hT : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re)))
      (L ⊗[Re] Aj) := IsLocalization.tensorRight _ _
  let : Algebra Aj C := (e'.toRingHom.comp (algebraMap Aj (L ⊗[Re] Aj))).toAlgebra
  let eA : L ⊗[Re] Aj ≃ₐ[Aj] C := AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun _ => rfl)
  have hCloc : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) C :=
    IsLocalization.isLocalization_of_algEquiv _ eA
  let : Algebra R Aj := ((algebraMap Re Aj).comp (algebraMap R Re)).toAlgebra
  have : IsScalarTower R Re Aj := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.Etale R Re :=
    (Algebra.Etale.of_isLocalizationAway j.e : Algebra.Etale (D0.obj j.j) (Localization.Away j.e))
  have : Algebra.Etale R Aj := Algebra.Etale.comp R Re Aj
  let : Algebra R C := ((algebraMap L C).comp (algebraMap R L)).toAlgebra
  have : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R Aj C := IsScalarTower.of_algebraMap_eq (fun r => by
    have key : ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r)) =
        algebraMap L (L ⊗[Re] Aj) (algebraMap R L r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R Re L]
      generalize algebraMap R Re r = c
      rw [Algebra.algebraMap_eq_smul_one (A := Aj) c, Algebra.algebraMap_eq_smul_one (A := L) c,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    show algebraMap L C (algebraMap R L r) = e' ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r))
    rw [key, AlgEquiv.commutes])
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R C) :=
    GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization R Aj C
      (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) (GlobalTheory.EtC.indEt_of_etale R Aj)
  let ψ' : Z →ₐ[R] C := (ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨W, _, _, _, u, v', huv⟩ := GlobalTheory.EtC.exists_etale_factor_of_indEt R C hC Z ψ'
  refine ⟨W, inferInstance, inferInstance, inferInstance, u, (χ.restrictScalars R).comp v', ?_⟩
  ext z
  have h1 := DFunLike.congr_fun huv z
  have h2 := DFunLike.congr_fun hψχ ((1 : L) ⊗ₜ[R] z)
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', ψ',
    Algebra.TensorProduct.includeRight_apply] at h1 h2 ⊢
  rw [h1, h2]
  simp [g1]

end GlobalTheory.IndEtFactorLoc
