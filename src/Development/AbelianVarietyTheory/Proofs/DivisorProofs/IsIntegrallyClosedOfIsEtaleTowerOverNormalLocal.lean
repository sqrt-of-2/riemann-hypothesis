module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.EtNormal

theorem isDomain_and_isIntegrallyClosed_of_formallyEtale (A T : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    [Algebra.FormallyEtale A T] [Algebra.EssFiniteType A T] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  let B := Algebra.EssFiniteType.subalgebra A T
  let P : Ideal B := (IsLocalRing.maximalIdeal T).comap (algebraMap B T)
  have hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl := by
    ext x
    change IsUnit (algebraMap B T x) ↔ x ∉ P
    simp [P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hloc : IsLocalization.AtPrime T P := by
    have := Algebra.EssFiniteType.isLocalization A T
    rw [hM] at this
    exact this
  have : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).1 inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A
  have : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e
  have : Algebra.IsSmoothAt A P := inferInstance
  obtain ⟨f, hfP, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) P ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

end GlobalTheory.EtNormal

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  intro K L _ _ cK cL r R T ι ψ τ h
  have := h.top.isLocalRing
  have := h.normal
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  let : Algebra ℂ R := c0.toAlgebra
  have : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  let : Algebra A T := φ.toAlgebra
  let : Algebra ℂ T := cT.toAlgebra
  have : Algebra.FormallyEtale A T := h.etale
  have : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
  have : IsScalarTower ℂ A T := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change cT a = φ (MvPolynomial.C (c0 a))
    have e : φ (MvPolynomial.C (c0 a)) = ι (c0 a) := MvPolynomial.eval₂Hom_C _ _ _
    rw [e]
    exact Subtype.ext (h.const a).symm
  have : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T
  have : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r
  exact (GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2

end GlobalTheory.FieldPair
