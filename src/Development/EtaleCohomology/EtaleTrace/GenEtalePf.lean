module

public import Development.EtaleCohomology.EtaleTrace.FibrePf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

namespace LateralTheory.EtaleTrace.GenEtaleRing

theorem ring_gen_etale (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [Algebra.IsEtaleAt A (⊥ : Ideal B)] :
    ∃ a : A, a ≠ 0 ∧ ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap A B a) B' → Algebra.Etale A' B' := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  obtain ⟨f, hf, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := by simpa using hf
  obtain ⟨a, ha, g, hg⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) f).exists_ne_zero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨a, ha, fun A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have hloc : Algebra.Etale A (Localization.Away (algebraMap A B a)) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hEt ⊢
    refine subset_trans ?_ hEt
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  have : Algebra.Etale A B' := Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B a))
      (Localization.Away (algebraMap A B a)) B').restrictScalars A)
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]; exact hB
  have : Algebra.FormallyEtale A' B' := Algebra.FormallyEtale.localization_base (Submonoid.powers a)
  have : Algebra.FiniteType A A' := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) A'
  have : Algebra.FinitePresentation A' B' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.GenEtaleRing

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineSetup : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom ∧
    ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime, (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

def EtaleOverBasic : Prop := ∀ {X P : Scheme.{0}} (π : X ⟶ P) (U : P.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) →
  ∀ a : Γ(P, U), (letI := (π.app U).hom.toAlgebra;
    ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra Γ(P, U) A'] [Algebra Γ(X, π ⁻¹ᵁ U) B']
      [Algebra A' B'] [Algebra Γ(P, U) B'] [IsScalarTower Γ(P, U) A' B'] [IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap Γ(P, U) Γ(X, π ⁻¹ᵁ U) a) B' → Algebra.Etale A' B') →
  Etale (π ∣_ P.basicOpen a)

theorem GenEtale_of (h1 : GenAffineSetup) (h2 : EtaleOverBasic) : GenEtale := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hnoeth, hfinU, hinj, _, het⟩ := h1 k p r π hπ hr hfin hsurj hun
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : Nonempty (π ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := hsurj.surj hne.some
    exact ⟨⟨x, show π x ∈ U by rw [hx]; exact hne.some_mem⟩⟩
  let := (π.app U).hom.toAlgebra
  have : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfinU
  have : FaithfulSMul Γ(P, U) Γ(X, π ⁻¹ᵁ U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨a, ha, H⟩ := LateralTheory.EtaleTrace.GenEtaleRing.ring_gen_etale Γ(P, U) Γ(X, π ⁻¹ᵁ U)
  refine ⟨P.basicOpen a, ?_, h2 π U hU hU' a H⟩
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  have : P.basicOpen a = ⊥ := by ext1; simpa using hc
  exact ha ((basicOpen_eq_bot_iff a).1 this)

end LateralTheory.EtaleTrace.Cov
