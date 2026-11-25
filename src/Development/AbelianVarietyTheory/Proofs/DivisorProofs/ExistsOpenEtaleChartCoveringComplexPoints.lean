module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenFinEt

private theorem generic_finite (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B] :
    ∃ a : A, a ≠ 0 ∧ ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap A B a) B' → Module.Finite A' B' := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples A s
  refine ⟨y, hy, fun A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  obtain ⟨u, hu⟩ : IsUnit (algebraMap A A' y) := IsLocalization.Away.algebraMap_isUnit y
  have hyy : algebraMap B B' (algebraMap A B y) = algebraMap A' B' (u : A') := by
    rw [hu, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hcancel : ∀ (n : ℕ) (x : B'), _root_.IsIntegral A' (x * algebraMap A' B' (u : A') ^ n) →
      _root_.IsIntegral A' x := by
    intro n x hx
    have : x = ((u⁻¹ : A'ˣ) : A') ^ n • (x * algebraMap A' B' (u : A') ^ n) := by
      rw [Algebra.smul_def, map_pow, mul_left_comm, ← mul_pow, ← map_mul, Units.inv_mul, map_one,
        one_pow, mul_one]
    rw [this]
    exact hx.smul _
  have hB1 : ∀ b : B, _root_.IsIntegral A' (algebraMap B B' b) := by
    have hle : Algebra.adjoin A (s : Set B) ≤
        ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B') := by
      refine Algebra.adjoin_le fun z hz => ?_
      have h1 : _root_.IsIntegral A' (algebraMap B B' (y • z)) :=
        ((hint z hz).map (IsScalarTower.toAlgHom A B B')).tower_top
      refine hcancel 1 _ ?_
      rw [Algebra.smul_def, map_mul, hyy, mul_comm] at h1
      rw [pow_one]
      exact h1
    intro b
    exact hle (hs ▸ Algebra.mem_top)
  have : Algebra.IsIntegral A' B' := ⟨fun x => by
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A B y)) x
    refine hcancel n x ?_
    simp only [map_pow, hyy] at hx
    rw [hx]
    exact hB1 b⟩
  have : Algebra.FiniteType B B' := IsLocalization.finiteType_of_monoid_fg
    (Submonoid.powers (algebraMap A B y)) B'
  have : Algebra.FiniteType A B' := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : Algebra.FiniteType A' B' := Algebra.FiniteType.of_restrictScalars_finiteType A A' B'
  exact Algebra.IsIntegral.finite

private theorem generic_free (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] :
    ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' →
      Module.Free A' B' := by
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have hu : IsUnit (algebraMap A A' r) :=
    isUnit_of_mul_isUnit_left (y := algebraMap A A' c)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (r * c))
  let : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) B)).equiv.symm
  have : Module.Free A' (TensorProduct A A' B) :=
    Module.Free.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B)
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers (r * c))) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]; exact hB
  exact Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers (r * c)) A'
    (IsScalarTower.toAlgHom A B B').toLinearMap).equiv

private theorem generic_etale (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CharZero A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B] :
    ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' →
      Algebra.Etale A' B' := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  let : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) := inferInstance
  have : Algebra.FormallyEtale (FractionRing A) (FractionRing B) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyEtale A (FractionRing A) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have : Algebra.FormallyEtale A (FractionRing B) :=
    Algebra.FormallyEtale.comp A (FractionRing A) (FractionRing B)
  have : IsLocalization (⊥ : Ideal B).primeCompl (FractionRing B) := by
    rw [Ideal.primeCompl_bot]; infer_instance
  have : Algebra.IsEtaleAt A (⊥ : Ideal B) :=
    Algebra.FormallyEtale.of_equiv ((IsLocalization.algEquiv (⊥ : Ideal B).primeCompl (FractionRing B)
      (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A)
  obtain ⟨f, hf, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := by simpa using hf
  obtain ⟨a, ha, hfa⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) f).exists_ne_zero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨a, ha, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have h1 : Algebra.Etale A (Localization.Away (algebraMap A B (a * c))) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at het ⊢
    refine subset_trans ?_ het
    obtain ⟨g, hg⟩ := hfa
    rw [map_mul, hg, mul_assoc]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  have : Algebra.Etale A B' :=
    Algebra.Etale.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B (a * c)))
      (Localization.Away (algebraMap A B (a * c))) B').restrictScalars A)
  have : Algebra.FormallyEtale A' B' :=
    Algebra.FormallyEtale.localization_base (Submonoid.powers (a * c))
  have : Algebra.FiniteType A A' := IsLocalization.finiteType_of_monoid_fg
    (Submonoid.powers (a * c)) A'
  have : Algebra.FinitePresentation A' B' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'
  exact ⟨inferInstance, inferInstance⟩

private theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  let := (X.evaluation U _ hxU).hom.toAlgebra
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

private theorem inj_alg_rank {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (h : f (genericPoint Y) = genericPoint X) (hδ : f.residueDegree (genericPoint Y) ≠ 0)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hyV : genericPoint Y ∈ V) (e : V ≤ f ⁻¹ᵁ U) :
    letI := (f.appLE U V e).hom.toAlgebra
    FaithfulSMul Γ(X, U) Γ(Y, V) ∧ Algebra.IsAlgebraic Γ(X, U) Γ(Y, V) ∧
      Module.finrank Γ(X, U) Γ(Y, V) = f.residueDegree (genericPoint Y) := by
  have hxU : f (genericPoint Y) ∈ U := e hyV
  let := (f.appLE U V e).hom.toAlgebra
  let := (X.evaluation U _ hxU).hom.toAlgebra
  let : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hyV).hom.toAlgebra
  let := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  let : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (f.appLE U V e ≫ Y.evaluation V _ hyV).hom.toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hnat : X.evaluation U _ hxU ≫ f.residueFieldMap (genericPoint Y) =
      f.appLE U V e ≫ Y.evaluation V _ hyV := by
    rw [Scheme.evaluation_naturality f _ hxU]
    simp [Scheme.Hom.appLE, Scheme.evaluation]
  have : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  have := isFractionRing_evaluation X hU h hxU
  have := isFractionRing_evaluation Y hV rfl hyV
  have : FiniteDimensional (X.residueField (f (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hδ)
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hinj : Function.Injective (algebraMap Γ(X, U) (Y.residueField (genericPoint Y))) := by
    rw [IsScalarTower.algebraMap_eq Γ(X, U) (X.residueField (f (genericPoint Y)))]
    exact (f.residueFieldMap (genericPoint Y)).hom.injective.comp
      (IsFractionRing.injective Γ(X, U) (X.residueField (f (genericPoint Y))))
  refine ⟨?_, ?_, (IsFractionRing.finrank_eq Γ(X, U) (X.residueField (f (genericPoint Y)))
    Γ(Y, V) (Y.residueField (genericPoint Y))).symm⟩
  · rw [faithfulSMul_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq Γ(X, U) Γ(Y, V)] at hinj
    exact Function.Injective.of_comp (f := algebraMap Γ(Y, V) (Y.residueField (genericPoint Y))) hinj
  · have : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
      (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (f (genericPoint Y)))).2 inferInstance
    exact Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)))
      (IsFractionRing.injective _ _)

set_option backward.isDefEq.respectTransparency.types false in
private theorem preimage_eq_of_finite {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π]
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hyV : genericPoint Y ∈ V) (e : V ≤ π ⁻¹ᵁ U) (hfin : (π.appLE U V e).hom.Finite) :
    π ⁻¹ᵁ U = V := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : IsFinite (π.resLE U V e) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp only [CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.comp ?_ hfin) ?_
    · exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    · exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  have : IsFinite (Y.homOfLE e ≫ π ∣_ U) := this
  have : IsFinite (Y.homOfLE e) := IsFinite.of_comp _ (π ∣_ U)
  have : Nonempty (π ⁻¹ᵁ U : Y.Opens) := ⟨⟨_, e hyV⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE e)) :=
    ⟨(Y.homOfLE e).isClosedMap.isClosed_range, (Y.homOfLE e).isOpenEmbedding.isOpen_range⟩
  have huniv := hcl.eq_univ ⟨_, ⟨⟨_, hyV⟩, rfl⟩⟩
  refine le_antisymm (fun y hy => ?_) e
  obtain ⟨z, hz⟩ : (⟨y, hy⟩ : (π ⁻¹ᵁ U : Y.Opens)) ∈ Set.range (Y.homOfLE e) := huniv ▸ trivial
  have : z.1 = y := by
    have := congrArg Subtype.val hz
    exact (Scheme.homOfLE_apply e z).symm.trans this
  exact this ▸ z.2

private theorem shrink {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π]
    (hg : π (genericPoint Y) = genericPoint X) {U₀ : X.Opens} {V₀ : Y.Opens} (hU₀ : IsAffineOpen U₀)
    (hV₀ : IsAffineOpen V₀) (hyV₀ : genericPoint Y ∈ V₀) (hVle : V₀ ≤ π ⁻¹ᵁ U₀)
    (P : ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A' B'], Prop)
    (a : Γ(X, U₀)) (ha : a ≠ 0)
    (H : letI := (π.appLE U₀ V₀ hVle).hom.toAlgebra
      ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra Γ(X, U₀) A'] [Algebra Γ(Y, V₀) B']
      [Algebra A' B'] [Algebra Γ(X, U₀) B'] [IsScalarTower Γ(X, U₀) A' B']
      [IsScalarTower Γ(X, U₀) Γ(Y, V₀) B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) a) B' →
      Module.Finite A' B' ∧ P A' B') :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ P Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
  let : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  have hUU₀ : X.basicOpen a ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen a) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen a := by
    have hne : X.basicOpen a ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen a).isOpen).2 ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen a with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle a) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  let iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  let iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  let iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  let iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  have : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  have : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  have hlA : IsLocalization.Away a Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  have hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) a) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  obtain ⟨hfin, hP⟩ := H Γ(X, U) Γ(Y, V) hlA hlB
  have hpre : π ⁻¹ᵁ U = V := preimage_eq_of_finite π hUa hVa hyV hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (letI := (π.appLE U W hW).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, W) ∧ P Γ(X, U) Γ(Y, W)) →
      (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ P Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h1
    exact h1
  exact ⟨U, hUa, hxU, hpre ▸ hVa, key V hVU hpre.symm ⟨hfin, hP⟩⟩

end GlobalTheory.GenFinEt

theorem _root_.GlobalTheory.T.exists_affine_etale_finite_nbhd_generic : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hδ
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have := hX.isLocallyNoetherian
  obtain ⟨U₁, hU₁, hxU₁, hV₁, hfin₁, -⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      IsAffineOpen (π ⁻¹ᵁ U) ∧ (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ True) := by
    obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint X))
    have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
      show π (genericPoint Y) ∈ U₀
      rw [hg]; exact hxU₀
    obtain ⟨V₀, hV₀, hyV₀, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
    have : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
    let : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
    have : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
      HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
    have : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) :=
      (GenFinEt.inj_alg_rank π hg hδ hU₀ hV₀ hyV₀ hVle).2.1
    obtain ⟨a, ha, H⟩ := GenFinEt.generic_finite Γ(X, U₀) Γ(Y, V₀)
    exact GenFinEt.shrink π hg hU₀ hV₀ hyV₀ hVle (fun _ _ _ _ _ => True) a ha
      fun A' B' _ _ _ _ _ _ _ _ hA hB => ⟨H A' B' hA hB, trivial⟩
  have hyV₁ : genericPoint Y ∈ π ⁻¹ᵁ U₁ := by
    show π (genericPoint Y) ∈ U₁
    rw [hg]; exact hxU₁
  obtain ⟨U, hU, hxU, hV, hfin, hfree, het⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      IsAffineOpen (π ⁻¹ᵁ U) ∧ (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧
        Algebra.Etale Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    have : Nonempty U₁ := ⟨⟨_, hxU₁⟩⟩
    have : Nonempty (π ⁻¹ᵁ U₁ : Y.Opens) := ⟨⟨_, hyV₁⟩⟩
    let : Algebra Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁) := (π.appLE U₁ (π ⁻¹ᵁ U₁) le_rfl).hom.toAlgebra
    have : IsNoetherianRing Γ(X, U₁) := IsLocallyNoetherian.component_noetherian ⟨U₁, hU₁⟩
    have : CharZero Γ(X, U₁) :=
      ((resG X (le_top : U₁ ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
    have : FaithfulSMul Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁) :=
      (GenFinEt.inj_alg_rank π hg hδ hU₁ hV₁ hyV₁ le_rfl).1
    obtain ⟨a, ha, Ha⟩ := GenFinEt.generic_free Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁)
    obtain ⟨b, hb, Hb⟩ := GenFinEt.generic_etale Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁)
    refine GenFinEt.shrink π hg hU₁ hV₁ hyV₁ le_rfl
      (fun A' B' _ _ _ => Module.Free A' B' ∧ Algebra.Etale A' B') (a * b) (mul_ne_zero ha hb)
      fun A' B' _ _ _ _ _ _ _ _ hA hB => ⟨?_, Ha b A' B' hA hB,
        Hb a A' B' (by rw [mul_comm]; exact hA) (by rw [mul_comm]; exact hB)⟩
    have : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₁) (Submonoid.powers (a * b))) B' := by
      rw [Algebra.algebraMapSubmonoid_powers]; exact hB
    exact Module.Finite.of_isLocalization Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁) (Submonoid.powers (a * b))
  have hyV : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hg]; exact hxU
  refine ⟨U, hU, hxU, hV, ?_⟩
  rw [Scheme.Hom.app_eq_appLE]
  exact ⟨het, hfin, hfree, (GenFinEt.inj_alg_rank π hg hδ hU hV hyV le_rfl).2.2⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RingTheory.RingHom.Etale\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices\nimport Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl\nimport Formalism.DegreeFormula.FlagDegFormula\nimport Formalism.SharpRestriction.CuspSpanNormBounds.Point\nimport Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc\n\n"}
section -- clump:auto
@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverDeg

theorem exists_open_covering_charts : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ σ : k →+* ℂ, (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hδ
  obtain ⟨U₁, hU₁, hx₁, ht⟩ := _root_.GlobalTheory.GenericCoords.exists_affine_etale_coords hp
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_nbhd_generic hp hq π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := _root_.GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover p π D _ _ U₁ U₂ hU₁ hx₁ ht hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun σ => ⟨fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩⟩
  · rw [_root_.GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact _root_.GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := _root_.GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDeg
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints =====
