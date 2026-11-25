module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.AlgebraicGeometry.FunctionField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.GenFiniteEtale

section Rings

variable (A B K L : Type) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]

include K L

omit [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L] in
theorem isAlgebraic_of_fractionRing [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L] : Algebra.IsAlgebraic A B := by
  have hKL : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hAL : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr hKL
  refine ⟨fun b => ?_⟩
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A B L) (IsFractionRing.injective B L)).mp
    (hAL.isAlgebraic (IsScalarTower.toAlgHom A B L b))

theorem exists_etale_away [CharZero K] [Algebra.FinitePresentation A B] :
    ∃ h : A, h ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
      [IsLocalization.Away (algebraMap A B h) B'], Algebra.Etale A B' := by
  classical

  have hKL : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have hAK : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (Rₘ := K) (nonZeroDivisors A)
  have hAL : Algebra.FormallyEtale A L := Algebra.FormallyEtale.comp A K L

  have hfr : IsLocalization (nonZeroDivisors B) (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [← Ideal.primeCompl_bot]
    infer_instance
  have hbot : Algebra.IsEtaleAt A (⊥ : Ideal B) :=
    Algebra.FormallyEtale.of_equiv
      ((IsLocalization.algEquiv (nonZeroDivisors B) L (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A)

  obtain ⟨f, hf, hfet⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := fun h0 => hf (by rw [h0]; exact Ideal.zero_mem _)

  obtain ⟨p, hp0, hp⟩ := (isAlgebraic_of_fractionRing A B K L).isAlgebraic f
  have hne : (Ideal.span {f}).comap (algebraMap A B) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_root_mem hf0 (Ideal.subset_span rfl) hp0 (by rwa [Polynomial.aeval_def] at hp)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp ha)
  have hle : PrimeSpectrum.basicOpen (algebraMap A B a) ≤ PrimeSpectrum.basicOpen f := by
    rw [hc, PrimeSpectrum.basicOpen_mul]
    exact inf_le_left
  have hsub : (PrimeSpectrum.basicOpen (algebraMap A B a) : Set (PrimeSpectrum B)) ⊆
      Algebra.etaleLocus A B :=
    (SetLike.coe_subset_coe.mpr hle).trans (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hfet)
  have het : Algebra.Etale A (Localization.Away (algebraMap A B a)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hsub
  refine ⟨a, ha0, fun B' _ _ _ _ _ => ?_⟩
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B a))
      (Localization.Away (algebraMap A B a)) B').restrictScalars A)

end Rings

theorem isFractionRing_eval (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let := (X.evaluation U (genericPoint X) hxU).hom.toAlgebra
  let r : X.functionField →+* X.residueField (genericPoint X) := (X.residue (genericPoint X)).hom
  have hinj : Function.Injective r := r.injective
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective r ⟨hinj, X.residue_surjective _⟩ with
      commutes' := fun a => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
  (hη : π (genericPoint Y) = genericPoint X) (hd : π.residueDegree (genericPoint Y) ≠ 0)

include hη hd

theorem affine_pair {V : X.Opens} {W : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ π ⁻¹ᵁ V) (hy : genericPoint Y ∈ W) :
    letI := (π.appLE V W e).hom.toAlgebra
    Function.Injective (algebraMap Γ(X, V) Γ(Y, W)) ∧ Algebra.IsAlgebraic Γ(X, V) Γ(Y, W) ∧
      Module.finrank Γ(X, V) Γ(Y, W) = π.residueDegree (genericPoint Y) ∧
      (CharZero Γ(X, V) → Algebra.FinitePresentation Γ(X, V) Γ(Y, W) →
        ∃ h : Γ(X, V), h ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra Γ(Y, W) B']
          [Algebra Γ(X, V) B'] [IsScalarTower Γ(X, V) Γ(Y, W) B']
          [IsLocalization.Away (algebraMap Γ(X, V) Γ(Y, W) h) B'], Algebra.Etale Γ(X, V) B') := by
  have hxV : π (genericPoint Y) ∈ V := e hy
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : Nonempty W := ⟨⟨_, hy⟩⟩
  let algB : Algebra Γ(X, V) Γ(Y, W) := (π.appLE V W e).hom.toAlgebra
  let algK : Algebra Γ(X, V) (X.residueField (π (genericPoint Y))) :=
    (X.evaluation V _ hxV).hom.toAlgebra
  let algL : Algebra Γ(Y, W) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation W _ hy).hom.toAlgebra
  let algKL : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  let algAL : Algebra Γ(X, V) (Y.residueField (genericPoint Y)) :=
    ((π.residueFieldMap (genericPoint Y)).hom.comp (X.evaluation V _ hxV).hom).toAlgebra
  have key : ∀ a : Γ(X, V), π.residueFieldMap (genericPoint Y) (X.evaluation V _ hxV a) =
      Y.evaluation W _ hy (π.appLE V W e a) := by
    intro a
    rw [Scheme.evaluation_naturality_apply π (genericPoint Y) hxV a]
    simp only [Scheme.evaluation, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have : IsScalarTower Γ(X, V) (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower Γ(X, V) Γ(Y, W) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq (fun a => key a)
  have hK : IsFractionRing Γ(X, V) (X.residueField (π (genericPoint Y))) :=
    isFractionRing_eval X hV hη hxV
  have hL : IsFractionRing Γ(Y, W) (Y.residueField (genericPoint Y)) :=
    isFractionRing_eval Y hW rfl hy
  have : FiniteDimensional (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)
  have hinj : Function.Injective (algebraMap Γ(X, V) Γ(Y, W)) := by
    intro a b hab
    have h1 : π.residueFieldMap (genericPoint Y) (X.evaluation V _ hxV a) =
        π.residueFieldMap (genericPoint Y) (X.evaluation V _ hxV b) := by
      rw [key a, key b]
      exact congrArg (Y.evaluation W _ hy) hab
    exact IsFractionRing.injective Γ(X, V) (X.residueField (π (genericPoint Y)))
      ((π.residueFieldMap (genericPoint Y)).hom.injective h1)
  refine ⟨hinj, isAlgebraic_of_fractionRing Γ(X, V) Γ(Y, W) (X.residueField (π (genericPoint Y)))
    (Y.residueField (genericPoint Y)), ?_, ?_⟩
  · exact (IsFractionRing.finrank_eq Γ(X, V) (X.residueField (π (genericPoint Y))) Γ(Y, W)
      (Y.residueField (genericPoint Y))).symm
  · intro hA hfp
    have := hA
    have := hfp
    have : CharZero (X.residueField (π (genericPoint Y))) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective Γ(X, V) _)
    exact exists_etale_away Γ(X, V) Γ(Y, W) (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y))


omit hη hd in
theorem genericPoint_mem_basicOpen {V : X.Opens} {h : Γ(X, V)} (hh : h ≠ 0) :
    genericPoint X ∈ X.basicOpen h := by
  rcases (V : Set X).eq_empty_or_nonempty with hV | hV
  · exfalso
    have hV' : V = ⊥ := SetLike.ext' hV
    subst hV'
    exact hh (Subsingleton.elim _ _)
  · have hx : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
    rw [Scheme.mem_basicOpen X h (genericPoint X) hx]
    have hinj := germ_injective_of_isIntegral X (genericPoint X) hx
    have h0 : X.presheaf.germ V (genericPoint X) hx h ≠ 0 := by
      intro h0
      exact hh (hinj (by rw [h0, map_zero]))
    exact (isUnit_iff_ne_zero (G₀ := X.functionField)).mpr h0

theorem eq_genericPoint {y : Y} (hy : π y = genericPoint X) : y = genericPoint Y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hyV : y ∈ π ⁻¹ᵁ V := by simpa [Scheme.Hom.mem_preimage, hy] using hxV
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyV (π ⁻¹ᵁ V).isOpen
  have e : W ≤ π ⁻¹ᵁ V := hWV
  have hηW : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr
      ⟨y, Set.mem_univ _, hyW⟩
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨-, halg, -, -⟩ := affine_pair π hη hd hV hW e hηW
  let := (π.appLE V W e).hom.toAlgebra
  obtain ⟨q, hyq⟩ : ∃ q, hW.fromSpec q = y := ⟨_, hW.fromSpec_primeIdealOf ⟨y, hyW⟩⟩
  have := hV.isOpenImmersion_fromSpec
  have := hW.isOpenImmersion_fromSpec
  have hgenV : hV.fromSpec (genericPoint (Spec Γ(X, V))) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion hV.fromSpec
  have hgenW : hW.fromSpec (genericPoint (Spec Γ(Y, W))) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion hW.fromSpec
  have hcomp : hV.fromSpec (Spec.map (π.appLE V W e) q) = π y := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec π hV hW e,
      Scheme.Hom.comp_apply, hyq]
  have hbot : Spec.map (π.appLE V W e) q = genericPoint (Spec Γ(X, V)) := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hcomp, hy]
    exact hgenV.symm
  rw [genericPoint_eq_bot_of_affine, Spec.map_apply] at hbot
  have hqbot : q.asIdeal = ⊥ := by
    by_contra hne
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    apply Ideal.under_ne_bot_of_algebraic_mem hb0 hb (halg.isAlgebraic b)
    exact congrArg PrimeSpectrum.asIdeal hbot
  rw [← hyq, ← hgenW, genericPoint_eq_bot_of_affine]
  congr 1
  exact PrimeSpectrum.ext hqbot


omit hη hd [IsIntegral X] [IsIntegral Y] in
theorem finite_app_of_le {V U : X.Opens} [IsFinite (π ∣_ V)] (hU : IsAffineOpen U) (e : U ≤ V) :
    IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite := by
  have hR : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{0}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (hf : IsIso f) => (inferInstance : IsFinite f))
  have h1 : IsFinite ((π ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) := inferInstance
  have h2 : IsFinite (π ∣_ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))) :=
    (MorphismProperty.arrow_mk_iso_iff (@IsFinite : MorphismProperty Scheme.{0})
      (morphismRestrictRestrict π V (V.ι ⁻¹ᵁ U))).mp h1
  have hUV : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr e
  rw [hUV] at h2
  have : IsAffine U := hU
  refine ⟨isAffine_of_isAffineHom (π ∣_ U), ?_⟩
  have h3 := (π ∣_ U).finite_app ⊤ (isAffineOpen_top _)
  change ((π ∣_ U).appTop).hom.Finite at h3
  rw [morphismRestrict_appTop] at h3
  have h4 := (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h3
  rwa [Scheme.Opens.ι_image_top] at h4

theorem exists_finite_etale_of_isProper [IsProper π] [IsLocallyNoetherian X] [CharZero Γ(X, ⊤)]
    (U₀ : X.Opens) (h₀ : genericPoint X ∈ U₀) :
    ∃ U : X.Opens, U ≤ U₀ ∧ IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (π.app U).hom.Finite ∧ (π.app U).hom.Etale ∧
      (letI := (π.app U).hom.toAlgebra
       Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) = π.residueDegree (genericPoint Y) := by
  have hfib : (⇑π ⁻¹' {genericPoint X}).Finite :=
    (Set.finite_singleton (genericPoint Y)).subset fun y hy => eq_genericPoint π hη hd hy
  obtain ⟨V, hηV, hVfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton π _ hfib
  obtain ⟨_, ⟨V', hV'a, rfl⟩, hηV', hV'le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show genericPoint X ∈ ((V ⊓ U₀ : X.Opens) : Set X) from ⟨hηV, h₀⟩) (V ⊓ U₀).isOpen
  have hle : V' ≤ V ⊓ U₀ := hV'le
  have hV'V : V' ≤ V := hle.trans inf_le_left
  have hV'U₀ : V' ≤ U₀ := hle.trans inf_le_right
  have hV' : IsAffineOpen V' := hV'a
  have : Nonempty V' := ⟨⟨_, hηV'⟩⟩
  obtain ⟨hW, hfinW⟩ := finite_app_of_le π hV' hV'V
  have hyW : genericPoint Y ∈ π ⁻¹ᵁ V' := by
    show π (genericPoint Y) ∈ V'
    rw [hη]; exact hηV'
  have : IsNoetherianRing Γ(X, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  have : CharZero Γ(X, V') := by
    refine ⟨fun a b hab => ?_⟩
    apply Nat.cast_injective (R := Γ(X, ⊤))
    apply map_injective_of_isIntegral X (homOfLE le_top : V' ⟶ ⊤)
    simp only [map_natCast]
    exact hab
  have H := affine_pair π hη hd hV' hW le_rfl hyW
  rw [Scheme.Hom.appLE_eq_app] at H
  let : Algebra Γ(X, V') Γ(Y, π ⁻¹ᵁ V') := (π.app V').hom.toAlgebra
  have : Module.Finite Γ(X, V') Γ(Y, π ⁻¹ᵁ V') := hfinW
  have : Algebra.FinitePresentation Γ(X, V') Γ(Y, π ⁻¹ᵁ V') :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨-, -, -, het⟩ := H
  obtain ⟨h, hh0, hh⟩ := het inferInstance inferInstance
  have hUV' : X.basicOpen h ≤ V' := X.basicOpen_le h
  have hUa : IsAffineOpen (X.basicOpen h) := hV'.basicOpen h
  have hηU : genericPoint X ∈ X.basicOpen h := genericPoint_mem_basicOpen hh0
  obtain ⟨hWU, hfinU⟩ := finite_app_of_le π hUa (hUV'.trans hV'V)
  have hyU : genericPoint Y ∈ π ⁻¹ᵁ X.basicOpen h := by
    show π (genericPoint Y) ∈ X.basicOpen h
    rw [hη]; exact hηU
  have H2 := affine_pair π hη hd hUa hWU le_rfl hyU
  rw [Scheme.Hom.appLE_eq_app] at H2
  refine ⟨X.basicOpen h, hUV'.trans hV'U₀, hUa, hηU, hWU, hfinU, ?_, H2.2.2.1⟩

  let iY : π ⁻¹ᵁ X.basicOpen h ⟶ π ⁻¹ᵁ V' := (Opens.map π.base).map (homOfLE hUV')
  let algB : Algebra Γ(Y, π ⁻¹ᵁ V') Γ(Y, π ⁻¹ᵁ X.basicOpen h) := (Y.presheaf.map iY.op).hom.toAlgebra
  let algA : Algebra Γ(X, V') Γ(Y, π ⁻¹ᵁ X.basicOpen h) :=
    (π.app V' ≫ Y.presheaf.map iY.op).hom.toAlgebra
  have : IsScalarTower Γ(X, V') Γ(Y, π ⁻¹ᵁ V') Γ(Y, π ⁻¹ᵁ X.basicOpen h) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.Away (algebraMap Γ(X, V') Γ(Y, π ⁻¹ᵁ V') h) Γ(Y, π ⁻¹ᵁ X.basicOpen h) :=
    hW.isLocalization_of_eq_basicOpen (π.app V' h) iY (Scheme.preimage_basicOpen π h)
  have hE : Algebra.Etale Γ(X, V') Γ(Y, π ⁻¹ᵁ X.basicOpen h) := hh _
  let algAh : Algebra Γ(X, V') Γ(X, X.basicOpen h) := (X.presheaf.map (homOfLE hUV').op).hom.toAlgebra
  have : IsLocalization.Away h Γ(X, X.basicOpen h) :=
    hV'.isLocalization_of_eq_basicOpen h (homOfLE hUV') rfl
  have : Algebra.Etale Γ(X, V') Γ(X, X.basicOpen h) := Algebra.Etale.of_isLocalizationAway h
  let algAhBh : Algebra Γ(X, X.basicOpen h) Γ(Y, π ⁻¹ᵁ X.basicOpen h) := (π.app (X.basicOpen h)).hom.toAlgebra
  have : IsScalarTower Γ(X, V') Γ(X, X.basicOpen h) Γ(Y, π ⁻¹ᵁ X.basicOpen h) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (π.app V' ≫ Y.presheaf.map iY.op).hom =
        (X.presheaf.map (homOfLE hUV').op ≫ π.app (X.basicOpen h)).hom
      rw [π.naturality]
      rfl)
  have : Algebra.Etale Γ(X, X.basicOpen h) Γ(Y, π ⁻¹ᵁ X.basicOpen h) :=
    Algebra.Etale.of_restrictScalars Γ(X, V') Γ(X, X.basicOpen h) Γ(Y, π ⁻¹ᵁ X.basicOpen h)
  exact this


end GlobalTheory.GenFiniteEtale
