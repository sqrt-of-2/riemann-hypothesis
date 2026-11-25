module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

open IsLocalRing

namespace GlobalTheory.EtaleCompletionNormal

theorem formallyUnramified_of_map_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallyUnramified R S := by
  constructor
  rw [← IsLocalRing.subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

theorem isDomain_and_isIntegrallyClosed : ∀ (D E : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [CommRing E] [IsLocalRing E] (h : D →+* E), IsNoetherianRing D → IsDomain (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsNoetherianRing E → IsAdicComplete (IsLocalRing.maximalIdeal E) E → IsLocalHom h → GlobalTheory.Toroidal.IsEtaleCompletion h → ((IsLocalRing.residue E).comp h).FormallyUnramified → IsDomain E ∧ IsIntegrallyClosed E := by
  intro D E _ _ _ _ _ h hD hAd hAi hE hEc _ het hfu
  obtain ⟨hflat, hmap, hfin⟩ := het
  have := hD; have := hE; have := hEc; have := hAd; have := hAi
  let A := AdicCompletion (maximalIdeal D) D
  have : IsNoetherianRing A := AdicNoeth.isNoetherianRing_adicCompletion D _
  have : IsAdicComplete ((maximalIdeal D).map h) E := by rw [hmap]; exact hEc
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension (maximalIdeal D) h
  let : Algebra A E := g.toAlgebra
  have hgA : ∀ a, g (algebraMap D A a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal A).map (algebraMap A E) = maximalIdeal E := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal D).map (g.comp _) = _
    rw [hg, hmap]
  have : IsLocalHom (algebraMap A E) := ((local_hom_tfae _).out 1 3).mpr hmA.le

  have hres : ((residue E).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap D A) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  have : Module.Finite A (E ⧸ (maximalIdeal A).map (algebraMap A E)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap A E)).Finite
    rw [hmA]
    exact hres
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A E)) E := by rw [hmA]; infer_instance
  have : Module.Finite A E := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

  have : Module.Flat A E := by
    refine LocalFlat.flat_of_relationsLift E (I := maximalIdeal A)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    let : Algebra D E := h.toAlgebra
    have : Module.Flat D E := hflat
    have fg := (maximalIdeal D).fg_of_isNoetherianRing
    have hkerA : ∀ x : A, AdicCompletion.evalₐ (maximalIdeal D) n x = 0 ↔ x ∈ maximalIdeal A ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem D,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal A ^ n).map (algebraMap A E) = (maximalIdeal D ^ n).map (algebraMap D E) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal D ^ n).map (g.comp _) = _
      rw [hg]
      rfl
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal D) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal D ^ n).map (algebraMap D E)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal D) n x)
      have hx : x - algebraMap D A a ∈ maximalIdeal A ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap A E x - h a ∈ (maximalIdeal D ^ n).map (algebraMap D E) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap A E x - g (algebraMap D A a) = algebraMap A E (x - algebraMap D A a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E (maximalIdeal D ^ n)).toLinearEquiv

  have : Algebra.FormallyUnramified A (ResidueField E) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap A (ResidueField E)).comp (algebraMap D A) = (residue E).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap D A) (by rw [e]; exact hfu)
  have : Algebra.FormallyUnramified A E := formallyUnramified_of_map_maximalIdeal hmA
  have : Algebra.FinitePresentation A E :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := E)).1 inferInstance
  have : Algebra.Etale A E := Algebra.Etale.of_formallyUnramified_of_flat
  have : IsLocalization.AtPrime E (maximalIdeal E) :=
    IsLocalization.self fun a ha => by_contra fun h' => ha h'
  exact isDomain_and_isIntegrallyClosed_atPrime_of_etale A (maximalIdeal E) E

end GlobalTheory.EtaleCompletionNormal
