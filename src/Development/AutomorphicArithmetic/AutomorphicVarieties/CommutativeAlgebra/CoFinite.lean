module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
public import Formalism.SharedLemmas.PrecompleteFinite

@[expose] public section

noncomputable section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  first

  | (apply _root_.Formalism.SharedLemmas.isPrecomplete_of_moduleFinite)

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := by
  have hsm : ∀ (K : Ideal R) (x : R), x ∈ (K • (⊤ : Submodule R R)) ↔ x ∈ K := by
    intro K x
    simp [smul_eq_mul, Ideal.mul_top]
  have he' : I ^ (e + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ e)) he
  have hpow : ∀ k, I ^ ((e + 1) * k) ≤ J ^ k := by
    intro k
    rw [pow_mul]
    exact Ideal.pow_right_mono he' k
  refine ⟨fun {f} hf => ?_⟩
  have hgc : ∀ {m n : ℕ}, m ≤ n →
      f ((e + 1) * m) ≡ f ((e + 1) * n) [SMOD (J ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
    rw [SModEq.sub_mem, hsm] at h ⊢
    exact hpow m h
  obtain ⟨L, hL⟩ := hJ.prec' (fun k => f ((e + 1) * k)) hgc
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (show n ≤ (e + 1) * n by nlinarith)
  have h2 := hL n
  rw [SModEq.sub_mem, hsm] at h1 h2 ⊢
  have h3 : f ((e + 1) * n) - L ∈ I ^ n := Ideal.pow_right_mono hJI n h2
  have := Ideal.add_mem _ h1 h3
  simpa using this

theorem UpperTheory.V.Alg.co_finite :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'] [IsLocalRing R'],
      (∀ x : R', ∃ a : O, x - algebraMap O R' a ∈ maximalIdeal R') → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ _ _ _ hres
  have : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  have : IsNoetherian R R' := inferInstance
  have hN : IsNoetherianRing R' := isNoetherian_of_tower R this
  have : Algebra.IsIntegral R R' := inferInstance
  have hcompl : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hcomap : ∀ P : Ideal R', P.IsPrime → maximalIdeal R ≤ P.comap (algebraMap R R') → P = maximalIdeal R' := by
    intro P hP hle
    have hcm : (P.comap (algebraMap R R')).IsMaximal := by
      have hne : P.comap (algebraMap R R') ≠ ⊤ := (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      have : P.comap (algebraMap R R') = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hne) hle
      rw [this]; infer_instance
    have := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P hcm
    exact IsLocalRing.eq_maximalIdeal this
  have hcm' : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hloc : IsLocalHom (algebraMap R R') := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [← hcm', Ideal.mem_comap] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this ha
  set J : Ideal R' := (maximalIdeal R).map (algebraMap R R') with hJdef
  have hJI : J ≤ maximalIdeal R' := by
    rw [hJdef, Ideal.map_le_iff_le_comap, hcm']
  have hrad : maximalIdeal R' ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    rw [hcomap P hPp (Ideal.map_le_iff_le_comap.1 hJP)]
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have : IsPrecomplete (maximalIdeal R) R' := isPrecomplete_finite (R := R) (M := R') (maximalIdeal R)
  have hJp : IsPrecomplete J R' := by
    rw [hJdef]
    exact IsPrecomplete.map_algebraMap_iff.2 this
  have hprec : IsPrecomplete (maximalIdeal R') R' := prec_cofinal hJI he hJp
  have : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hlocO : IsLocalHom (algebraMap O R') := by
    rw [IsScalarTower.algebraMap_eq O R R']
    infer_instance
  exact
    { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hprec }
      isLocalHom := hlocO
      res_surj := hres }
