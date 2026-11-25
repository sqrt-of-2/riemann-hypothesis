module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
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
public import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Formalism.SharedLemmas.PrecompleteFinite

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  first

  | (apply _root_.Formalism.SharedLemmas.isPrecomplete_of_moduleFinite)

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.CA.cl_fin :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'], IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ _ _ _ h
  have := h.noeth
  have := h.complete
  have := h.isLocalHom
  have := h.res_fin
  have hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hIntegral : (algebraMap R R').IsIntegral :=
    RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap R R') hIntegral (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R') hIntegral P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (isPrecomplete_finite _))
  have hloc : IsLocalHom (algebraMap R R') := ⟨fun a ha => by
    by_contra hn
    have h1 : a ∈ maximalIdeal R := hn
    rw [← hcomap, Ideal.mem_comap] at h1
    exact h1 ha⟩
  have hT : IsScalarTower O (ResidueField R) (ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
        ← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField R'),
        IsScalarTower.algebraMap_apply O R' (ResidueField R'),
        IsScalarTower.algebraMap_apply R R' (ResidueField R'),
        IsScalarTower.algebraMap_apply O R R']
  exact
    { noeth := hN
      complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
      isLocalHom := by
        rw [IsScalarTower.algebraMap_eq O R R']
        infer_instance
      res_fin := Module.Finite.trans (ResidueField R) (ResidueField R') }
