module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiholomorphicLiftSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField GlobalTheory.UPel.HT

theorem UpperTheory.Gal.FiniteEtaleModels.O.mOne :
    UpperTheory.Gal.FiniteEtaleModels.O.MOne := by
  intro q _ D hm
  have := D.freeLa
  have := D.finLa
  have hb : Function.Bijective (algebraMap (𝓞 D.F) D.O) :=
    ⟨D.algebraMap_injective hm, Datum.algebraMap_surjective_of_m_eq_one q D hm⟩
  have hfin : Module.Finite D.O D.La := Module.Finite.of_restrictScalars_finite ℤ D.O D.La
  refine ⟨hb, ?_, hfin⟩
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective _ hb
  let : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (r : 𝓞 D.F) (x : D.La), r • x = algebraMap (𝓞 D.F) D.O r • x :=
    fun _ _ => rfl
  have : IsScalarTower ℤ (𝓞 D.F) D.La :=
    ⟨fun n r x => by rw [hsmul, hsmul, map_zsmul, smul_assoc]⟩
  have htors : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨r, hr⟩, hx⟩
    have hx' : r • x = 0 := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr0
    have hz : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0 := by
      have h1 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x =
          ((Ideal.absNorm (Ideal.span {r}) : ℕ) : 𝓞 D.F) • x := by
        rw [natCast_zsmul]
        exact (Nat.cast_smul_eq_nsmul (𝓞 D.F) _ x).symm
      rw [h1, ← hs, mul_smul, hx', smul_zero]
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN)
  have : Module.Flat (𝓞 D.F) D.La := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htors
  have : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.FinitePresentation (𝓞 D.F) D.La := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 D.F) D.La := Module.Flat.projective_of_finitePresentation
  have h1 : RingHomInvPair (e : 𝓞 D.F →+* D.O) (e.symm : D.O →+* 𝓞 D.F) :=
    RingHomInvPair.of_ringEquiv e
  have h2 : RingHomInvPair (e.symm : D.O →+* 𝓞 D.F) (e : 𝓞 D.F →+* D.O) :=
    RingHomInvPair.symm _ _
  let f : D.La ≃ₛₗ[(e : 𝓞 D.F →+* D.O)] D.La :=
    { AddEquiv.refl D.La with map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv f
