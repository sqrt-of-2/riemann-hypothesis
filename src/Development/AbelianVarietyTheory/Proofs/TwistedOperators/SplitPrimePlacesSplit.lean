module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitPlace

theorem isSplit_of_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : IsSplit (E := E) v := by
  classical
  have hfin : Module.Finite (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
  have hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
    | infer_instance

  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact h2

  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [hdeg] at hsum

  have hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q := by
    intro Q hQo
    have hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F) := by
      rw [← hQo.over]
      exact hv
    have hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q := hmem
    simpa using hmem'

  have hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    have := hQp
    have := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hN : Ideal.absNorm Q = p := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1
    have key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p := by
      rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]
      exact hN
    exact Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)

  have he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    have := hQp
    have := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hsq : (p : 𝓞 E) ∉ Q ^ 2 := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2
    have hle : Q.ramificationIdx (𝓞 F) ≤ 1 := by
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
      by_contra hlt
      push Not at hlt
      have hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2 :=
        Ideal.le_pow_of_le_ramificationIdx' hlt
      apply hsq
      have hin := hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)
      simpa using hin
    have hpos : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    show Q.ramificationIdx (𝓞 F) = 1
    omega

  by_contra hns
  obtain ⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal := by
    first
    | obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
      exact ⟨Q0, hQ0m.isPrime, hQ0o⟩

  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨Q0, hQ0p, hQ0o⟩
  have honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0 := by
    rintro ⟨Q, hQp, hQo⟩
    by_contra hne
    apply hns
    have := hQo
    haveI := hQ0o
    refine ⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩
    intro hPQ
    exact hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))
  rw [Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb)
    (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0] at hsum
  omega

theorem isSplit_of_splitsCompletely : ∀ (D : D7) (p : ℕ), SplitsCompletely D p → ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → IsSplit (E := D.host.E) v := by
  intro D p hp v hv
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
      exact IsQuadraticExtension.finrank_eq_two _ _
    | have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
      have hF := Formalism.HC.HostAx.finrank_hostF D.host.toHostAx
      have hm := Module.finrank_mul_finrank ℚ D.host.F D.host.E
      have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
      rw [hE, hF] at hm
      rw [hF] at hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  exact isSplit_of_norm h2 hp.1 hp.2 v hv

end GlobalTheory.SplitPlace
