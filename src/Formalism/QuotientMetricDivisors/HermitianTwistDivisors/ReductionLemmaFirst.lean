module

public import Formalism.QuotientMetricDivisors.Statement
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SelectionLemmas
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain Matrix
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ReductionFirst

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Tw (w : HeightOneSpectrum (𝓞 K)) : Submonoid (𝓞 K) where
  carrier := {s | s ∉ w.asIdeal ∧ cO K s ∉ w.asIdeal}
  one_mem' := by
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    exact ⟨h1, by simpa using h1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [map_mul] at h
      rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha' h, hb' h]

omit [NumberField K] [StarRing K] in
theorem cO_coe [NumberField K] [StarRing K] (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, star_star]

theorem cO_mem_Tw {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w :=
  ⟨hs.2, by rw [cO_cO]; exact hs.1⟩

omit [NumberField K] [StarRing K] in
theorem hcompl_le_Tw [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ Tw w := by
  refine Submonoid.closure_le.2 ?_
  rintro s ⟨hs, hs'⟩
  exact ⟨hs, hs' (cO K s) rfl⟩

omit [NumberField K] [StarRing K] in
theorem smul_coe [NumberField K] [StarRing K] {m : Type*} (r : 𝓞 K) (v : m → K) : r • v = (r : K) • v :=
  (algebraMap_smul K r v).symm

omit [StarRing K] in
theorem vw_mul [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 ha)
      (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hb)]

omit [StarRing K] in
theorem vw_pow [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (a : K) (m : ℕ) :
    vw w (a ^ m) = (m : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

omit [StarRing K] in
theorem vw_int_nonneg [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : 0 ≤ vw w (r : K) := by
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coeIdeal_nonneg K w _

omit [StarRing K] in
theorem vw_unit [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (hr : r ∉ w.asIdeal) :
    vw w (r : K) = 0 := by
  classical
  have hr0 : r ≠ 0 := fun h => hr (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {r} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr0
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coeIdeal K w hJ]
  have h2 : ¬ w.asIdeal ∣ Ideal.span {r} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hr
  have h3 := mt (Associates.count_ne_zero_iff_dvd hJ w.irreducible).1 h2
  rw [not_not] at h3
  simp [h3]

omit [NumberField K] [StarRing K] in
theorem Tw_ne_zero [NumberField K] [StarRing K] {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : (s : K) ≠ 0 := by
  intro h
  apply hs.1
  have : s = 0 := RingOfIntegers.ext (by simpa using h)
  rw [this]; exact w.asIdeal.zero_mem

theorem main {n D : ℕ} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG) (l g : ℕ) (hl : 0 < l)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H) M, ((l : 𝓞 K) ^ g) • x ∈ M)
    (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K) (he : IsLocBasis (matLat P M) w e) :
    vw w (gramR (quotGram P H) e) ≤ (g : ℤ) * (D : ℤ) * vw w (l : K) :=
  _root_.UpperTheory.Reformulated.B.SelectionLemmas.main H P M hM l g hl hdual w e he

end ReductionFirst

theorem reduction_lemma_first : LemmaRa := by
  intro K _ _ _ _ K0 _ v0 _ n D H _ _ P _ M hM l g hl hdual w e he
  exact ReductionFirst.main H P M hM.fg l g hl hdual w e he

end Formalism.DivisionValues
