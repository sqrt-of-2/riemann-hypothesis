module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStepOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

theorem measure_isomorphism_at_infinity : IsoStep := by
  intro E _ _ _ S r T aa F0 Λ hC f hF
  have hE := first_dual_reduction E S r T aa F0 Λ hC
  have hFd := second_dual_reduction E S r T aa F0 Λ hC f hF
  obtain ⟨_, _, _, _, _, hne, _, ⟨x, hx⟩⟩ := hC
  obtain ⟨x', hx'⟩ : ∃ x' : 𝓞 E, (x' : E) = star (x : E) :=
    ⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩
  have herm : ∀ u v, star (S.hT u v) = S.hT v u := fun u v => by
    rw [← starRingEnd_apply]
    exact LinearMap.isSymm_def.1 S.herm u v
  have hfe : ∀ c a, S.hT (f c) (F0.e a) = if a = c then 1 else 0 := fun c a => by
    rw [← herm, hF.1 a c]
    by_cases h : a = c <;> simp [h]
  have addm : ∀ {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} {u v : E}, u ∈ I → v ∈ I → u + v ∈ I :=
    fun hu hv => FractionalIdeal.mem_coeToSubmodule.1
      (Submodule.add_mem _ (FractionalIdeal.mem_coeToSubmodule.2 hu) (FractionalIdeal.mem_coeToSubmodule.2 hv))
  have negm : ∀ {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} {u : E}, u ∈ I → -u ∈ I :=
    fun hu => FractionalIdeal.mem_coeToSubmodule.1 (Submodule.neg_mem _ (FractionalIdeal.mem_coeToSubmodule.2 hu))
  have zerom : ∀ {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}, (0 : E) ∈ I :=
    FractionalIdeal.mem_coeToSubmodule.1 (Submodule.zero_mem _)
  have summ : ∀ {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (g : Fin r → E), (∀ k, g k ∈ I) →
      ∑ k, g k ∈ I :=
    fun g hg => FractionalIdeal.mem_coeToSubmodule.1 (Submodule.sum_mem _ (fun k _ => FractionalIdeal.mem_coeToSubmodule.2 (hg k)))
  have intm : ∀ {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (o : 𝓞 E) {t : E}, t ∈ I → (o : E) * t ∈ I := by
    intro I o t ht
    have h1 := Submodule.smul_mem (I : Submodule (𝓞 E) E) o (FractionalIdeal.mem_coeToSubmodule.2 ht)
    rw [Algebra.smul_def] at h1
    exact FractionalIdeal.mem_coeToSubmodule.1 h1
  have hff : ∀ k b, S.hT (f k) (f b) ∈ aa k * aa b := by
    intro k b
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (S.hT (f k) (f b)) * (aa b)⁻¹ ≤ aa k := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      have h1 : S.hT (f k) (j • f b) ∈ aa k := hF.2.2 k _ (hFd b j hj)
      rw [map_smul, smul_eq_mul] at h1
      rw [smul_mul_assoc, mul_comm (S.hT (f k) (f b)) j]
      exact FractionalIdeal.mem_coeToSubmodule.1 (Submodule.smul_mem _ z (FractionalIdeal.mem_coeToSubmodule.2 h1))
    have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (S.hT (f k) (f b)) * (aa b)⁻¹ * aa b ≤
        aa k * aa b := by gcongr
    rw [mul_assoc, inv_mul_cancel₀ (hne b), mul_one] at h2
    exact h2 (FractionalIdeal.mem_spanSingleton_self _ _)
  have hprod : ∀ k b (t s : E), t ∈ aa k * aa b → s ∈ (aa k)⁻¹ → t * s ∈ aa b := by
    intro k b t s ht hs
    have h1 := FractionalIdeal.mul_mem_mul ht hs
    rwa [mul_comm (aa k) (aa b), mul_assoc, mul_inv_cancel₀ (hne k), mul_one] at h1
  let c : Fin r → Fin r → E := fun a b =>
    if a < b then -S.hT (f a) (f b) else if a = b then -(S.hT (f b) (f b) * (x : E)) else 0
  let f' : Fin r → S.V := fun b => f b + ∑ k, c k b • F0.e k
  have hc_mem : ∀ k b, star (c k b) ∈ aa k * aa b := by
    intro k b
    simp only [c]
    split_ifs with h1 h2
    · rw [star_neg, herm]
      exact negm (by rw [mul_comm]; exact hff b k)
    · subst h2
      rw [star_neg, star_mul', herm, ← hx', mul_comm (S.hT (f k) (f k)) (x' : E)]
      exact negm (intm x' (hff k k))
    · rw [star_zero]
      exact zerom
  have hsum : ∀ a b, S.hT (f a) (f b) + c a b + star (c b a) = 0 := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · have h1 : ¬ b < a := not_lt.2 hab.le
      have h2 : b ≠ a := hab.ne'
      simp [c, hab, h1, h2]
    · subst hab
      simp only [c, lt_irrefl, ↓reduceIte]
      rw [star_neg, star_mul', herm]
      have h3 : S.hT (f a) (f a) * (x : E) + S.hT (f a) (f a) * star (x : E) = S.hT (f a) (f a) := by
        rw [← mul_add, hx, mul_one]
      linear_combination -h3
    · have h1 : ¬ a < b := not_lt.2 hab.le
      have h2 : a ≠ b := hab.ne'
      simp [c, hab, h1, h2, herm]
  refine ⟨f', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b

    simp [f', map_sum, F0.e_iso, hF.1]
  · intro b

    simp [f', map_sum, F0.z_orth, hF.2.1]
  · intro b l hl
    have hexp : S.hT (f' b) l = S.hT (f b) l + ∑ k, star (c k b) * S.hT (F0.e k) l := by

      simp [f', map_sum, starRingEnd_apply]
    rw [hexp]
    exact addm (hF.2.2 b l hl) (summ _ (fun k => hprod k b _ _ (hc_mem k b) (hE k l hl)))
  · intro a b
    have h := hsum a b

    simp [f', map_sum, hfe, hF.1, F0.e_iso, Finset.sum_ite_eq', starRingEnd_apply]
    linear_combination h

end PI.SRW
