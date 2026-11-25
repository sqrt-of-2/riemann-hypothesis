module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis

@[expose] public section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

lemma flagSpan_vanish (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : v ∈ C2.flagSpan k r z a) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    have hbr : b.val < r := by have := a.isLt; rw [Fin.lt_def] at hb; omega
    simp only [fvec, dite_eq_left hbr, bvec, Pi.single_apply, eI]
    rw [ite_eq_right]
    intro e; rw [Fin.lt_def] at hb; have := congrArg Fin.val e; simp at this; omega
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma mulVec_bvec (M : B.Mat k r) (x : Fin (2 * r + k + 1)) : M *ᵥ bvec x = fun i => M i x := by
  funext i; simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def wpart (s : B.Mat k r) : B.Mat k r := fun i j =>
  if r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k then s i j else if i = j then 1 else 0

lemma zero_block (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    ∀ n : ℕ, ∀ a : Fin r, a.val = n → s (esI k r a) j = 0 := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    have e := congrFun (congrFun hU (eI k r a)) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at e
    simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
    have hH : Hpk k r (eI k r a) j = 0 := by
      rw [GBasic.Hpk_eq, ite_eq_right]
      intro h'; have := congrArg Fin.val h'
      rw [GBasic.sig_lo _ _ _ (by simp [eI])] at this; simp [eI] at this; omega
    rw [hH, Finset.sum_eq_single (eI k r a)] at e
    · rw [hcol a _ (by simp [eI]), ite_eq_left rfl, star_one, one_mul] at e
      have hsig : GBasic.sig k r (eI k r a) = esI k r a := by
        apply Fin.ext; rw [GBasic.sig_lo _ _ _ (by simp [eI])]; simp [eI, esI]
      have hsg : GBasic.sgn k r (eI k r a) = 1 := by
        unfold GBasic.sgn; rw [ite_eq_right]; simp [eI]; omega
      rw [hsig, hsg, one_mul] at e
      exact e
    · intro p _ hp
      by_cases hpa : a.val ≤ p.val
      · rw [hcol a p hpa, ite_eq_right hp, star_zero, zero_mul]
      · push Not at hpa
        have hpr : p.val < r := by omega
        have hsig : GBasic.sig k r p = esI k r ⟨p.val, hpr⟩ := by
          apply Fin.ext; rw [GBasic.sig_lo _ _ _ hpr]; simp [esI]
        rw [hsig, ih p.val (by omega) ⟨p.val, hpr⟩ rfl, mul_zero, mul_zero]
    · simp

end FlagSpanVanishing

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

lemma sig_notW (x : Fin (2 * r + k + 1)) (hx : ¬ (r ≤ x.val ∧ x.val ≤ r + k)) :
    ¬ (r ≤ (GBasic.sig k r x).val ∧ (GBasic.sig k r x).val ≤ r + k) := by
  have := GBasic.sig_val k r x
  have hx' := x.isLt
  split_ifs at this <;> omega

lemma sig_fixes_middle_block (x : Fin (2 * r + k + 1)) (hx : r ≤ x.val ∧ x.val ≤ r + k) : GBasic.sig k r x = x :=
  GBasic.sig_mid k r x hx.1 hx.2

lemma wpart_uh (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0) :
    wpart s ∈ UH (Hpk k r) := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  show (wpart s)ᴴ * Hpk k r * wpart s = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun hU i) j
      rw [Matrix.mul_assoc, Matrix.mul_apply] at e
      simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_fixes_middle_block p hp]
        simp only [wpart, ite_eq_left (And.intro hp.1 (And.intro hp.2 (And.intro hi.1 hi.2))),
          ite_eq_left (And.intro hp.1 (And.intro hp.2 (And.intro hj.1 hj.2)))]
      · have h1 : wpart s p i = 0 := by
          simp only [wpart]; rw [ite_eq_right (fun h => hp ⟨h.1, h.2.1⟩), ite_eq_right]
          intro e; rw [e] at hp; exact hp hi
        rw [h1, star_zero, zero_mul]
        by_cases hpr : p.val < r
        · have : r + k < (GBasic.sig k r p).val := by rw [GBasic.sig_lo _ _ _ hpr]; omega
          rw [hA _ j this hj.1 hj.2, mul_zero, mul_zero]
        · have : r + k < p.val := by omega
          rw [hA p i this hi.1 hi.2, star_zero, zero_mul]
    · rw [Finset.sum_eq_single (GBasic.sig k r j)]
      · have h1 : wpart s (GBasic.sig k r j) i = 0 := by
          simp only [wpart]
          rw [ite_eq_right (fun h => sig_notW j hj ⟨h.1, h.2.1⟩), ite_eq_right]
          intro e; rw [← e] at hi; exact sig_notW j hj hi
        rw [h1, star_zero, zero_mul, GBasic.Hpk_eq, ite_eq_right]
        intro e; rw [sig_fixes_middle_block i hi] at e; rw [e] at hj; exact hj hi
      · intro p _ hp
        have : wpart s (GBasic.sig k r p) j = 0 := by
          simp only [wpart]; rw [ite_eq_right (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), ite_eq_right]
          intro e; apply hp; rw [← e, GBasic.sig_sig]
        rw [this, mul_zero, mul_zero]
      · simp
  · rw [Finset.sum_eq_single i]
    · have h1 : wpart s i i = 1 := by
        simp only [wpart]; rw [ite_eq_right (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      have h2 : wpart s (GBasic.sig k r i) j = if GBasic.sig k r i = j then 1 else 0 := by
        simp only [wpart]; rw [ite_eq_right (fun h => sig_notW i hi ⟨h.1, h.2.1⟩)]
      rw [h1, star_one, one_mul, h2, GBasic.Hpk_eq]
      by_cases e : GBasic.sig k r i = j
      · rw [ite_eq_left e, ite_eq_left e.symm, mul_one]
      · rw [ite_eq_right e, ite_eq_right (fun h => e h.symm), mul_zero]
    · intro p _ hp
      have : wpart s p i = 0 := by
        simp only [wpart]; rw [ite_eq_right (fun h => hi ⟨h.2.2.1, h.2.2.2⟩), ite_eq_right hp]
      rw [this, star_zero, zero_mul]
    · simp

end FlagSpanVanishing

open C2x5 C2x7 FlagSpanVanishing

theorem standard_flag_property : C2.SFlag := by
  intro k r z hz
  ext s
  constructor
  · rintro ⟨hs, hfl⟩
    have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        s i (eI k r a) = if i = eI k r a then 1 else 0 := by
      intro a i hi
      have h := flagSpan_vanish z (Fin.castSucc a) _ (hfl (Fin.castSucc a)) i (by simpa using hi)
      have hf : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by rw [fvec, dite_eq_left (by simp)]; rfl
      rw [hf, mulVec_bvec, Pi.sub_apply, sub_eq_zero] at h
      rw [h]; simp [bvec, Pi.single_apply]
    have hzc : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (s *ᵥ z) i = z i := by
      intro i hi
      have h := flagSpan_vanish z (Fin.last r) _ (hfl (Fin.last r)) i (by simpa using hi)
      have hf : fvec k r z (Fin.last r) = z := by rw [fvec, dite_eq_right (by simp)]
      rw [hf, Pi.sub_apply, sub_eq_zero] at h; exact h
    have hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0 := by
      intro p j hp hj1 hj2
      have hpa : 2 * r + k - p.val < r := by omega
      have e : esI k r ⟨2 * r + k - p.val, hpa⟩ = p := Fin.ext (by simp [esI]; omega)
      rw [← e]; exact zero_block s hs hcol j hj1 hj2 _ _ rfl
    have hhU := wpart_uh s hs hA
    set h := wpart s with hh
    have hhW : h ∈ UWset k r z := by
      refine ⟨hhU, fun a => ⟨?_, ?_⟩, ?_⟩
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [ite_eq_right (by intro h'; have := h'.2.2.1; simp only [eI] at this; omega)]
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [ite_eq_right (by intro h'; have := h'.2.2.2; simp only [esI] at this; omega)]
      · funext i
        by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
        · rw [← hzc i hi.1]
          simp only [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · simp only [hh, wpart, ite_eq_left (And.intro hi.1 (And.intro hi.2 hj))]
          · have hzj : z j = 0 := hz.1 j (by omega)
            rw [hzj, mul_zero, mul_zero]
        · simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single i]
          · simp only [hh, wpart]; rw [ite_eq_right (fun h' => hi ⟨h'.1, h'.2.1⟩)]; simp
          · intro j _ hj
            simp only [hh, wpart]; rw [ite_eq_right (fun h' => hi ⟨h'.1, h'.2.1⟩), ite_eq_right (Ne.symm hj), zero_mul]
          · simp
    have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hhU
    have hblk := WeylGroupFacts.uw_block (WeylGroupFacts.uw_inv hhW)
    refine ⟨h, hhW, h⁻¹ * s, ?_, ?_⟩
    · rw [WeylGroupFacts.nset_iff]
      refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hhU) hs, fun i j hj hij => ?_⟩
      rw [Matrix.mul_apply]
      by_cases hjr : j.val < r
      · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
        have hterm : ∀ p, h⁻¹ i p * s p j = (if i = p then 1 else 0) * s p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr)]
          · have := hcol ⟨j.val, hjr⟩ p (by simp; omega)
            rw [e, ite_eq_right (fun e' => hpr (by rw [e']; exact hjr))] at this
            rw [this, mul_zero, mul_zero]
        simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        have := hcol ⟨j.val, hjr⟩ i (by simp; omega)
        rw [e] at this; exact this
      · have hir : r ≤ i.val := by omega
        have hterm : ∀ p, h⁻¹ i p * s p j = h⁻¹ i p * h p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr), ite_eq_right (fun e' => by rw [e'] at hir; omega), zero_mul, zero_mul]
          · by_cases hpk : p.val ≤ r + k
            · simp only [hh, wpart]
              rw [ite_eq_left ⟨by omega, hpk, by omega, hj⟩]
            · rw [hA p j (by omega) (by omega) hj]
              simp only [hh, wpart]
              rw [ite_eq_right (fun h' => hpk h'.2.1), ite_eq_right (fun e' => by rw [e'] at hpk; exact hpk hj)]
        simp only [hterm]
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hhu, Matrix.one_apply]
    · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  · intro hs
    refine ⟨Sset_UH hs, fun a => ?_⟩
    obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    rw [colEq hsF a]
    have hfa : fvec k r z a = ∑ c, (if c = a then (1 : ℂ) else 0) • fvec k r z c := by
      simp [ite_smul]
    rw [hfa, ← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro c _
    rw [← sub_smul]
    by_cases hca : c < a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hca⟩, rfl⟩)
    · have : U c a - (if c = a then 1 else 0) = 0 := by
        rcases eq_or_lt_of_le (not_lt.mp hca) with e | e
        · rw [← e, hU2, ite_eq_left rfl, sub_self]
        · rw [hU1 c a e, ite_eq_right (ne_of_gt e), sub_self]
      rw [this, zero_smul]; exact Submodule.zero_mem _

end Formalism.FourierDecayAlt.P
