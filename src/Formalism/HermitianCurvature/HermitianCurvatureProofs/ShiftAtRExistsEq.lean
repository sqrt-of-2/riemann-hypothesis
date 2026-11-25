module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def uPlus (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l + 1 then u i + n₀ else u i

def uMinus (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l then u i - n₀ else u i

structure WigData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {Wq : Type} [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ) (l n₀ : ℕ)
    (b : ℝ) where
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  πp : B.Mat k r → (Wqp →L[ℂ] Wqp)
  πm : B.Mat k r → (Wqm →L[ℂ] Wqm)
  Ap : B.Mat k r → (Wqp →L[ℂ] Wq)
  Am : B.Mat k r → (Wqm →L[ℂ] Wq)
  typeP : Q.IsType k r z' πp (uPlus u l n₀)
  typeM : Q.IsType k r z' πm (uMinus u l n₀)
  polyP : PolyOp (n₀ * (r + 1)) Ap
  polyM : PolyOp (n₀ * (r + 1)) Am
  equivP : WigEquiv z z' π' πp Ap
  equivM : WigEquiv z z' π' πm Am
  upperP : WigUpper z z' n₀ Ap
  upperM : WigUpper z z' n₀ Am
  lower : WigLower z z' b n₀ Ap Am

attribute [instance] WigData.iNp WigData.iIp WigData.iFp WigData.iNm WigData.iIm WigData.iFm

def WigExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → Q.IsType k r z' π' u →
    (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) →
    1 ≤ l → l < k → (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1) → 3 ≤ b → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) →
    Nonempty (WigData k r z z' π' u l n₀ b)

def PlaceSwapExists : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (p : KB.Pl P Wp Wq) (u'' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ),
    Q.IsType P.k P.r p.T.base.z' π'' u'' → (shP P P.u u'').OK → 1 ≤ l0 → l0 ≤ P.k →
    ∃ q : KB.Pl (shP P P.u u'') Wp Wq', SwapTie p q ∧ q.T.base.π' = π'' ∧ q.l0 = l0

theorem okPlus (P : M.Par) (l n₀ : ℕ) (hOK : P.OK) (hu : P.u = P.u') (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1)) : (shP P P.u (uPlus P.u' l n₀)).OK := by
  have key : ∀ a b c d : ℝ, a + 1 ≤ c → a + 1 ≤ d → b + 1 ≤ c → b + 1 ≤ d →
      max a b + 1 / 2 ≤ min c d - 1 / 2 := by
    intro a b c d h1 h2 h3 h4
    have ha : a + 1 ≤ min c d := le_min h1 h2
    have hb : b + 1 ≤ min c d := le_min h3 h4
    have hm : max a b ≤ min c d - 1 := max_le (by linarith) (by linarith)
    linarith
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨n, hn⟩ := hOK.int_u' i hi
    by_cases h : i = l + 1
    · refine ⟨n + n₀, ?_⟩
      simp only [shP, uPlus, ite_eq_left h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [shP, uPlus, ite_eq_right h]
      exact hn
  · have hg := hOK.gap i hi
    simp only [Formalism.FourierDecayAlt.M.Par.lo, Formalism.FourierDecayAlt.M.Par.hi, shP, uPlus] at hg ⊢
    rw [hu] at hg ⊢
    simp only [max_self, min_self] at hg
    by_cases h1 : i = l
    · subst h1
      simp only [ite_true, show ¬ (i = i + 1) by omega, ite_false]
      exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases h2 : i = l + 1
      · subst h2
        simp only [show ¬ (l + 1 + 1 = l + 1) by omega, ite_false, ite_true]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
      · simp only [show ¬ (i + 1 = l + 1) by omega, ite_false, ite_eq_right h2]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

theorem okMinus (P : M.Par) (l n₀ : ℕ) (hOK : P.OK) (hu : P.u = P.u') (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1)) : (shP P P.u (uMinus P.u' l n₀)).OK := by
  have key : ∀ a b c d : ℝ, a + 1 ≤ c → a + 1 ≤ d → b + 1 ≤ c → b + 1 ≤ d →
      max a b + 1 / 2 ≤ min c d - 1 / 2 := by
    intro a b c d h1 h2 h3 h4
    have ha : a + 1 ≤ min c d := le_min h1 h2
    have hb : b + 1 ≤ min c d := le_min h3 h4
    have hm : max a b ≤ min c d - 1 := max_le (by linarith) (by linarith)
    linarith
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨n, hn⟩ := hOK.int_u' i hi
    by_cases h : i = l
    · refine ⟨n - n₀, ?_⟩
      simp only [shP, uMinus, ite_eq_left h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [shP, uMinus, ite_eq_right h]
      exact hn
  · have hg := hOK.gap i hi
    simp only [Formalism.FourierDecayAlt.M.Par.lo, Formalism.FourierDecayAlt.M.Par.hi, shP, uMinus] at hg ⊢
    rw [hu] at hg ⊢
    simp only [max_self, min_self] at hg
    by_cases h1 : i = l
    · subst h1
      simp only [ite_true, show ¬ (i + 1 = i) by omega, ite_false]
      exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases h2 : i + 1 = l
      · subst h2
        simp only [show ¬ (i = i + 1) by omega, ite_false, ite_true]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
      · simp only [ite_eq_right h1, ite_eq_right h2]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

end

end Formalism.FourierDecayAlt.P.CutBPEq
