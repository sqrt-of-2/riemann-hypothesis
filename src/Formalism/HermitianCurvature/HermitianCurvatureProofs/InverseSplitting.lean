module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates

@[expose] public section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace InverseSplitting

open C2x2

variable {m : ℕ}

noncomputable def lsStep (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) :
    ℕ → Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ
  | 0 => (1, 1)
  | n + 1 =>
    (Matrix.of fun i j => if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then l i j - ((lsStep w l n).1 * (lsStep w l n).2) i j else 0)
        else (lsStep w l n).1 i j,
     Matrix.of fun i j => if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then 0 else l i j - ((lsStep w l n).1 * (lsStep w l n).2) i j)
        else (lsStep w l n).2 i j)

structure Inv (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (n : ℕ)
    (A B : Matrix (Fin m) (Fin m) ℂ) : Prop where
  up : ∀ i j : Fin m, i < j → A i j = 0 ∧ B i j = 0
  diag : ∀ i, A i i = 1 ∧ B i i = 1
  far : ∀ i j : Fin m, j.val + n < i.val → A i j = 0 ∧ B i j = 0
  supA : ∀ i j : Fin m, j < i → ¬ (w.symm j < w.symm i) → A i j = 0
  supB : ∀ i j : Fin m, j < i → w.symm j < w.symm i → B i j = 0
  prod : ∀ i j : Fin m, i.val ≤ j.val + n → (A * B) i j = l i j

lemma inv_step (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) :
    ∀ n, Inv w l n (lsStep w l n).1 (lsStep w l n).2 := by
  intro n
  induction n with
  | zero =>
    show Inv w l 0 1 1
    refine ⟨fun i j h => ?_, fun i => by simp, fun i j h => ?_, fun i j h _ => ?_,
      fun i j h _ => ?_, fun i j h => ?_⟩
    · have hne : i ≠ j := ne_of_lt h
      simp [Matrix.one_apply_ne hne]
    · have hne : i ≠ j := fun e => by subst e; omega
      simp [Matrix.one_apply_ne hne]
    · simp [Matrix.one_apply_ne (ne_of_lt h).symm]
    · simp [Matrix.one_apply_ne (ne_of_lt h).symm]
    · rw [Matrix.one_mul]
      by_cases hij : i = j
      · subst hij
        simp [hl.2 i]
      · have hlt : i < j := by
          have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
          rw [Fin.lt_def]
          omega
        rw [Matrix.one_apply_ne hij, hl.1 i j hlt]
  | succ n ih =>
    obtain ⟨hup, hdiag, hfar, hsupA, hsupB, hprod⟩ := ih
    set A := (lsStep w l n).1 with hAdef
    set B := (lsStep w l n).2 with hBdef
    have hA' : ∀ i j, (lsStep w l (n + 1)).1 i j = if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then l i j - (A * B) i j else 0) else A i j := fun i j => rfl
    have hB' : ∀ i j, (lsStep w l (n + 1)).2 i j = if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then 0 else l i j - (A * B) i j) else B i j := fun i j => rfl
    refine ⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_, fun i j h hw => ?_,
      fun i j h hw => ?_, fun i j h => ?_⟩
    · have hv : ¬ i.val = j.val + n + 1 := by
        rw [Fin.lt_def] at h
        omega
      rw [hA', hB', ite_eq_right hv, ite_eq_right hv]
      exact hup i j h
    · have hv : ¬ i.val = i.val + n + 1 := by omega
      rw [hA', hB', ite_eq_right hv, ite_eq_right hv]
      exact hdiag i
    · have hv : ¬ i.val = j.val + n + 1 := by omega
      rw [hA', hB', ite_eq_right hv, ite_eq_right hv]
      exact hfar i j (by omega)
    · rw [hA']
      split_ifs with hv
      · rfl
      · exact hsupA i j h hw
    · rw [hB']
      split_ifs with hv
      · rfl
      · exact hsupB i j h hw
    · rw [Matrix.mul_apply]
      by_cases hgap : i.val = j.val + n + 1
      ·
        have hji : j ≠ i := fun e => by subst e; omega
        have hAij : A i j = 0 := (hfar i j (by omega)).1
        have hBij : B i j = 0 := (hfar i j (by omega)).2
        have hterm : ∀ k, (lsStep w l (n + 1)).1 i k * (lsStep w l (n + 1)).2 k j =
            A i k * B k j + (if k = j then (lsStep w l (n + 1)).1 i j else 0) +
              (if k = i then (lsStep w l (n + 1)).2 i j else 0) := by
          intro k
          by_cases hkj : k = j
          · subst hkj
            have hv : ¬ k.val = k.val + n + 1 := by omega
            rw [hB' k k, ite_eq_right hv, (hdiag k).2, hAij, ite_eq_left rfl, ite_eq_right hji]
            simp
          by_cases hki : k = i
          · subst hki
            have hv : ¬ k.val = k.val + n + 1 := by omega
            rw [hA' k k, ite_eq_right hv, (hdiag k).1, hBij, ite_eq_right hkj, ite_eq_left rfl]
            simp
          have hv1 : ¬ i.val = k.val + n + 1 := fun e => hkj (Fin.ext (by omega))
          have hv2 : ¬ k.val = j.val + n + 1 := fun e => hki (Fin.ext (by omega))
          rw [hA' i k, hB' k j, ite_eq_right hv1, ite_eq_right hv2, ite_eq_right hkj, ite_eq_right hki]
          simp
        rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ _),
          ite_eq_left (Finset.mem_univ _), ← Matrix.mul_apply, hA', hB', ite_eq_left hgap, ite_eq_left hgap]
        split_ifs <;> ring
      ·
        have hle : i.val ≤ j.val + n := by omega
        rw [← hprod i j hle, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk1 : i.val = k.val + n + 1
        · have hkj : k < j := by
            rw [Fin.lt_def]
            omega
          have hv2 : ¬ k.val = j.val + n + 1 := by omega
          rw [hB' k j, ite_eq_right hv2, (hup k j hkj).2]
          simp
        · rw [hA' i k, ite_eq_right hk1]
          by_cases hk2 : k.val = j.val + n + 1
          · have hik : i < k := by
              rw [Fin.lt_def]
              omega
            rw [(hup i k hik).1]
            simp
          · rw [hB' k j, ite_eq_right hk2]

end InverseSplitting

open C2x2 InverseSplitting

lemma conj_mul_eq_mul_conj {m : ℕ} (P X Y : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P⁻¹ * (X * Y) * P = (P⁻¹ * X * P) * (P⁻¹ * Y * P) := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

lemma conj_inv_eq_inv_conj {m : ℕ} (P X : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    (P⁻¹ * X * P)⁻¹ = P⁻¹ * X⁻¹ * P := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

theorem lower_triangular_splitting : C2.LowSplit := by
  intro m P hP l hl
  obtain ⟨w, d, hd, rfl⟩ := hP
  set Q : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a i => if i = w a then (d a)⁻¹ else 0 with hQ
  have hQP : Q * C2.monoP w d = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [hQ, C2.monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hab : a = b
    · subst hab
      simp [hd a]
    · simp [Matrix.one_apply_ne hab, Ne.symm hab]
  have hPinv : (C2.monoP w d)⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have hPdet : IsUnit (C2.monoP w d).det := Matrix.isUnit_det_of_left_inverse hQP
  have hconj : ∀ (X : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m),
      ((C2.monoP w d)⁻¹ * X * C2.monoP w d) a b = (d a)⁻¹ * X (w a) (w b) * d b := by
    intro X a b
    rw [hPinv, Matrix.mul_apply]
    simp only [Matrix.mul_apply, hQ, C2.monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have I := inv_step w l hl m
  set A := (lsStep w l m).1 with hAdef
  set B := (lsStep w l m).2 with hBdef
  have hAB : l = A * B := by
    ext i j
    exact (I.prod i j (by omega)).symm
  have hAL : A ∈ C2.LTset m := ⟨fun i j h => (I.up i j h).1, fun i => (I.diag i).1⟩
  have hBL : B ∈ C2.LTset m := ⟨fun i j h => (I.up i j h).2, fun i => (I.diag i).2⟩
  have hAc : (C2.monoP w d)⁻¹ * A * C2.monoP w d ∈ C2.LTset m := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [hconj]
      rcases lt_trichotomy (w a) (w b) with h | h | h
      · rw [(I.up _ _ h).1]
        simp
      · exact absurd (w.injective h) (ne_of_lt hab)
      · rw [I.supA _ _ h (by simpa using (not_lt.2 hab.le))]
        simp
    · rw [hconj, (I.diag (w a)).1]
      field_simp [hd a]
  have hBc : (C2.monoP w d)⁻¹ * B * C2.monoP w d ∈ C2.UTset m := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [hconj]
      rcases lt_trichotomy (w a) (w b) with h | h | h
      · rw [(I.up _ _ h).2]
        simp
      · exact absurd (w.injective h) (ne_of_lt hba).symm
      · rw [I.supB _ _ h (by simpa using hba)]
        simp
    · rw [hconj, (I.diag (w a)).2]
      field_simp [hd a]
  refine ⟨(A, B), ⟨⟨hAL, hAc⟩, ⟨hBL, hBc⟩, hAB⟩, ?_⟩
  rintro ⟨A2, B2⟩ ⟨hA2, hB2, hl2⟩
  have hl2' : l = A2 * B2 := hl2
  have hAdet : IsUnit A.det := by rw [_root_.Formalism.FourierDecayAlt.P.C2x2.lt_det hAL]; exact isUnit_one
  have hB2det : IsUnit B2.det := by rw [_root_.Formalism.FourierDecayAlt.P.C2x2.lt_det hB2.1]; exact isUnit_one
  have hkey : A⁻¹ * A2 = B * B2⁻¹ := by
    calc A⁻¹ * A2 = A⁻¹ * A2 * (B2 * B2⁻¹) := by
          rw [Matrix.mul_nonsing_inv B2 hB2det, Matrix.mul_one]
      _ = A⁻¹ * (A2 * B2) * B2⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * B) * B2⁻¹ := by rw [← hl2', ← hAB]
      _ = B * B2⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAdet, Matrix.one_mul]
  have hYL : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d ∈ C2.LTset m := by
    rw [conj_mul_eq_mul_conj _ _ _ hPdet, ← conj_inv_eq_inv_conj _ _ hPdet]
    exact _root_.Formalism.FourierDecayAlt.P.C2x2.lt_mul (_root_.Formalism.FourierDecayAlt.P.C2x2.lt_inv hAc) hA2.2
  have hYU : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d ∈ C2.UTset m := by
    rw [hkey, conj_mul_eq_mul_conj _ _ _ hPdet, ← conj_inv_eq_inv_conj _ _ hPdet]
    exact _root_.Formalism.FourierDecayAlt.P.C2x2.ut_mul hBc (_root_.Formalism.FourierDecayAlt.P.C2x2.ut_inv hB2.2)
  have hY : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hYL.1 i j h, Matrix.one_apply_ne (ne_of_lt h)]
    · subst h
      rw [hYL.2 i, Matrix.one_apply_eq]
    · rw [hYU.1 i j h, Matrix.one_apply_ne (ne_of_lt h).symm]
  have hZ : A⁻¹ * A2 = 1 := by
    calc A⁻¹ * A2 = C2.monoP w d * ((C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d) *
          (C2.monoP w d)⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one,
            Matrix.mul_nonsing_inv_cancel_left _ _ hPdet]
      _ = 1 := by rw [hY, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPdet]
  have hA2A : A2 = A := by
    calc A2 = A * (A⁻¹ * A2) := (Matrix.mul_nonsing_inv_cancel_left A A2 hAdet).symm
      _ = A := by rw [hZ, Matrix.mul_one]
  have hB2B : B2 = B := by
    calc B2 = A⁻¹ * (A * B2) := (Matrix.nonsing_inv_mul_cancel_left A B2 hAdet).symm
      _ = A⁻¹ * (A * B) := by rw [← hA2A, ← hl2', hAB, hA2A]
      _ = B := Matrix.nonsing_inv_mul_cancel_left A B hAdet
  rw [hA2A, hB2B]

theorem upper_splitting : C2.UpSplit := by
  intro m P hP u hu
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, huniq⟩ := lower_triangular_splitting m P hP uᴴ (_root_.Formalism.FourierDecayAlt.P.C2x2.ut_conjT hu)
  refine ⟨(bᴴ, aᴴ), ⟨_root_.Formalism.FourierDecayAlt.P.C2x2.lt_conjT hb.1, _root_.Formalism.FourierDecayAlt.P.C2x2.lt_conjT ha.1,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hb,
    by simpa only [Matrix.conjTranspose_conjTranspose] using ha, ?_⟩, ?_⟩
  · show u = bᴴ * aᴴ
    rw [← Matrix.conjTranspose_mul, ← hab, Matrix.conjTranspose_conjTranspose]
  · rintro ⟨q1, q2⟩ ⟨_, _, hq1c, hq2c, hq⟩
    have h := huniq (q2ᴴ, q1ᴴ) ⟨hq2c, hq1c, by
      show uᴴ = q2ᴴ * q1ᴴ
      rw [← Matrix.conjTranspose_mul, ← hq]⟩
    simp only [Prod.mk.injEq] at h
    rw [← h.1, ← h.2, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]

end Formalism.FourierDecayAlt.P
