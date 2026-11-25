module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import Mathlib.Algebra.Order.Star.Real

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB, ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

theorem zero_ne_last (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h2
  omega

def sgd (d : ℂ) : ℂ := ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)

theorem sgd_sq (d : ℂ) (hd : 1 < ‖d‖) : sgd d * sgd d = d * conj d - 1 := by
  have hx : 0 ≤ Complex.normSq d - 1 := by
    have h1 : 1 < Complex.normSq d := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg d]
    linarith
  unfold sgd
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_one]

theorem star_sgd (d : ℂ) : star (sgd d) = sgd d := by
  unfold sgd
  exact Complex.conj_ofReal _

section entries
variable (hk : 1 ≤ k) (d : ℂ)
include hk

theorem character_first_entry : mud k d 0 0 = -conj d := by
  unfold mud
  simp
theorem character_last_entry : mud k d (Fin.last k) 0 = -sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [ite_eq_right (fun h => h0 h.1.symm), ite_eq_left ⟨rfl, rfl⟩]
theorem mud0L : mud k d 0 (Fin.last k) = sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [ite_eq_right (fun h => h0 h.2.symm), ite_eq_right (fun h => h0 h.1), ite_eq_left ⟨rfl, rfl⟩]
theorem mudLL : mud k d (Fin.last k) (Fin.last k) = d := by
  have h0 := zero_ne_last hk
  unfold mud
  rw [ite_eq_right (fun h => h0 h.1.symm), ite_eq_right (fun h => h0 h.2.symm), ite_eq_right (fun h => h0 h.1.symm),
    ite_eq_left ⟨rfl, rfl⟩]

theorem mud_col {l j : Fin (k + 1)} (hj0 : j ≠ 0) (hjL : j ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [ite_eq_right (fun h => hj0 h.2), ite_eq_right (fun h => hj0 h.2), ite_eq_right (fun h => hjL h.2),
    ite_eq_right (fun h => hjL h.2)]

theorem mud_row {l j : Fin (k + 1)} (hl0 : l ≠ 0) (hlL : l ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [ite_eq_right (fun h => hl0 h.1), ite_eq_right (fun h => hlL h.1), ite_eq_right (fun h => hl0 h.1),
    ite_eq_right (fun h => hlL h.1)]

theorem sum_two {f : Fin (k + 1) → ℂ} (hf : ∀ l, l ≠ 0 → l ≠ Fin.last k → f l = 0) :
    ∑ l, f l = f 0 + f (Fin.last k) := Finset.sum_eq_add 0 (Fin.last k) (zero_ne_last hk) (fun c _ hc => hf c hc.1 hc.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)

theorem mul_mud_col (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (k + 1)} (hj0 : j ≠ 0)
    (hjL : j ≠ Fin.last k) : (P * mud k d) i j = P i j := by
  rw [Matrix.mul_apply]
  simp [mud_col hk d hj0 hjL]

theorem mul_mud_blk (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) (hj : j = 0 ∨ j = Fin.last k) :
    (P * mud k d) i j = P i 0 * mud k d 0 j + P i (Fin.last k) * mud k d (Fin.last k) j := by
  rw [Matrix.mul_apply]
  apply sum_two hk
  intro l hl0 hlL
  rw [mud_row hk d hl0 hlL, ite_eq_right, mul_zero]
  rintro rfl
  rcases hj with h | h
  · exact hl0 h
  · exact hlL h

end entries

theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then (if i = Fin.last k then -1 else 1) else 0 := by
  unfold Hb
  rw [Matrix.diagonal_apply]

theorem mud_unitary (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d)ᴴ * Hb k * mud k d = Hb k := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  ext i j
  have hP : ∀ a b : Fin (k + 1), ((mud k d)ᴴ * Hb k) a b = star (mud k d b a) * (if b = Fin.last k then -1 else 1) := by
    intro a b; unfold Hb; rw [mul_diagonal, conjTranspose_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, ite_true, ite_eq_right h0L, star_neg, hss, Complex.star_def, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, character_first_entry hk, character_last_entry hk, ite_true, ite_eq_right h0L, ite_eq_right h0L.symm, hss,
        Complex.star_def]
      ring
    · simp only [mud_col hk d hi0 hiL, ite_eq_right (Ne.symm hi0), ite_eq_right (Ne.symm hiL), ite_eq_right hi0]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, mud0L hk, mudLL hk, ite_true, ite_eq_right h0L, star_neg, hss, Complex.star_def,
        Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, ite_true, ite_eq_right h0L, hss, Complex.star_def]
      linear_combination hs
    · simp only [mud_col hk d hi0 hiL, ite_eq_right (Ne.symm hi0), ite_eq_right (Ne.symm hiL), ite_eq_right hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hP, mud_row hk d hj0 hjL, Hb_apply]
    by_cases hij : i = j
    · subst hij; simp [hjL]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]; simp

theorem mud_conj_mul (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d).map (starRingEnd ℂ) * mud k d = 1 := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  have hc : ∀ a b : Fin (k + 1), ((mud k d).map (starRingEnd ℂ)) a b = conj (mud k d a b) := fun a b => rfl
  have hsc : conj (sgd d) = sgd d := hss
  ext i j
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hc, hc, Matrix.one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, character_last_entry hk, ite_true, map_neg, hsc, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, character_first_entry hk, ite_eq_right h0L.symm, map_neg, hsc]
      ring
    · simp only [mud_row hk d hi0 hiL, ite_eq_right hi0, ite_eq_right hiL]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hc, hc, Matrix.one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, mudLL hk, ite_eq_right h0L, map_neg, hsc, Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, mud0L hk, ite_true, map_neg, hsc]
      linear_combination -hs
    · simp only [mud_row hk d hi0 hiL, ite_eq_right hi0, ite_eq_right hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hc, mud_col hk d hj0 hjL, Matrix.one_apply]
    split_ifs <;> simp

theorem herm_mulVec {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    herm H (A *ᵥ u) (A *ᵥ v) = herm (Aᴴ * H * A) u v := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem herm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) (u v : Fin n → ℂ) :
    herm H (a • u) (b • v) = a * conj b * herm H u v := by
  unfold herm
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem herm_mud_last (hk : 1 ≤ k) (d : ℂ) :
    herm (Hb k) (mud k d *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -d := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp [Pi.single_apply, Hb_apply, mudLL hk d]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wbE_smul {r : ℕ} (a : ℂ) (v : Fin (k + 1) → ℂ) : wbE k r (a • v) = a • wbE k r v := by
  funext i
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [wbE, h]

theorem bvec_wI {r : ℕ} (j : Fin (k + 1)) : bvec (wI k r j) = wbE k r (Pi.single j 1) := by
  funext i
  simp only [bvec, wI, wbE, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 RepsA

theorem stReps (h : UnitaryGroupStructuralFacts) : StReps := by
  obtain ⟨hB2, -, hRC, hBCF, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClG, -, hClW, -⟩ := hB2
  intro k r Wp _ _ _ D X hD _ γ hγ c d hc hd
  have hk := D.k_pos
  obtain ⟨hγu, hγz⟩ := hγ
  have hT : 0 < Tz k r D.z := D.T_pos

  have hdet : IsUnit γ.det := by
    have h1 := congrArg Matrix.det hγu
    rw [det_mul, det_mul, det_conjTranspose] at h1
    have hHb : (Hb k).det = -1 := by
      unfold Hb; rw [det_diagonal, Finset.prod_ite_eq' Finset.univ (Fin.last k) (fun _ => (-1 : ℂ))]
      simp
    rw [hHb] at h1
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0] at h1; simp at h1
  have hγi : γ⁻¹ * γ = 1 := nonsing_inv_mul γ hdet
  have hγi' : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hdet
  have hHbi : (γ⁻¹)ᴴ * Hb k * γ⁻¹ = Hb k := by
    calc (γ⁻¹)ᴴ * Hb k * γ⁻¹ = (γ⁻¹)ᴴ * (γᴴ * Hb k * γ) * γ⁻¹ := by rw [hγu]
      _ = (γ * γ⁻¹)ᴴ * Hb k * (γ * γ⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hb k := by rw [hγi']; simp
  set μ := mud k d with hμ
  set M := γ * μ * γ⁻¹ with hM
  have hμu : μᴴ * Hb k * μ = Hb k := mud_unitary hk d hd

  have h1 : Mᴴ * Hb k * M = Hb k := by
    rw [show Mᴴ * Hb k * M = (γ⁻¹)ᴴ * (μᴴ * (γᴴ * Hb k * γ) * μ) * γ⁻¹ by
      simp only [hM, conjTranspose_mul, Matrix.mul_assoc]]
    rw [hγu, hμu, hHbi]

  set s : ℝ := Real.sqrt (Tz k r D.z) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hT).ne'
  have hzE : D.z = wbE k r ((s : ℂ) • (γ *ᵥ Pi.single (Fin.last k) 1)) := by
    rw [wbE_smul, ← embWb_mulVec, ← bvec_wI, hγz, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0,
      Complex.ofReal_one, one_smul]
  have hMγ : M * γ = γ * μ := by rw [hM, Matrix.mul_assoc, hγi, Matrix.mul_one]
  have h2 : herm (Hpk k r) (embWb k r M *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d := by
    conv_lhs => rw [hzE]
    rw [embWb_mulVec, herm_wbE, mulVec_smul, mulVec_mulVec, hMγ, ← mulVec_mulVec, herm_smul, herm_mulVec, hγu,
      herm_mud_last hk d, Complex.conj_ofReal, ← Complex.ofReal_mul, hs, Real.mul_self_sqrt hT.le]
    ring

  have hB1 : bigCell k r c 1 ∈ GV k r := bigCell_one_unitary c hc
  have hEM : embWb k r M ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨M, h1, rfl⟩
  have hg0 : g0 k r γ c d = bigCell k r c 1 * embWb k r M := (hBCF k r c M).1
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [hg0]; exact (hClG k r).mul_mem _ hB1 _ hEM.1
  · set Γ := embWb k r γ with hΓdef
    set Γi := embWb k r γ⁻¹ with hΓidef
    have hΓΓi : Γ * Γi = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi', embWb_one]
    have hΓiΓ : Γi * Γ = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi, embWb_one]
    have hΓinv : Γ⁻¹ = Γi := inv_eq_right_inv hΓΓi
    have hΓW : Γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγu, rfl⟩
    have hΓiW : Γi ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ⁻¹, hHbi, rfl⟩
    have hconjM : ∀ N, embWb k r (γ * N * γ⁻¹) = Γ * embWb k r N * Γi := by
      intro N; rw [embWb_mul, embWb_mul]
    have e1 : Γi * g0 k r γ c d * Γ = bigCell k r c μ := by
      rw [hg0, hM, hconjM, (hBCF k r c μ).1]
      rw [show Γi * (bigCell k r c 1 * (Γ * embWb k r μ * Γi)) * Γ =
          (Γi * bigCell k r c 1) * Γ * embWb k r μ * (Γi * Γ) by simp only [Matrix.mul_assoc]]
      rw [(hUWb k r).2.2 c Γi hΓiW, Matrix.mul_assoc (bigCell k r c 1) Γi Γ, hΓiΓ, Matrix.mul_one, Matrix.mul_one]
    have e2 : gbar k r γ (g0 k r γ c d) =
        bigCell k r (star c) 1 * embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) := by
      unfold gbar
      rw [hΓinv, e1, bigCell_map_conj, (hBCF k r (star c) _).1, hconjM, ← Matrix.mul_assoc Γ,
        (hUWb k r).2.2 (star c) Γ hΓW]
      simp only [Matrix.mul_assoc]
    have hB1' : bigCell k r (star c) 1 * bigCell k r c 1 = 1 := bigCell_star_mul c hc
    have hμc : μ.map (starRingEnd ℂ) * μ = 1 := mud_conj_mul hk d hd
    have hE : embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) * embWb k r M = 1 := by
      rw [← embWb_mul, hM, show γ * μ.map (starRingEnd ℂ) * γ⁻¹ * (γ * μ * γ⁻¹) =
          γ * (μ.map (starRingEnd ℂ) * μ) * γ⁻¹ by
            simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc γ⁻¹ γ, hγi, Matrix.one_mul],
        hμc, Matrix.mul_one, hγi', embWb_one]
    have hg0' : g0 k r γ c d = embWb k r M * bigCell k r c 1 := (hBCF k r c M).2
    unfold th
    rw [e2, Matrix.mul_inv_rev, inv_eq_right_inv hE, inv_eq_right_inv hB1', hg0']
  · have hz' : D.z' = D.z := hD.z_eq
    have hcond : Tz k r D.z * Tz k r D.z' <
        Complex.normSq (herm (Hpk k r) (embWb k r M *ᵥ D.z') D.z) := by
      rw [hz', h2, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
      have h1d : 1 < Complex.normSq d := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg d]
      have hTT : 0 < Tz k r D.z * Tz k r D.z := mul_pos hT hT
      nlinarith
    obtain ⟨h, hh, h', hh', hm⟩ :=
      hRC k r D.z D.z' D.μsec hk D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec (embWb k r M) hEM hcond
    rw [hz', h2] at hm
    rw [hz'] at hh'
    have hu := (hClW k r D.z).unit h hh
    have hu' := (hClW k r D.z).unit h' hh'
    refine ⟨h⁻¹, (hClW k r D.z).inv_mem h hh, h'⁻¹, (hClW k r D.z).inv_mem h' hh', ?_⟩
    rw [nonsing_inv_nonsing_inv h hu]
    show bigCell k r c (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * g0 k r γ c d * h'⁻¹
    have hE : embWb k r (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * embWb k r M * h'⁻¹ := by
      rw [hm]; simp only [← Matrix.mul_assoc]
      rw [mul_nonsing_inv h hu, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv h' hu', Matrix.mul_one]
    have hcm := (hUWb k r).2.2 c h ((hUWb k r).2.1 D.z hh)
    rw [(hBCF k r c _).1, hE, hg0]
    simp only [← Matrix.mul_assoc]
    rw [← hcm]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps =====
