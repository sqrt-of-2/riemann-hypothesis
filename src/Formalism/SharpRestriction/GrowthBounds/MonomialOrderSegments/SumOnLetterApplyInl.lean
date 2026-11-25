module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DdivOnLetterMonomial, Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DdivOnLetterMonomial =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DdivOnLetterMonomial", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial\npublic import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

section Gen

variable {σ : Type} [Fintype σ]

def bin (M α : σ →₀ ℕ) : K := ∏ x, ((α x).choose (M x) : K)

private theorem finsupp_prod_choose_eq_bin_of_le (M α : σ →₀ ℕ) (h : M ≤ α) :
    (α.prod fun x k => (k.choose (M x) : K)) = bin M α := by
  unfold bin Finsupp.prod
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => ?_
  have h0 : α x = 0 := by simpa using hx
  have hle : M x ≤ α x := by
    exact Finsupp.le_def.1 h x
  have h1 : M x = 0 := by omega
  simp [h0, h1]

theorem ddiv_monomial' (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) = monomial (α - M) (c * bin M α) := by
  rw [ddiv_monomial]
  by_cases h : M ≤ α
  · rw [ite_eq_left h, finsupp_prod_choose_eq_bin_of_le M α h]
  · rw [ite_eq_right h]
    obtain ⟨x, hx⟩ : ∃ x, α x < M x := by
      by_contra hc
      push Not at hc
      apply h
      exact Finsupp.le_def.2 hc
    have h0 : (bin M α : K) = 0 := by
      unfold bin
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Nat.choose_eq_zero_of_lt hx])
    rw [h0, mul_zero, map_zero]

theorem vge_bin (v : AddValuation K (WithTop ℚ)) (M α : σ →₀ ℕ) : vge v 0 (bin M α : K) := by
  have h : (bin M α : K) = ((∏ x, (α x).choose (M x) : ℕ) : K) := by
    rw [bin, Nat.cast_prod]
  rw [h]
  exact vge_natCast v _

theorem ddiv_ddiv_of_disjoint (M₁ M₂ : σ →₀ ℕ) (h : ∀ x, M₁ x = 0 ∨ M₂ x = 0)
    (F : MvPolynomial σ K) : ddiv M₁ (ddiv M₂ F) = ddiv (M₁ + M₂) F := by
  refine MvPolynomial.induction_on' F (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · have hb : (bin M₂ α : K) * bin M₁ (α - M₂) = bin (M₁ + M₂) α := by
      unfold bin
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => ?_
      rcases h x with h1 | h2
      · simp [h1]
      · simp [h2]
    simp only [ddiv_monomial']
    rw [tsub_tsub, add_comm M₂ M₁, mul_assoc, hb]
  · simp only [ddiv_add, h₁, h₂]

theorem ddiv_zero' (F : MvPolynomial σ K) : ddiv 0 F = F := by
  refine MvPolynomial.induction_on' F (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [ddiv_monomial']
    simp [bin]
  · rw [ddiv_add, h₁, h₂]

theorem expand_monomial' {τ : Type} (P : ℕ) (d : τ →₀ ℕ) (c : K) :
    expand P (monomial d c) = monomial (P • d) c := by
  rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_eq,
    Finsupp.prod_of_support_subset _ Finsupp.support_smul (fun n e => (X n : MvPolynomial τ K) ^ e)
      (fun i _ => pow_zero _)]

end Gen

section Letter

variable {L : Type} [DecidableEq L] {r : ℕ}

theorem onLetter_apply (i : L) (β : Fin r →₀ ℕ) (j : L) (a : Fin r) :
    onLetter i β (j, a) = if j = i then β a else 0 := by
  unfold onLetter
  by_cases h : j = i
  · subst h
    rw [ite_eq_left rfl]
    exact Finsupp.mapDomain_apply_of_injective (fun x y hxy => by simpa using hxy) β a
  · rw [ite_eq_right h]
    have hne : (j, a) ∉ Set.range (fun b : Fin r => (i, b)) := by
      rintro ⟨b, hb⟩
      exact h (congrArg Prod.fst hb).symm
    first
      | exact Finsupp.mapDomain_of_notMem_range _ _ hne

def letE (α : L × Fin r →₀ ℕ) (i : L) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => α (i, a)

@[simp] theorem letE_apply (α : L × Fin r →₀ ℕ) (i : L) (a : Fin r) : letE α i a = α (i, a) := rfl

def offE (i : L) (α : L × Fin r →₀ ℕ) : L × Fin r →₀ ℕ := α.filter fun x => x.1 ≠ i

theorem offE_apply (i : L) (α : L × Fin r →₀ ℕ) (j : L) (a : Fin r) :
    offE i α (j, a) = if j = i then 0 else α (j, a) := by
  unfold offE
  rw [Finsupp.filter_apply]
  by_cases h : j = i <;> simp [h]

theorem absE_eq_sum (β : Fin r →₀ ℕ) : absE β = ∑ a, β a := by
  unfold absE
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

theorem absE_letE (α : L × Fin r →₀ ℕ) (i : L) : absE (letE α i) = ldeg α i := by
  rw [absE_eq_sum]
  unfold ldeg
  simp only [letE_apply]

end Letter

section Der

variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)

def divE {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => η a / P

@[simp] theorem divE_apply {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) (a : Fin r) : divE P η a = η a / P := rfl

theorem der' (hDER : DER K v p) (hD : DVRHyp v p) (r g : ℕ) (M : Fin r →₀ ℕ) (c : ℕ) (hc : 1 ≤ c) :
    ∃ (I : Type) (_ : Fintype I) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)),
      (∀ s, 0 ≤ v (cf s)) ∧ (∀ s, (absE (κ s) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % p ^ g) then
          monomial (ρ' s + p ^ g • (δ s + (divE (p ^ g) η - κ s))) (cf s * bin (κ s) (divE (p ^ g) η))
          else 0) := by
  have hP : 0 < p ^ g := pow_pos hD.prime.pos g
  have H : ∀ ρf : Fin r → Fin (p ^ g), ∃ (n : ℕ) (cf : Fin n → K) (ρ' δ κ : Fin n → (Fin r →₀ ℕ)),
      (∀ t, 0 ≤ v (cf t)) ∧ (∀ t, (absE (κ t) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ (β γ : Fin r →₀ ℕ), ((c : ℕ) : WithTop ℚ) ≤
        v ((ddiv M (monomial ((Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • β) (1 : K)) -
          ∑ t, monomial (ρ' t) (cf t) *
            expand (p ^ g) (monomial (δ t) (1 : K) * ddiv (κ t) (monomial β (1 : K)))).coeff γ) :=
    fun ρf => hDER hD r g _ (fun a => by simp) M c hc
  choose n cf ρ' δ κ hcf hκ happ using H
  refine ⟨Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf), inferInstance, fun s a => (s.1 a : ℕ),
    fun s => cf s.1 s.2, fun s => ρ' s.1 s.2, fun s => δ s.1 s.2, fun s => κ s.1 s.2,
    fun s => hcf s.1 s.2, fun s => hκ s.1 s.2, fun η => ?_⟩
  obtain ⟨ρf, hρf⟩ : ∃ ρf : Fin r → Fin (p ^ g), ∀ a, (ρf a : ℕ) = η a % p ^ g :=
    ⟨fun a => ⟨η a % p ^ g, Nat.mod_lt _ hP⟩, fun a => rfl⟩
  have hη : η = (Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • divE (p ^ g) η := by
    ext a
    have hm := Nat.mod_add_div (η a) (p ^ g)
    simp [divE_apply, hρf]
    all_goals first | exact hm.symm
  have hterm : ∀ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
      ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) =
      monomial (ρ' ρf t + p ^ g • (δ ρf t + (divE (p ^ g) η - κ ρf t)))
        (cf ρf t * bin (κ ρf t) (divE (p ^ g) η)) := by
    intro t
    rw [ddiv_monomial', MvPolynomial.monomial_mul_monomial, expand_monomial', MvPolynomial.monomial_mul_monomial, one_mul, one_mul]
  have hsum : (∑ s : (Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf)),
      if (fun a => (s.1 a : ℕ)) = (fun a => η a % p ^ g) then
        monomial (ρ' s.1 s.2 + p ^ g • (δ s.1 s.2 + (divE (p ^ g) η - κ s.1 s.2)))
          (cf s.1 s.2 * bin (κ s.1 s.2) (divE (p ^ g) η)) else 0) =
      ∑ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
        ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single ρf]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [hterm t]
      exact if_pos (funext hρf)
    · intro b _ hb
      refine Finset.sum_eq_zero fun t _ => if_neg ?_
      intro h
      apply hb
      funext a
      apply Fin.ext
      have h2 : ((b a : ℕ)) = η a % p ^ g := congrFun h a
      rw [h2, hρf a]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hpoly : ddiv M (monomial η (1 : K)) - (∑ s : (Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf)),
      if (fun a => (s.1 a : ℕ)) = (fun a => η a % p ^ g) then
        monomial (ρ' s.1 s.2 + p ^ g • (δ s.1 s.2 + (divE (p ^ g) η - κ s.1 s.2)))
          (cf s.1 s.2 * bin (κ s.1 s.2) (divE (p ^ g) η)) else 0) =
      ddiv M (monomial ((Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • divE (p ^ g) η) (1 : K)) -
        ∑ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
          ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) := by
    rw [hsum, ← hη]
  intro γ
  have key := happ ρf (divE (p ^ g) η) γ
  rw [← hpoly] at key
  exact (vge_natCast_bound v c _).2 key

end Der

section App

variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}

theorem bin_onLetter (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    (bin (onLetter i M) α : K) = bin M (letE α i) := by
  unfold bin
  rw [Fintype.prod_prod_type, Finset.prod_eq_single i]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [onLetter_apply, if_pos rfl, letE_apply]
  · intro j _ hj
    refine Finset.prod_eq_one fun a _ => ?_
    rw [onLetter_apply, if_neg hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sub_onLetter (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    α - onLetter i M = offE i α + onLetter i (letE α i - M) := by
  ext ⟨j, a⟩
  simp only [Finsupp.tsub_apply, Finsupp.add_apply, offE_apply, onLetter_apply, letE_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem cge_rename (v : AddValuation K (WithTop ℚ)) {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)
    {a : ℝ} {Q : MvPolynomial σ K} (hQ : cge v a Q) : cge v a (rename f Q) := by
  intro β
  by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain f hf]
    exact hQ u
  · rw [coeff_rename_eq_zero f Q β (fun u hu => absurd ⟨u, hu⟩ h)]
    exact vge_zero v a

def putL (i : L) (α : L × Fin r →₀ ℕ) : MvPolynomial (Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K :=
  (LinearMap.mulLeft K (monomial (offE i α) (1 : K))).comp (rename fun a : Fin r => (i, a)).toLinearMap

private theorem putL_eq_monomial_mul_rename (i : L) (α : L × Fin r →₀ ℕ) (Q : MvPolynomial (Fin r) K) :
    putL i α Q = monomial (offE i α) (1 : K) * rename (fun a : Fin r => (i, a)) Q := by
  simp only [putL, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]

theorem putL_monomial (i : L) (α : L × Fin r →₀ ℕ) (η : Fin r →₀ ℕ) (c : K) :
    putL i α (monomial η c) = monomial (offE i α + onLetter i η) c := by
  rw [putL_eq_monomial_mul_rename, rename_monomial, monomial_mul, one_mul, onLetter]

theorem cge_putL (v : AddValuation K (WithTop ℚ)) (i : L) (α : L × Fin r →₀ ℕ) {a : ℝ}
    {Q : MvPolynomial (Fin r) K} (hQ : cge v a Q) : cge v a (putL i α Q) := by
  rw [putL_eq_monomial_mul_rename]
  have h := cge_mul v (cge_monomial v (offE i α) (vge_one v))
    (cge_rename v (fun a : Fin r => (i, a)) (fun x y hxy => by simpa using hxy) hQ)
  rwa [zero_add] at h

theorem ddiv_onLetter_monomial (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    ddiv (onLetter i M) (monomial α (1 : K)) = putL i α (ddiv M (monomial (letE α i) 1)) := by
  rw [ddiv_monomial', ddiv_monomial', putL_monomial, sub_onLetter, bin_onLetter]

variable {I : Type} [Fintype I]

def appMon (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) : MvPolynomial (L × Fin r) K :=
  ∑ s, if cls s = (fun a => α (i, a) % P) then
    monomial (offE i α + onLetter i (ρ' s + P • (δ s + (divE P (letE α i) - κ s))))
      (cf s * bin (κ s) (divE P (letE α i))) else 0

theorem appMon_eq (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) :
    appMon i P cls cf ρ' δ κ α = putL i α (∑ s, if cls s = (fun a => letE α i a % P) then
      monomial (ρ' s + P • (δ s + (divE P (letE α i) - κ s))) (cf s * bin (κ s) (divE P (letE α i)))
      else 0) := by

  rw [map_sum, appMon]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : cls s = (fun a => α (i, a) % P)
  · rw [if_pos h, if_pos (show cls s = fun a => letE α i a % P from h), putL_monomial]
  · rw [if_neg h, if_neg (show ¬ cls s = fun a => letE α i a % P from h), map_zero]

theorem cge_appMon (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) (α : L × Fin r →₀ ℕ) :
    cge v 0 (appMon i P cls cf ρ' δ κ α) := by
  unfold appMon
  apply cge_sum v
  intro s _
  by_cases h : cls s = (fun a => α (i, a) % P)
  · rw [if_pos h]
    refine cge_monomial v _ ?_
    have h2 := vge_mul v ((vge_zero_iff v (cf s)).2 (hcf s))
      (vge_bin v (κ s) (divE P (letE α i)))
    rwa [add_zero] at h2
  · rw [if_neg h]
    exact cge_zero v 0

end App

section AppL

variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]

theorem ddiv_as_sum {σ : Type} (M : σ →₀ ℕ) (G : MvPolynomial σ K) :
    ddiv M G = ∑ α ∈ G.support, G.coeff α • ddiv M (monomial α (1 : K)) := by
  conv_lhs => rw [G.as_sum]
  rw [ddiv_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← ddiv_smul]
  simp only [smul_monomial, smul_eq_mul, mul_one]

def appL (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) :
    MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K :=
  lsup (appMon i P cls cf ρ' δ κ)

theorem cge_appL (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) {a : ℝ} {G : MvPolynomial (L × Fin r) K}
    (hG : cge v a G) : cge v a (appL i P cls cf ρ' δ κ G) := by
  rw [appL, lsup_apply]
  apply cge_sum v
  intro α _
  have h := cge_smul v (hG α) (cge_appMon v i P cls cf ρ' δ κ hcf α)
  rwa [add_zero] at h

theorem cge_ddiv_sub_appL (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (M : Fin r →₀ ℕ)
    (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) (c : ℝ)
    (hder : ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % P) then
          monomial (ρ' s + P • (δ s + (divE P η - κ s))) (cf s * bin (κ s) (divE P η)) else 0))
    {a : ℝ} {G : MvPolynomial (L × Fin r) K} (hG : cge v a G) :
    cge v (a + c) (ddiv (onLetter i M) G - appL i P cls cf ρ' δ κ G) := by
  rw [ddiv_as_sum, appL, lsup_apply, ← Finset.sum_sub_distrib]
  apply cge_sum v
  intro α _
  rw [← smul_sub]
  refine cge_smul v (hG α) ?_
  rw [ddiv_onLetter_monomial, appMon_eq, ← map_sub]
  exact cge_putL v i α (hder (letE α i))

end AppL

namespace TwistData

variable (D : TwistData K) (p : ℕ)

theorem liftE_mb (α : D.EA) (b : D.Lb) (a : Fin D.r) : D.liftE p α (D.mb b, a) = α (Sum.inl b, a) := by
  rfl

theorem liftE_mw (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    D.liftE p α (D.mw t, a) = α (Sum.inr t, a) / D.P p t := by
  rfl

def emb (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (fun t => ρ t x.2 + D.P p t * ζ (D.mw t, x.2)) x.1

theorem emb_inl (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  rfl

theorem emb_inr (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inr t, a) = ρ t a + D.P p t * ζ (D.mw t, a) := by
  rfl

theorem emb_liftE (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (h : D.InClass p ρ α) :
    D.emb p ρ (D.liftE p α) = α := by
  ext ⟨x, a⟩
  rcases x with b | t
  · rw [emb_inl, liftE_mb]
  · rw [emb_inr, liftE_mw, ← h t a, Nat.mod_add_div]

theorem digitPart_dg (ρ : D.Tau → Fin D.r → ℕ) (f : D.EA → K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (dg f G) = dg (fun ζ => f (D.emb p ρ ζ)) (D.digitPart p ρ G) := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [Formalism.MainNotions.PlaneGram.dg_monomial, digitPart_monomial, digitPart_monomial]
    by_cases h : D.InClass p ρ α
    · rw [if_pos h, if_pos h, Formalism.MainNotions.PlaneGram.dg_monomial, D.emb_liftE p ρ α h]
    · rw [if_neg h, if_neg h, map_zero]
  · rw [map_add (f := _), digitPart_add, digitPart_add, map_add (f := _), h₁, h₂]

theorem cge_digitPart (v : AddValuation K (WithTop ℚ)) (ρ : D.Tau → Fin D.r → ℕ) {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (hG : cge v a G) : cge v a (D.digitPart p ρ G) := by
  unfold digitPart
  apply Formalism.MainNotions.PlaneGram.cge_sum v
  intro α _
  by_cases h : D.InClass p ρ α
  · rw [if_pos h]
    exact Formalism.MainNotions.PlaneGram.cge_monomial v _ (hG α)
  · rw [if_neg h]
    exact Formalism.MainNotions.PlaneGram.cge_zero v a

variable (t : D.Tau)

theorem inClass_new (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (ρ1 x : Fin D.r →₀ ℕ) :
    D.InClass p ρ'' (offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x)) ↔
      (∀ a, ρ1 a % D.P p t = ρ'' t a) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by
  have hval : ∀ t' a, ((Formalism.MainNotions.PlaneGram.offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x) : D.EA)) (Sum.inr t', a) =
      if t' = t then ρ1 a + D.P p t * x a else α (Sum.inr t', a) := by
    intro t' a
    rw [Finsupp.add_apply, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply]
    by_cases h : t' = t
    · subst h
      simp
    · have hne : (Sum.inr t' : D.OL) ≠ Sum.inr t := fun e => h (Sum.inr_injective e)
      simp [h, hne]
  constructor
  · intro h
    refine ⟨fun a => ?_, fun t' ht' a => ?_⟩
    · have h1 := h t a
      rw [hval, if_pos rfl, Nat.add_mul_mod_self_left] at h1
      exact h1
    · have h1 := h t' a
      rw [hval, if_neg ht'] at h1
      exact h1
  · rintro ⟨h1, h2⟩ t' a
    rw [hval]
    by_cases h : t' = t
    · subst h
      rw [if_pos rfl, Nat.add_mul_mod_self_left]
      exact h1 a
    · rw [if_neg h]
      exact h2 t' h a

theorem inClass_update (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (cl : Fin D.r → ℕ) :
    D.InClass p (Function.update ρ'' t cl) α ↔
      (cl = fun a => α (Sum.inr t, a) % D.P p t) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by
  constructor
  · intro h
    refine ⟨funext fun a => ?_, fun t' ht' a => ?_⟩
    · have h1 := h t a
      rw [Function.update_apply, if_pos rfl] at h1
      exact h1.symm
    · have h1 := h t' a
      rw [Function.update_apply, if_neg ht'] at h1
      exact h1
  · rintro ⟨h1, h2⟩ t' a
    rw [Function.update_apply]
    by_cases h : t' = t
    · subst h
      rw [if_pos rfl, h1]
    · rw [if_neg h]
      exact h2 t' h a

private theorem liftE_apply_eq_sum_elim (α : D.EA) (x : D.ML × Fin D.r) :
    D.liftE p α x = Sum.elim (fun b => α (Sum.inl b, x.2))
      (Sum.elim (fun _ => 0) (Sum.elim (fun s => α (Sum.inr s, x.2) / D.P p s) (fun _ => 0))) x.1 := by
  rfl

theorem liftE_new (hP : 0 < D.P p t) (α : D.EA) (ρ1 δ1 κ1 : Fin D.r →₀ ℕ) :
    D.liftE p (offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ1 + D.P p t • (δ1 + (divE (D.P p t) (letE α (Sum.inr t)) - κ1)))) =
      onLetter (D.mw t) (divE (D.P p t) ρ1 + δ1) + (D.liftE p α - onLetter (D.mw t) κ1) := by
  ext ⟨y, a⟩
  rcases y with b | t' | t' | t'
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
  · by_cases h : t' = t
    · subst h
      simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
      first
        | (rw [← mul_add, Nat.add_mul_div_left _ _ hP]; omega)
    · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw, h]
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]

theorem letE_liftE_mw (α : D.EA) :
    letE (D.liftE p α) (D.mw t) = divE (D.P p t) (letE α (Sum.inr t)) := by
  ext a
  simp only [Formalism.MainNotions.PlaneGram.letE_apply, Formalism.MainNotions.PlaneGram.divE_apply, liftE_mw]

theorem digitPart_zero (ρ : D.Tau → Fin D.r → ℕ) :
    D.digitPart p ρ (0 : MvPolynomial (D.OL × Fin D.r) K) = 0 := by
  rw [digitPart_eq, map_zero]

def opS (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  c1 • ((LinearMap.mulLeft K (monomial (onLetter (D.mw t) μ) (1 : K))).comp
    (ddivL (onLetter (D.mw t) κ1)))

theorem opS_apply (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) (Q : MvPolynomial (D.ML × Fin D.r) K) :
    D.opS t μ κ1 c1 Q = c1 • (monomial (onLetter (D.mw t) μ) (1 : K) * ddiv (onLetter (D.mw t) κ1) Q) := by
  simp only [opS, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Formalism.MainNotions.PlaneGram.ddiv_eq]

private theorem digitPart_approx_term_lemma_4 (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cl : Fin D.r → ℕ) (e : K) (ρ0 δ0 κ0 : Fin D.r →₀ ℕ) (α : D.EA) (c : K) :
    c • D.digitPart p ρ'' (if cl = (fun a => α (Sum.inr t, a) % D.P p t) then
      monomial (Formalism.MainNotions.PlaneGram.offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ0 + D.P p t • (δ0 + (Formalism.MainNotions.PlaneGram.divE (D.P p t) (Formalism.MainNotions.PlaneGram.letE α (Sum.inr t)) - κ0))))
        (e * Formalism.MainNotions.PlaneGram.bin κ0 (Formalism.MainNotions.PlaneGram.divE (D.P p t) (Formalism.MainNotions.PlaneGram.letE α (Sum.inr t)))) else 0) =
      if (fun a => ρ0 a % D.P p t) = ρ'' t then
        D.opS t (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) κ0 e (D.digitPart p (Function.update ρ'' t cl) (monomial α c))
      else 0 := by
  have hsh : ∀ L : D.EM, D.opS t (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) κ0 e (monomial L c) =
      monomial (onLetter (D.mw t) (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) + (L - onLetter (D.mw t) κ0))
        (c * (e * Formalism.MainNotions.PlaneGram.bin κ0 (Formalism.MainNotions.PlaneGram.letE L (D.mw t)))) := by
    intro L
    rw [opS_apply, Formalism.MainNotions.PlaneGram.ddiv_monomial', Formalism.MainNotions.PlaneGram.bin_onLetter, monomial_mul, smul_monomial, smul_eq_mul,
      one_mul, mul_left_comm]
  by_cases h2 : (fun a => ρ0 a % D.P p t) = ρ'' t
  · rw [if_pos h2]
    by_cases h1 : cl = (fun a => α (Sum.inr t, a) % D.P p t)
    · rw [if_pos h1, digitPart_monomial, digitPart_monomial]
      by_cases hQ : ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a
      · rw [if_pos ((D.inClass_new p t ρ'' α ρ0 _).2 ⟨fun a => congrFun h2 a, hQ⟩),
          if_pos ((D.inClass_update p t ρ'' α cl).2 ⟨h1, hQ⟩), smul_monomial, smul_eq_mul, hsh,
          D.liftE_new p t hP, letE_liftE_mw]
      · rw [if_neg (fun h => hQ ((D.inClass_new p t ρ'' α ρ0 _).1 h).2),
          if_neg (fun h => hQ ((D.inClass_update p t ρ'' α cl).1 h).2), smul_zero, map_zero]
    · rw [if_neg h1, digitPart_zero, smul_zero, digitPart_monomial,
        if_neg (fun h => h1 ((D.inClass_update p t ρ'' α cl).1 h).1), map_zero]
  · rw [if_neg h2]
    by_cases h1 : cl = (fun a => α (Sum.inr t, a) % D.P p t)
    · rw [if_pos h1, digitPart_monomial,
        if_neg (fun h => h2 (funext ((D.inClass_new p t ρ'' α ρ0 _).1 h).1)), smul_zero]
    · rw [if_neg h1, digitPart_zero, smul_zero]

theorem digitPart_appL {I : Type} [Fintype I] (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cls : I → Fin D.r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin D.r →₀ ℕ))
    (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ'' (appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G) =
      ∑ s, if (fun a => ρ' s a % D.P p t) = ρ'' t then
        D.opS t (divE (D.P p t) (ρ' s) + δ s) (κ s) (cf s)
          (D.digitPart p (Function.update ρ'' t (cls s)) G) else 0 := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [Formalism.MainNotions.PlaneGram.appL, Formalism.MainNotions.PlaneGram.lsup_monomial, digitPart_smul, Formalism.MainNotions.PlaneGram.appMon, digitPart_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact digitPart_approx_term_lemma_4 D p t hP ρ'' (cls s) (cf s) (ρ' s) (δ s) (κ s) α c
  · rw [map_add (f := _), digitPart_add, h₁, h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (fun a => ρ' s a % D.P p t) = ρ'' t
    · rw [if_pos h, if_pos h, if_pos h, digitPart_add, map_add (f := _)]
    · rw [if_neg h, if_neg h, if_neg h, add_zero]

end TwistData

end Formalism.MainNotions.PlaneGram
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DdivOnLetterMonomial =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DdivOnLetterMonomial\npublic import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen\npublic import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut\nimport Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

theorem cge_ddiv (v : AddValuation K (WithTop ℚ)) {σ : Type} (M : σ →₀ ℕ) {a : ℝ}
    {F : MvPolynomial σ K} (hF : cge v a F) : cge v a (ddiv M F) := by
  intro β
  rw [coeff_ddiv]
  have h1 : vge v 0 ((β + M).prod fun x k => (k.choose (M x) : K)) := by
    unfold Finsupp.prod
    rw [← Nat.cast_prod]
    exact vge_natCast v _
  have := vge_mul v (hF (β + M)) h1
  rwa [add_zero] at this

namespace TwistData

variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)

def ChOK (θ : (j : Fin D.J) → Fin (D.nch j) → ℝ) (a : ℝ) (G : MvPolynomial (D.OL × Fin D.r) K) : Prop :=
  ∃ G0 E : MvPolynomial (D.OL × Fin D.r) K, G = G0 + E ∧ cge v a G0 ∧ cge v (a + D.c) E ∧
    ∀ (ρ : D.Tau → Fin D.r → ℕ) (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (θ j i) (D.digitPart p ρ G0)

variable {D v p}

theorem ChOK.mono {θ θ' : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (hθ : ∀ j i, θ' j i ≤ θ j i) :
    D.ChOK v p θ' a G := by
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  exact ⟨G0, E, h1, h2, h3, fun ρ j i => vala_mono (hθ j i) (h4 ρ j i)⟩

variable (D p)

def CostA (n : ℕ) (f : D.EA → K) : Prop :=
  ∀ ρ : D.Tau → Fin D.r → ℕ, CostV D.msg Set.univ n (fun ζ => f (D.emb p ρ ζ))

theorem costM_ok : CostOK (CostV (K := K) (r := D.r) D.msg Set.univ) :=
  costV_ok D.msg Set.univ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)

theorem costA_ok : CostOK (D.CostA p) := by
  constructor
  · exact fun _ => D.costM_ok.one
  · exact fun m n _ _ hf hg ρ => D.costM_ok.mul m n _ _ (hf ρ) (hg ρ)
  · exact fun n _ _ hf hg ρ => D.costM_ok.add n _ _ (hf ρ) (hg ρ)
  · exact fun n a _ hf ρ => D.costM_ok.smul n a _ (hf ρ)
  · exact fun m n _ hmn hf ρ => D.costM_ok.mono m n _ hmn (hf ρ)

theorem costM_choose [NeZero D.r] (hV2 : V2 K) (x : D.ML × Fin D.r) (k : ℕ) :
    CostV (K := K) D.msg Set.univ k (fun ζ => ((ζ x).choose k : K)) :=
  fun _ _ _ _ h => vala_dg_choose hV2 x k h

theorem costA_choose [NeZero D.r] (hV2 : V2 K) (x : D.OL × Fin D.r) (k : ℕ) :
    D.CostA p k (fun α => ((α x).choose k : K)) := by
  intro ρ
  obtain ⟨i, a⟩ := x
  rcases i with b | t
  · simp only [emb_inl]
    exact D.costM_choose hV2 (D.mb b, a) k
  · simp only [emb_inr]
    exact cost_choose_affine D.costM_ok (fun ζ => ζ (D.mw t, a))
      (fun k => D.costM_choose hV2 (D.mw t, a) k) (ρ t a) (D.P p t) k

variable {D p}

theorem ChOK.dg [NeZero D.r] (hV2 : V2 K) {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (f : D.EA → K)
    (hf0 : ∀ α, 0 ≤ v (f α)) (T : Finset (D.OL × Fin D.r → ℕ)) (lam : (D.OL × Fin D.r → ℕ) → K)
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c)
    (hf : ∀ α : D.EA, ((D.c : ℕ) : WithTop ℚ) ≤ v (f α - binomComb T lam (fun x => α x))) :
    D.ChOK v p (fun j i => θ j i - 6 * D.c) a (Formalism.MainNotions.PlaneGram.dg f G) := by
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  have hC := D.costA_ok (K := K) p
  obtain ⟨g, hg0, hg1, hg2⟩ :=
    approx_of_trunc (v := v) hC (D.costA_choose p hV2) T lam hlam f hf
  refine ⟨Formalism.MainNotions.PlaneGram.dg g G0, Formalism.MainNotions.PlaneGram.dg (fun α => f α - g α) G0 + Formalism.MainNotions.PlaneGram.dg f E,
    ?_, ?_, ?_, ?_⟩
  · rw [h1, map_add (f := _), dg_sub_fun]; abel
  · have := cge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) h2
    rwa [zero_add] at this
  · refine cge_add v ?_ ?_
    · have := cge_dg v (fun α => (vge_natCast_bound v D.c _).mpr (hg1 α)) h2
      rwa [add_comm] at this
    · have := cge_dg v (fun α => (vge_zero_iff v _).mpr (hf0 α)) h3
      rwa [zero_add] at this
  · intro ρ j i
    rw [digitPart_dg]
    have := hg2 ρ (D.chainSet j i) (Set.mem_univ _) (θ j i) _ (h4 ρ j i)
    have e : θ j i - ((6 * D.c : ℕ) : ℝ) = θ j i - 6 * D.c := by push_cast; ring
    rwa [e] at this

theorem vala_opS [NeZero D.r] (hV2 : V2 K) (t : D.Tau) (S : Finset D.ML) (μ κ1 : Fin D.r →₀ ℕ) (c1 : K)
    {θ : ℝ} {Q : MvPolynomial (D.ML × Fin D.r) K} (hQ : vala D.msg S θ Q) :
    vala D.msg S (θ - absE κ1) (D.opS t μ κ1 c1 Q) := by
  classical
  rw [opS_apply]
  refine vala_smul c1 (vala_mul_left_nonneg ?_ (vala_ddiv_letter hV2 (D.mw t) κ1 hQ))
  refine valS_nonneg_of_vec D.msg S _ fun α hα i a hne => ?_
  have := support_monomial_subset hα
  rw [Finset.mem_singleton] at this
  rw [this, onLetter_apply] at hne
  by_cases hi : i = D.mw t
  · rw [hi]; rfl
  · rw [if_neg hi] at hne; exact absurd rfl hne

theorem vala_opS_out (t : D.Tau) (S : Finset D.ML) (hS : D.mw t ∉ S) (μ κ1 : Fin D.r →₀ ℕ) (c1 : K)
    {θ : ℝ} {Q : MvPolynomial (D.ML × Fin D.r) K} (hQ : vala D.msg S θ Q) :
    vala D.msg S θ (D.opS t μ κ1 c1 Q) := by
  classical
  have hform : ∀ α : D.EM, D.opS t μ κ1 c1 (monomial α 1) =
      monomial (onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1))
        (c1 * bin κ1 (letE α (D.mw t))) := by
    intro α
    rw [opS_apply, ddiv_monomial', monomial_mul, smul_monomial, bin_onLetter]
    simp
  refine vala_outside_linear (D.opS t μ κ1 c1) (fun i => i = D.mw t)
    (fun i hi h => hS (h ▸ hi)) ?_ ?_ hQ
  · intro α
    rw [hform, hform, monomial_mul, one_mul]
    have e1 : onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1) =
        eIn (fun i => i = D.mw t) α + (onLetter (D.mw t) μ +
          (eOut (fun i => i = D.mw t) α - onLetter (D.mw t) κ1)) := by
      ext ⟨i, a⟩
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, onLetter_apply, eIn_apply, eOut_apply]
      by_cases hi : i = D.mw t
      · simp [hi]
      · simp [hi]
    have e2 : letE (eOut (fun i => i = D.mw t) α) (D.mw t) = letE α (D.mw t) := by
      ext a
      simp [eOut_apply]
    rw [e1, e2]
  · intro α
    rw [hform]
    refine valS_nonneg_of_vec D.msg S _ fun β hβ i a hne => ?_
    have := support_monomial_subset hβ
    rw [Finset.mem_singleton] at this
    by_cases hi : i = D.mw t
    · rw [hi]; rfl
    · exfalso
      apply hne
      rw [this]
      simp [onLetter_apply, eOut_apply, hi]

theorem mw_not_mem_chainSet (D : TwistData K) (t : D.Tau) (j : Fin D.J) (i : Fin (D.nch j))
    (h : t.1 ≠ D.aux₃ j) : D.mw t ∉ D.chainSet j i := by
  classical
  intro hm
  unfold chainSet wSet at hm
  rcases Finset.mem_union.mp hm with h1 | h1
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h1
    simp [mb, mw] at hb
  · obtain ⟨m, -, hm'⟩ := Finset.mem_image.mp h1
    apply h
    have : (D.aux₃ j, m) = t := by simpa [mw] using hm'
    rw [← this]

theorem ChOK.ddiv [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (t : D.Tau) (M : Fin D.r →₀ ℕ) :
    D.ChOK v p (fun j i => θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G) := by
  classical
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  obtain ⟨I, hI, cls, cf, ρ', δ, κ, hcf, hκ, hder⟩ := der' v p hDER hD D.r (D.g t) M D.c hc
  have hP : 0 < D.P p t := pow_pos hD.prime.pos _
  refine ⟨appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0,
    (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G0 - appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0) +
      Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) E, ?_, ?_, ?_, ?_⟩
  · rw [h1, ddiv_add]; abel
  · exact cge_appL v _ _ cls cf ρ' δ κ hcf h2
  · exact cge_add v (cge_ddiv_sub_appL v _ (D.P p t) M cls cf ρ' δ κ D.c hder h2) (cge_ddiv v _ h3)
  · intro ρ'' j i
    rw [D.digitPart_appL p t hP]
    refine vala_sum _ _ fun s _ => ?_
    show vala D.msg (D.chainSet j i)
      (θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) _
    by_cases hB : (fun a => ρ' s a % D.P p t) = ρ'' t
    · rw [if_pos hB]
      by_cases hj : t.1 = D.aux₃ j
      · rw [if_pos hj]
        refine vala_mono ?_ (vala_opS hV2 t _ _ (κ s) (cf s) (h4 (Function.update ρ'' t (cls s)) j i))
        have := hκ s
        have e : ((D.P p t : ℕ) : ℝ) = (p : ℝ) ^ D.g t := by unfold P; push_cast; rfl
        rw [e]
        linarith
      · rw [if_neg hj, sub_zero]
        exact vala_opS_out t _ (D.mw_not_mem_chainSet t j i hj) _ (κ s) (cf s)
          (h4 (Function.update ρ'' t (cls s)) j i)
    · rw [if_neg hB]
      exact vala_zero _

theorem sum_onLetter_apply_inr (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (t : D.Tau) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inr t, a) =
      if t ∈ s then M (Sum.inr t, a) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [onLetter_apply, letE_apply, Sum.inr.injEq]
  rw [Finset.sum_ite_eq]

theorem sum_onLetter_apply_inl (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (b : D.Lb) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inl b, a) = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun t' _ => ?_
  rw [onLetter_apply, if_neg (by simp)]

theorem ChOK.ddiv_finset [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (M : D.EA) (s : Finset D.Tau) :
    D.ChOK v p (fun j i => θ j i - ∑ t ∈ s,
        (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv (∑ t ∈ s, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) G) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, sub_zero]
    rw [ddiv_zero']
    exact h
  | insert t s ht ih =>
    have h1 := ih.ddiv hV2 hDER hD hc t (letE M (Sum.inr t))
    rw [ddiv_ddiv_of_disjoint] at h1
    · rw [Finset.sum_insert ht]
      refine h1.mono fun j i => ?_
      rw [Finset.sum_insert ht, absE_letE]
      linarith
    · rintro ⟨i, a⟩
      rcases i with b | t'
      · right; exact D.sum_onLetter_apply_inl M s b a
      · by_cases htt : t' = t
        · right
          rw [D.sum_onLetter_apply_inr M s t' a, if_neg (htt ▸ ht)]
        · left
          rw [onLetter_apply, if_neg (fun hh => htt (Sum.inr.inj hh))]

theorem ChOK.ddiv_all [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (M : D.EA)
    (hM : ∀ b a, M (Sum.inl b, a) = 0) :
    D.ChOK v p (fun j i => θ j i - ∑ t,
        (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv M G) := by
  have h1 := h.ddiv_finset hV2 hDER hD hc M Finset.univ
  have e : (∑ t, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) = M := by
    ext ⟨i, a⟩
    rcases i with b | t
    · rw [D.sum_onLetter_apply_inl M _ b a, hM]
    · rw [D.sum_onLetter_apply_inr M _ t a, if_pos (Finset.mem_univ _)]
  rwa [e] at h1

theorem nxt_prv (D : TwistData K) (j : Fin D.J) : D.nxt (D.aux₃ j) = j := by
  apply Fin.ext
  have hJ : 0 < D.J := j.pos
  have hj := j.isLt
  simp only [nxt, aux₃]
  rw [Nat.mod_add_mod, show j.val + D.J - 1 + 1 = j.val + D.J by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hj]

theorem hypH' (D : TwistData K) (p : ℕ) (kH : ℝ) (hH : D.HypH p kH) (j : Fin D.J) (m : Fin D.r)
    (i : Fin (D.nch j)) :
    (D.r : ℝ) * D.dLL (D.aux₃ j) / (D.P p (D.aux₃ j, m) : ℝ) + kH * D.r * D.c ≤ D.sl j i := by
  have h := hH (D.aux₃ j) m
  rw [D.nxt_prv j] at h
  exact h i

theorem sum_ldeg_div_add_le_sl (D : TwistData K) (p : ℕ) (hp : 0 < p) (hr : 0 < D.r) (hH : D.HypH p 13) (M : D.EA)
    (hMd : ∀ t : D.Tau, ldeg M (Sum.inr t) ≤ D.dLL t.1) (j : Fin D.J) (i : Fin (D.nch j)) :
    (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) +
      12 * D.c ≤ D.sl j i := by
  classical
  have hr' : (0 : ℝ) < D.r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
  have hc0 : (0 : ℝ) ≤ D.c := Nat.cast_nonneg _
  have e1 : (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) =
      ∑ m : Fin D.r, ((ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (D.aux₃ j)]
    · simp
    · intro j0 _ hj0
      simp [hj0]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  have e2 : ∀ m : Fin D.r, (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c ≤
      (D.sl j i - 13 * D.r * D.c) / D.r + D.c := by
    intro m
    have hP : (0 : ℝ) < (D.P p (D.aux₃ j, m) : ℝ) := by
      have : 0 < D.P p (D.aux₃ j, m) := pow_pos hp _
      exact_mod_cast this
    have h1 := D.hypH' p 13 hH j m i
    have h2 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) ≤ D.dLL (D.aux₃ j) := by exact_mod_cast hMd (D.aux₃ j, m)
    have h3 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤
        (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) := div_le_div_of_nonneg_right h2 hP.le
    have h4 : (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤ (D.sl j i - 13 * D.r * D.c) / D.r := by
      rw [le_div_iff₀ hr']
      rw [mul_div_assoc] at h1
      linarith
    linarith
  have e3 := Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin D.r))) => e2 m)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
    mul_div_cancel₀ _ hr'.ne'] at e3
  nlinarith

end TwistData

theorem stepE_of [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (hV2 : V2 K) (hDER : DER K v p) :
    StepE K v p := by
  intro hD D hValid hH F hF hb M hM0 hMd ρ
  obtain ⟨hr, -, hc, -, -, -, hgu, hgs⟩ := hValid
  haveI : NeZero D.r := ⟨hr.ne'⟩
  have h0 : D.ChOK v p D.th (-D.n0 v) F := by
    refine ⟨F, 0, by rw [add_zero], ?_, cge_zero v _, fun ρ j i => hF.2.1 ρ j i⟩
    have := cge_of_bge hD hF.1 hb
    rw [zero_sub] at this
    exact this
  obtain ⟨T1, lam1, hl1, hf1⟩ := hgs 1 (Or.inl rfl)
  obtain ⟨T2, lam2, hl2, hf2⟩ := hgs (-1) (Or.inr rfl)
  have h1 := h0.dg hV2 D.ga (fun α => (hgu α).ge) T1 lam1 hl1
    (fun α => by have := hf1 α; rwa [zpow_one] at this)
  have h2 := h1.ddiv_all hV2 hDER hD hc M hM0
  have h3 := h2.dg hV2 (fun α => (D.ga α)⁻¹) (fun α => (v_unit_inv v (hgu α)).ge) T2 lam2 hl2
    (fun α => by have := hf2 α; rwa [zpow_neg_one] at this)
  obtain ⟨G0, E, hG, -, hE, hval⟩ := h3
  refine ⟨D.digitPart p ρ G0, D.digitPart p ρ E, ?_, fun j i => ?_, ?_⟩
  · rw [D.gaAct_eq, hG, D.digitPart_add]
  · refine vala_mono ?_ (hval ρ j i)
    have := D.sum_ldeg_div_add_le_sl p hD.prime.pos hr hH M hMd j i
    linarith
  · have := D.cge_digitPart p v ρ hE
    rwa [neg_add_eq_sub] at this

end Formalism.MainNotions.PlaneGram
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl =====
