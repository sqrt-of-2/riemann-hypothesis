module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem relDim_bot {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card]
  rfl

abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

theorem relDim_projectiveSpace {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl

def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0

theorem binomFn_sub (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring

theorem weight_projIdx (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  simp [blockWeight]

theorem finrank_gradedPiece_projectiveSpace (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap := by
    intro x y h
    simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero] using h
  unfold gradedPiece
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :=
    {d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}
  let e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)) :=
    Equiv.subtypeEquivRight fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]
      constructor
      · intro h
        rw [← weight_projIdx]
        exact congrFun h ()
      · intro h
        funext u
        rw [weight_projIdx]
        exact h
  have : Fintype s := Fintype.ofEquiv _ e.symm
  rw [LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_sigma]
  rw [add_comm, Nat.choose_symm_add]

theorem hilbFn_projectiveSpace (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [ite_eq_left (fun k => hm), ite_eq_left hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [ite_eq_right (fun h => hm (h ())), ite_eq_right hm]

theorem foldr_diffStep_binomFn (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]
    funext m
    simp only [diffStep, Pi.sub_apply, Pi.one_apply]
    exact binomFn_sub N (m ())

theorem intNum_projectiveSpace (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by
  have hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ()) := by
    funext m
    rw [zero_add, hilbFn_projectiveSpace]
  unfold intNum mixedDiff
  rw [List.ofFn_const, hh, foldr_diffStep_binomFn]
  have hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1 :=
    (Filter.eventually_ge_atTop 0).mono fun m hm => by
      have : (0 : ℤ) ≤ m () := hm ()
      simp [binomFn, this]
  have hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c := ⟨1, hev⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hev).exists
  exact h1.symm.trans h2

theorem blockIncl_injective {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
