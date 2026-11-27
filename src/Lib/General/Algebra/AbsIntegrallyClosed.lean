module

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import Lib.Speed

/-!
# Absolutely integrally closed rings and their stability properties; Frobenius powers

* `New.Variety.frobPow`: the ring endomorphism `x ↦ x ^ p ^ f`, for a prime `p` with `p = 0` in
  the ring.
* `TauCeti.IsAbsolutelyIntegrallyClosed`: every monic polynomial of positive degree has a root (the
  ring need not be a domain).
* The property passes to subrings that are integrally closed in the ring
  (`TauCeti.IsAbsolutelyIntegrallyClosed.of_isIntegrallyClosedIn`), to quotients
  (`TauCeti.IsAbsolutelyIntegrallyClosed.of_surjective`) and to localisations
  (`TauCeti.IsAbsolutelyIntegrallyClosed.of_isLocalization`). For a field it means algebraically
  closed: algebraically closed fields have it by an instance, and
  `TauCeti.isAbsolutelyIntegrallyClosed_iff_isAlgClosed` identifies the two properties.
* `TauCeti.IsAbsolutelyIntegrallyClosed.exists_root_map_eq`,
  `TauCeti.IsAbsolutelyIntegrallyClosed.mem_range_of_isIntegralElem`: for `f : A →+* B` from an
  absolutely integrally closed ring into a domain, roots in `B` of monic polynomials over `A` lift
  to roots in `A`, so integral elements lie in the image.
-/

@[expose] public section

open Polynomial

namespace New.Variety

/-- The ring endomorphism `x ↦ x ^ p ^ f` of a commutative ring `B` in which the prime `p` is
zero. -/
@[simps! -fullyApplied]
def frobPow {p : ℕ} {B : Type*} [Fact (Nat.Prime p)] [CommRing B] (h : (p : B) = 0) (f : ℕ) :
    B →+* B :=
  -- The map is additive because the mixed terms of the binomial expansion are multiples of `p`.
  RingHom.mk' (powMonoidHom (p ^ f)) (by simp [add_pow_prime_pow_eq Fact.out, h])

end New.Variety

namespace TauCeti.IsAbsolutelyIntegrallyClosed

variable {A B : Type*} [CommRing A] [CommRing B]

/-- If `A` is absolutely integrally closed and `f : B →+* A` is a ring map, then every monic
polynomial over `B` of positive degree has a root in `A` along `f`. -/
lemma exists_eval₂_eq_zero [hA : IsAbsolutelyIntegrallyClosed A] (f : B →+* A)
    {P : B[X]} (hP : Monic P) (h_deg : 0 < P.natDegree) : ∃ x : A, P.eval₂ f x = 0 := by
  nontriviality A
  simpa [eval_map] using hA.exists_root (P.map f) (hP.map f) (by rwa [hP.natDegree_map f])

variable (A) in
/-- If `A` is absolutely integrally closed and `B` is integrally closed in the `B`-algebra `A`
(in particular `B → A` is injective), then `B` is absolutely integrally closed. -/
@[stacks 0DCP "for any ring in which `B` is integrally closed, not only a localisation"]
lemma of_isIntegrallyClosedIn [hA : IsAbsolutelyIntegrallyClosed A] [Algebra B A]
    [h_closed : IsIntegrallyClosedIn B A] : IsAbsolutelyIntegrallyClosed B := by
  refine ⟨fun P hP h_deg ↦ ?_⟩
  obtain ⟨h_inj, h_range⟩ := isIntegrallyClosedIn_iff.1 h_closed
  obtain ⟨x, hx⟩ := hA.exists_eval₂_eq_zero (algebraMap B A) hP h_deg
  -- The root `x` is integral over `B`, so it comes from `B`; and `B → A` is injective.
  obtain ⟨b, rfl⟩ : ∃ b : B, algebraMap B A b = x := h_range ⟨P, hP, hx⟩
  exact ⟨b, h_inj (by simpa using hx)⟩

/-- Let `A` be absolutely integrally closed and `f : A →+* B` a ring map. A monic polynomial over
`B` of positive degree whose coefficients lie in the image of `f` has a root in `B`. -/
lemma exists_root_of_coeffs_subset_range [hA : IsAbsolutelyIntegrallyClosed A]
    {f : A →+* B} {P : B[X]}
    (h_coeffs : (P.coeffs : Set B) ⊆ Set.range f) (hP : P.Monic) (h_deg : 0 < P.natDegree) :
    ∃ x : B, P.IsRoot x := by
  -- `P` is the image of a monic `Q` of the same degree, and `f` maps a root of `Q` to one of `P`.
  obtain ⟨Q, rfl, hQ_deg, hQ⟩ :=
    lifts_and_natDegree_eq_and_monic ((lifts_iff_coeffs_subset_range P).2 h_coeffs) hP
  obtain ⟨x, hx⟩ := hA.exists_root Q hQ (by lia)
  exact ⟨f x, hx.map f⟩

/-- In an absolutely integrally closed ring, every element has an `n`-th root for `n ≠ 0`. -/
lemma exists_pow_eq [hA : IsAbsolutelyIntegrallyClosed A] (n : ℕ) [hn : NeZero n] (a : A) :
    ∃ x : A, x ^ n = a := by
  exact exists_pow_nat_eq a hn.pos

/-- In a nonzero absolutely integrally closed ring `A`, for `n > 1` and any `c`, `b` in `A`, the
equation `x ^ n - c * x = b` has a solution `x` in `A`. -/
lemma exists_pow_sub_mul_eq [hA : IsAbsolutelyIntegrallyClosed A] [Nontrivial A] (n : ℕ)
    [hn : Fact (1 < n)] (c b : A) : ∃ x : A, x ^ n - c * x = b := by
  -- The solutions are the roots of a monic polynomial of degree `n > 1`.
  let P : A[X] := X ^ n - (C c * X + C b)
  have hP : P.IsMonicOfDegree n :=
    (isMonicOfDegree_X_pow A n).sub (natDegree_linear_le.trans_lt hn.out)
  have h_deg : 0 < P.natDegree := (zero_lt_one.trans hn.out).trans_eq hP.natDegree_eq.symm
  simpa [P, ← sub_sub, sub_eq_zero] using hA.exists_root P hP.monic h_deg

/-! ### Maps to a domain -/

/-- Let `A` be absolutely integrally closed, `f : A →+* B` a ring map to a domain, and `P` a monic
polynomial over `A`. Every root `x` in `B` of the image of `P` is `f a` for some root `a` of `P`
in `A`. -/
lemma exists_root_map_eq [hA : IsAbsolutelyIntegrallyClosed A] {f : A →+* B} [IsDomain B] {x : B}
    {P : A[X]} (hP : Monic P) (hx : P.eval₂ f x = 0) : ∃ a : A, P.IsRoot a ∧ f a = x := by
  obtain ⟨s, hs⟩ := splits_iff_exists_multiset.mp (splits hP)
  rw [hP.leadingCoeff, C_1, one_mul] at hs
  -- The product of the images of the linear factors vanishes in the domain `B`.
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ s, x = f a := by
    simpa [hs, eval₂_multiset_prod, Multiset.map_map, Function.comp_def, sub_eq_zero] using hx
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, by rw [hs]; simp [Polynomial.IsRoot], hax.symm⟩

/-- If `A` is absolutely integrally closed and `f : A →+* B` is a ring map to a domain, then every
element of `B` that is integral along `f` lies in the image of `f`. -/
lemma mem_range_of_isIntegralElem [hA : IsAbsolutelyIntegrallyClosed A] {f : A →+* B}
    [IsDomain B] {x : B} (hx : f.IsIntegralElem x) : x ∈ f.range := by
  obtain ⟨P, hP, hPx⟩ := hx
  obtain ⟨a, -, rfl⟩ := hA.exists_root_map_eq hP hPx
  exact ⟨a, rfl⟩

end TauCeti.IsAbsolutelyIntegrallyClosed
