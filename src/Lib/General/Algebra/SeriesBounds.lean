module

import TauCeti.RingTheory.PowerSeries.Exp.Padic.Subst
public import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.PowerSeries.Binomial
public import Lib.CM.FormalGroup.IntegralParameter
import Lib.General.Algebra.AbsIntegrallyClosed

/-!
# Integrality of exponentials, logarithms and roots of power series

The file first shows that, over an algebraically closed valued field, there is an integral point at
which finitely many given polynomials are at least as large as all their coefficients. It then
bounds the coefficients of power series built by exponentials, logarithms and roots over `ℂ_[p]`.
There `v` denotes the additive valuation with `v(p) = 1`, so that `‖c‖ = p ^ (-v(c))`, and `v(g)`
for a series `g` is the infimum of the valuations of its coefficients. `expSubst g` is `exp ℂ_[p]`
substituted at `g`, written `exp g`, and `logOf f` is `log ℂ_[p]`, the series of `log (1 + X)`,
substituted at `f - 1`, written `log f`. For `g(0) = 0` it proves that `exp g` is integral when
`v(g) ≥ 1 / (p - 1)`, gives a divisibility criterion for `exp g - 1`, and shows that `exp g` lies in
a ring `𝒪[[T]]` if its `m`-th power does, for `m` prime to `p`.

The imported notions used in the statements are these.

* `seriesToCp` is the inclusion of the series with integral coefficients into all series over
  `ℂ_[p]`. Its range consists of the series whose coefficients have norm at most `1`.
* `IsSeriesGenerator B T` says that `T = X + ⋯` and that `B` is the ring of all integral series in
  `T`, written `B = 𝒪[[T]]`.

## Main definitions and results

* `New.exists_val_coeff_le_val_eval`: at one integral point, finitely many polynomials are at least
  as large as all their coefficients.
* `New.norm_coeff_expSubst_le_one`: `exp g` is integral if `g(0) = 0` and `v(g) ≥ 1 / (p - 1)`,
  degree by degree.
* `New.norm_coeff_expSubst_sub_one_le`, `New.IsSeriesGenerator.mem_of_expSubst_smul_eq`: for
  `v(c) ≥ 1 / (p - 1)` and `g(0) = 0`, the number `c` divides `exp g - 1` if it divides `g`, and,
  for `c ≠ 0` and in a ring `𝒪[[T]]`, `c` divides `g` if it divides `exp g - 1`.
* `New.IsSeriesGenerator.expSubst_mem_of_pow_mem`: if `g(0) = 0` and `(exp g) ^ m ∈ 𝒪[[T]]` with `m`
  prime to `p`, then `exp g ∈ 𝒪[[T]]`.

## Relation to the literature

Known result: the Gauss norm equals the supremum norm on the unit polydisc over an algebraically
closed valued field. Source: Bosch, Güntzer and Remmert, *Non-Archimedean Analysis*.

Known result: the integrality of the `p`-adic exponential and logarithm on series of large enough
valuation, and of the binomial series with exponent in `ℤ_p`.
-/

@[expose] public section

/-!
## A general integral point

Each polynomial is a constant times a polynomial with nonzero reduction. As the residue field is
infinite, there is a point at which none of the reductions vanishes.
-/

section IntegralityPrinciple

open Finset IsLocalRing MvPolynomial TauCeti.IsAbsolutelyIntegrallyClosed

/-- Over an algebraically closed valued field there is an integral point at which each of finitely
many polynomials takes a value at least as large as all its coefficients. -/
lemma New.exists_val_coeff_le_val_eval {K σ : Type*} {n : ℕ} [Field K] [IsAlgClosed K]
    (v : Valuation K NNReal) (f : Fin n → MvPolynomial σ K) :
    ∃ y : σ → v.valuationSubring,
      ∀ (i : Fin n) (m : σ →₀ ℕ),
        v ((f i).coeff m) ≤ v (eval (algebraMap v.valuationSubring K ∘ y) (f i)) := by
  classical
  -- Write `f i = c i • g i` with `g i` over `V` of nonzero reduction. The residue field is
  -- algebraically closed, hence infinite, so at some `y` no reduction vanishes: each `g i` takes
  -- a unit value at `y`.
  set V : ValuationSubring K := v.valuationSubring
  have h_scale (q : MvPolynomial σ K) :
      ∃ (c : K) (g : MvPolynomial σ V), map (residue V) g ≠ 0 ∧ q = c • g.map (algebraMap V K) := by
    -- A coefficient `q.coeff k` of largest valuation divides the others, with quotients `w m`.
    obtain ⟨k, hk⟩ : ∃ k : σ →₀ ℕ, ∀ m ∈ q.support,
        V.valuation (q.coeff m) ≤ V.valuation (q.coeff k) :=
      Set.exists_upper_bound_image q.support (V.valuation ∘ q.coeff) (Set.toFinite _)
    have h_dvd : ∀ m ∈ q.support, ∃ w : V, (w : K) * q.coeff k = q.coeff m :=
      fun m hm ↦ (V.valuation_le_iff _ _).1 (hk m hm)
    choose! w hw using h_dvd
    let g : MvPolynomial σ V := monomial k 1 + ∑ d ∈ q.support.erase k, monomial d (w d)
    have h_coeff (d : σ →₀ ℕ) :
        g.coeff d = if k = d then 1 else if d ∈ q.support then w d else 0 := by
      obtain rfl | hkd := eq_or_ne k d <;> simp [g, coeff_monomial, eq_comm, *]
    refine ⟨q.coeff k, g, ne_of_apply_ne (·.coeff k) (by simp [coeff_map, h_coeff]), ?_⟩
    ext d
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_map, h_coeff]
    split_ifs with hkd hd
    · simp [hkd]
    · simp [← hw d hd, mul_comm]
    · simpa using hd
  -- Now `f i = c i • g i`, and the reduction of each `g i` is not zero.
  choose c g hg hfg using fun i : Fin n ↦ h_scale (f i)
  have : IsAlgClosed (ResidueField V) :=
    have := of_isIntegrallyClosedIn K (B := V)
    TauCeti.isAbsolutelyIntegrallyClosed_iff_isAlgClosed.mp
      (.of_surjective (residue V) residue_surjective)
  -- Over an infinite field a nonzero polynomial has a nonzero value.
  obtain ⟨y₀, hy₀⟩ :
      ∃ y₀ : σ → ResidueField V, eval y₀ (∏ i : Fin n, map (residue V) (g i)) ≠ eval y₀ 0 :=
    not_forall.1 fun h_eq ↦ prod_ne_zero_iff.2 (fun i _ ↦ hg i) (MvPolynomial.funext h_eq)
  obtain ⟨y, rfl⟩ : ∃ y : σ → V, residue V ∘ y = y₀ := residue_surjective.comp_left y₀
  have h_unit (i : Fin n) : IsUnit (eval y (g i)) := by
    rw [map_prod, map_zero, prod_ne_zero_iff] at hy₀
    rw [← residue_ne_zero_iff_isUnit]
    simpa [eval_map, ← eval₂_comp] using hy₀ i (mem_univ i)
  refine ⟨y, fun i m ↦ ?_⟩
  -- The factor `c i` is common, and the unit `eval y (g i)` divides every coefficient of `g i`.
  have h_le : v (algebraMap V K ((g i).coeff m)) ≤ v (algebraMap V K (eval y (g i))) :=
    (Valuation.integer.integers v).le_of_dvd (h_unit i).dvd
  grw [hfg i, AddMonoidAlgebra.coeff_smul_apply, coeff_map, smul_eval, eval_map, ← eval₂_comp,
    smul_eq_mul, map_mul, map_mul, h_le]

end IntegralityPrinciple

/-!
## Bounds for exponentials, logarithms and roots

The bounds come from Legendre's formula for `v(j!)` and from the binomial series over `ℤ_p`.
-/

section SeriesBounds

open PowerSeries IsUltrametricDist

namespace New
variable {p : ℕ} [Fact p.Prime]


/-- If `g(0) = 0`, then `s g(X) - g(δ X)` has constant term `0`. -/
lemma constantCoeff_smul_sub_rescale {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0)
    (s δ : ℂ_[p]) : constantCoeff (s • g - rescale δ g) = 0 := by
  simp [constantCoeff_rescale, hg_zero]

/-- The logarithmic derivative: `f (log f)' = f'` if `f(0) = 1`. -/
lemma mul_derivative_logOf {f : ℂ_[p]⟦X⟧} (hf : constantCoeff f = 1) :
    f * d⁄dX (logOf f) = d⁄dX f := by
  rw [← PowerSeries.logDeriv_def, mul_comm, PowerSeries.logDeriv_mul f hf]

section Bounds

/-- Let `g` be a series in any variables. If the coefficients of `g` in degrees `≤ l`
have norm at most `r`, those of `g ^ j` in these degrees have norm at most `r ^ j`. -/
lemma norm_coeff_pow_le {σ : Type} {g : MvPowerSeries σ ℂ_[p]} {l : ℕ} {r : ℝ}
    (hg : ∀ m : σ →₀ ℕ, m.degree ≤ l → ‖g.coeff m‖ ≤ r) (j : ℕ)
    {m : σ →₀ ℕ} (hm : m.degree ≤ l) : ‖(g ^ j).coeff m‖ ≤ r ^ j := by
  simpa using MvPowerSeries.norm_coeff_pow_mul_prod_le (c := fun _ ↦ 1)
    (fun _ ↦ zero_le_one) (fun k hk ↦ by simpa using hg k ((Finsupp.degree_mono hk).trans hm)) j

/-- Let `g` be a series in any variables with `g(0) = 0`, with coefficients in degrees `≤ l` of
norm at most `r`, and let `f = ∑ f_j X ^ j` satisfy `‖f_j‖ r ^ j ≤ s` for all `j`.
Then the coefficients of `f(g)` in degrees `≤ l` have norm at most `s`. -/
lemma norm_coeff_subst_le {σ : Type} {g : MvPowerSeries σ ℂ_[p]} {l : ℕ} {r s : ℝ}
    {f : ℂ_[p]⟦X⟧} (hg_zero : g.constantCoeff = 0)
    (hg : ∀ m : σ →₀ ℕ, m.degree ≤ l → ‖g.coeff m‖ ≤ r) (hf : ∀ j : ℕ, ‖coeff j f‖ * r ^ j ≤ s)
    {m : σ →₀ ℕ} (hm : m.degree ≤ l) : ‖(f.subst g).coeff m‖ ≤ s := by
  simpa using PowerSeries.norm_coeff_subst_mul_prod_le (c := fun _ ↦ 1)
    (fun _ ↦ zero_le_one) (.of_constantCoeff_zero hg_zero)
    (fun k hk ↦ by simpa using hg k ((Finsupp.degree_mono hk).trans hm)) hf

/-- Let `g(0) = 0`. If the coefficients of `g` in degrees `≤ l` have norm at most
`p ^ (-1 / (p - 1))`, that is, valuation at least `1 / (p - 1)`, then `exp g`, written `expSubst g`,
is integral in these degrees.

A consequence of the upper bound `v(j!) ≤ j / (p - 1)` given by Legendre's formula, applied to the
terms `g ^ j / j!` of the exponential series: the case of radius `1` of Tau Ceti's weighted bound.
-/
lemma norm_coeff_expSubst_le_one {σ : Type} {g : MvPowerSeries σ ℂ_[p]}
    (hg_zero : g.constantCoeff = 0) {l : ℕ}
    (hg : ∀ m : σ →₀ ℕ, m.degree ≤ l → ‖g.coeff m‖ ≤ p ^ (-(1 / (p - 1)) : ℝ))
    {m : σ →₀ ℕ} (hm : m.degree ≤ l) : ‖(expSubst g).coeff m‖ ≤ 1 := by
  simpa using PowerSeries.norm_coeff_subst_exp_mul_prod_le_one (p := p) (c := fun _ ↦ 1)
    (fun _ ↦ zero_le_one) hg_zero
    (fun k hk ↦ by simpa using hg k ((Finsupp.degree_mono hk).trans hm))

end Bounds

/-- If the coefficients of the series `g` in one variable below the degree `l` have norm at most
`r`, those of `g ^ j` below the degree `l` have norm at most `r ^ j`. -/
lemma norm_coeff_pow_le_of_lt {g : ℂ_[p]⟦X⟧} {l : ℕ} {r : ℝ}
    (hg : ∀ n < l, ‖coeff n g‖ ≤ r) (j : ℕ) {n : ℕ} (hn : n < l) : ‖coeff n (g ^ j)‖ ≤ r ^ j := by
  refine norm_coeff_pow_le (l := n) (fun m hm ↦ ?_) j (Finsupp.degree_single () n).le
  rw [Finsupp.unique_single m] at hm ⊢
  exact hg _ (by simpa using hm.trans_lt hn)

/-- Let `g` be a series in one variable with `g(0) = 0`, with coefficients below the degree `l`
of norm at most `r`, and let `f = ∑ f_j X ^ j` satisfy `‖f_j‖ r ^ j ≤ s` for all
`j`. Then the coefficients of `f(g)` below the degree `l` have norm at most `s`. -/
lemma norm_coeff_subst_le_of_lt {f g : ℂ_[p]⟦X⟧} {l : ℕ} {r s : ℝ}
    (hg_zero : constantCoeff g = 0) (hg : ∀ n < l, ‖coeff n g‖ ≤ r)
    (hf : ∀ j : ℕ, ‖coeff j f‖ * r ^ j ≤ s) {n : ℕ} (hn : n < l) : ‖coeff n (f.subst g)‖ ≤ s := by
  refine norm_coeff_subst_le (l := n) hg_zero (fun m hm ↦ ?_) hf (Finsupp.degree_single () n).le
  rw [Finsupp.unique_single m] at hm ⊢
  exact hg _ (by simpa using hm.trans_lt hn)

/-- A triangular system: let `x = X ^ 2 + ⋯` be integral below the degree `l` and `R` a polynomial.
If the coefficients of `R(x)` below the degree `l` have norm at most `s`, then so do the
coefficients `R_i` of `R` with `2 i < l`. -/
lemma norm_coeff_le_of_aeval {x : ℂ_[p]⟦X⟧} {l : ℕ} {s : ℝ} (h_dvd : X ^ 2 ∣ x)
    (h_two : coeff 2 x = 1) (hx : ∀ n < l, ‖coeff n x‖ ≤ 1) {R : Polynomial ℂ_[p]}
    (hR : ∀ n < l, ‖coeff n (R.aeval x)‖ ≤ s) {i : ℕ} (hi : 2 * i < l) : ‖R.coeff i‖ ≤ s := by
  -- Induction on `i`: in degree `2 i` only the powers `x ^ j` with `j ≤ i` contribute to `R(x)`,
  -- and `x ^ i` has the coefficient `1` there.
  obtain ⟨u, rfl⟩ := h_dvd
  have hu : constantCoeff u = 1 := by simpa [coeff_X_pow_mul'] using h_two
  have hs : HasSubst (X ^ 2 * u) := .of_constantCoeff_zero' (by simp)
  have h_pow (j n : ℕ) :
      coeff n ((X ^ 2 * u) ^ j) = if 2 * j ≤ n then coeff (n - 2 * j) (u ^ j) else 0 := by
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul']
  induction i using Nat.strong_induction_on with | _ i ih => ?_
  have h_lead : coeff (2 * i) ((X ^ 2 * u) ^ i) = 1 := by simp [h_pow i, hu]
  have h_zero (j : ℕ) (hj : i < j) : coeff (2 * i) ((X ^ 2 * u) ^ j) = 0 := by
    rw [h_pow, ite_eq_right (by omega)]
  have h_sum : coeff (2 * i) (R.aeval (X ^ 2 * u)) =
      ∑ j ∈ Finset.range i, R.coeff j * coeff (2 * i) ((X ^ 2 * u) ^ j) + R.coeff i := by
    rw [← subst_coe hs, coeff_subst' hs,
      finsum_eq_sum_of_support_subset (s := Finset.range (i + 1)) _ fun j hj ↦ ?_,
      Finset.sum_range_succ, h_lead]
    · simp
    · by_contra h_not
      exact hj (by simp [h_zero j (by simpa using h_not)])
  have h_lower : ‖∑ j ∈ Finset.range i, R.coeff j * coeff (2 * i) ((X ^ 2 * u) ^ j)‖ ≤ s := by
    refine norm_sum_le_of_forall_le_of_nonneg ((norm_nonneg _).trans (hR _ hi)) fun j hj ↦ ?_
    have hj_lt : j < i := Finset.mem_range.1 hj
    have h_int : ‖coeff (2 * i) ((X ^ 2 * u) ^ j)‖ ≤ 1 :=
      (norm_coeff_pow_le_of_lt hx j hi).trans_eq (one_pow j)
    grw [norm_mul, h_int, mul_one, ih j hj_lt (by omega)]
  rw [eq_sub_of_add_eq' h_sum.symm, sub_eq_add_neg]
  exact (norm_add_le_max _ _).trans (max_le (hR _ hi) (by rwa [norm_neg]))

/-- Legendre's bound `v((n + 1)!) ≤ n / (p - 1)`, for the norm of `ℂ_p`. -/
lemma rpow_pow_le_norm_factorial_succ (n : ℕ) :
    ((p : ℝ) ^ (-(1 / (p - 1)) : ℝ)) ^ n ≤ ‖((n + 1).factorial : ℂ_[p])‖ := by
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  have h : ((p : ℝ) - 1) * (multiplicity p (n + 1).factorial : ℝ) ≤ n := by
    rw [← Nat.cast_pred (Fact.out : p.Prime).pos]
    exact_mod_cast Nat.le_of_lt_succ
      (sub_one_mul_multiplicity_factorial_lt_of_ne_zero p n.succ_ne_zero)
  rw [← Real.rpow_mul_natCast p.cast_nonneg, neg_mul, one_div_mul_eq_div,
    norm_natCast_eq_inv_pow_padicValNat (n + 1).factorial_ne_zero, Nat.padicValNat_def]
  simpa [Real.rpow_neg] using Real.rpow_le_rpow_of_exponent_le hp.le
    (neg_le_neg ((le_div_iff₀' (sub_pos.2 hp)).2 h))

/-- If `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, then `c ^ j / (j + 1)!` is
integral, as `v((j + 1)!) ≤ j / (p - 1)`. -/
lemma norm_pow_le_norm_factorial_succ {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) (j : ℕ) :
    ‖c‖ ^ j ≤ ‖((j + 1).factorial : ℂ_[p])‖ := by
  exact (pow_le_pow_left₀ (norm_nonneg c) hc j).trans
    (rpow_pow_le_norm_factorial_succ j)

/-- If `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, then `c ^ j / (j + 1)` is
integral. -/
lemma norm_pow_le_norm_succ {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) (j : ℕ) :
    ‖c‖ ^ j ≤ ‖((j + 1 : ℕ) : ℂ_[p])‖ := by
  grw [norm_pow_le_norm_factorial_succ hc j, Nat.factorial_succ, Nat.cast_mul, norm_mul,
    norm_natCast_le_one ℂ_[p] j.factorial, mul_one]

/-- Let `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, and `g(0) = 0`. If `c` divides
the coefficients of `g` below the degree `l`, that is, they have norm at most `‖c‖`, then it also
divides those of `exp g - 1`, where `exp g` is `expSubst g`. -/
lemma norm_coeff_expSubst_sub_one_le {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ))
    {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0) {l : ℕ} (hg : ∀ n < l, ‖coeff n g‖ ≤ ‖c‖)
    {n : ℕ} (hn : n < l) : ‖coeff n (expSubst g - 1)‖ ≤ ‖c‖ := by
  have hs : HasSubst g := .of_constantCoeff_zero' hg_zero
  have h_subst : expSubst g - 1 = (exp ℂ_[p] - 1).subst g := by
    rw [subst_sub hs, ← coe_substAlgHom hs, map_one, coe_substAlgHom]
  rw [h_subst]
  refine norm_coeff_subst_le_of_lt hg_zero hg ?_ hn
  rintro (_ | j)
  · simp
  calc ‖coeff (j + 1) (exp ℂ_[p] - 1)‖ * ‖c‖ ^ (j + 1)
      = ‖c‖ ^ j / ‖((j + 1).factorial : ℂ_[p])‖ * ‖c‖ := by
        simp [coeff_one, coeff_exp, pow_succ, div_eq_inv_mul, mul_assoc]
    _ ≤ ‖c‖ := mul_le_of_le_one_left (norm_nonneg c)
      (div_le_one_of_le₀ (norm_pow_le_norm_factorial_succ hc j) (norm_nonneg _))

/-- If `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, the series `log (1 + c X) / c`
is integral: it lies in the range of `seriesToCp`, the inclusion of the integral series. -/
lemma inv_smul_rescale_log_mem {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) :
    c⁻¹ • rescale c (log ℂ_[p]) ∈ seriesToCp.range := by
  rw [mem_range_seriesToCp]
  rintro (_ | j)
  · simp
  calc ‖coeff (j + 1) (c⁻¹ • rescale c (log ℂ_[p]))‖
      = ‖c‖⁻¹ * ‖c‖ * (‖c‖ ^ j / ‖((j + 1 : ℕ) : ℂ_[p])‖) := by
        simp [coeff_rescale, coeff_log, pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm]
    _ ≤ ‖c‖ ^ j / ‖((j + 1 : ℕ) : ℂ_[p])‖ :=
        mul_le_of_le_one_left (by positivity) (inv_mul_le_one_of_le₀ le_rfl (norm_nonneg c))
    _ ≤ 1 := div_le_one_of_le₀ (norm_pow_le_norm_succ hc j) (norm_nonneg _)

/-- For `m` prime to `p` the series `1 + X` has an `m`-th root with constant term `1` and integral
coefficients (it lies in the range of `seriesToCp`): the binomial series with exponent `1 / m`, as
its coefficients lie in `ℤ_p`. -/
lemma exists_pow_eq_one_add_X {m : ℕ} (hm : p.Coprime m) :
    ∃ b : ℂ_[p]⟦X⟧, b ∈ seriesToCp.range ∧ constantCoeff b = 1 ∧ b ^ m = 1 + X := by
  -- The exponent `r = 1 / m` lies in `ℤ_p`.
  obtain ⟨r, hr⟩ : ∃ r : ℤ_[p], m * r = 1 :=
    (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hm)).exists_right_inv
  let φ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have h_norm (x : ℤ_[p]) : ‖φ x‖ ≤ 1 :=
    (norm_algebraMap' ℂ_[p] (x : ℚ_[p])).trans_le x.norm_le_one
  refine ⟨(binomialSeries ℤ_[p] r).map φ, mem_range_seriesToCp.2 fun n ↦ h_norm _, ?_, ?_⟩
  · simp [← coeff_zero_eq_constantCoeff_apply]
  · rw [← map_pow, ← binomialPow_one_add_X, pow_binomialPow (by simp), nsmul_eq_mul, hr,
      binomialPow_one (by simp), map_add, map_one, map_X]

/-- Two series with constant term `1` and the same `m`-th power, `m ≠ 0`, are equal. -/
lemma eq_of_pow_eq_pow_of_constantCoeff_eq_one {f g : ℂ_[p]⟦X⟧} {m : ℕ} (hm : m ≠ 0)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h_pow : f ^ m = g ^ m) : f = g := by
  apply (binomialPow_left_inj hf hg (Units.mk0 (m : ℚ) (Nat.cast_ne_zero.mpr hm))).mp
  simpa [hf, hg] using h_pow

namespace IsSeriesGenerator

/-- Let `B = 𝒪[[T]]` (`IsSeriesGenerator B T`: `T = X + ⋯` and `B` is the ring of all integral
series in `T`), let `f` be a series with integral coefficients (an element of the range of
`seriesToCp`) and `h ∈ B` without constant term. Then `f(h) ∈ B`. -/
lemma subst_mem {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧} (hB : IsSeriesGenerator B T)
    {f h : ℂ_[p]⟦X⟧} (hf : f ∈ seriesToCp.range) (hh : h ∈ B) (hh_zero : constantCoeff h = 0) :
    f.subst h ∈ B := by
  obtain ⟨G, rfl⟩ : ∃ G : (valRingCp p)⟦X⟧, seriesToCp G = f := hf
  obtain ⟨F, rfl⟩ := (hB.mem_iff h).1 hh
  have hF : constantCoeff F = 0 := by
    simpa [hB.constantCoeff_eq_zero, constantCoeff_seriesToCp] using hh_zero
  exact (hB.mem_iff _).2 ⟨G.subst F, (subst_seriesToCp_subst hB.constantCoeff_eq_zero hF G).symm⟩

/-- Let `B = 𝒪[[T]]` (`IsSeriesGenerator B T`), `c ≠ 0`, `v(c) ≥ 1 / (p - 1)`, that is,
`‖c‖ ≤ p ^ (-1 / (p - 1))`, and `g(0) = 0`. If `exp (c g) = 1 + c H` with `H ∈ B`, where `exp` is
`expSubst`, then `g ∈ B`. -/
lemma mem_of_expSubst_smul_eq {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}
    (hB : IsSeriesGenerator B T) {c : ℂ_[p]} (hc_ne : c ≠ 0)
    (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) {g H : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0)
    (hH : H ∈ B) (h_exp : expSubst (c • g) = 1 + c • H) : g ∈ B := by
  -- Taking logarithms gives `g = (log (1 + c X) / c)(H)`, an integral series in `H`.
  have hcg : constantCoeff (c • g) = 0 := by simp [hg_zero]
  have hH_zero : constantCoeff H = 0 := by simpa [h_exp, hc_ne] using constantCoeff_subst_exp hcg
  have hs : HasSubst H := .of_constantCoeff_zero' hH_zero
  have h_log : (c⁻¹ • rescale c (log ℂ_[p])).subst H = g :=
    calc _ = c⁻¹ • logOf (1 + c • H) := by
          rw [subst_smul hs, subst_rescale_eq_subst_smul _ hs, logOf_eq, add_sub_cancel_left]
      _ = g := by rw [← h_exp, logOf_subst_exp hcg, inv_smul_smul₀ hc_ne]
  rw [← h_log]
  exact hB.subst_mem (inv_smul_rescale_log_mem hc) hH hH_zero

/-- Let `B = 𝒪[[T]]` (`IsSeriesGenerator B T`: `T = X + ⋯` and `B` is the ring of all integral
series in `T`), `m` prime to `p` and `g(0) = 0`. If `(exp g) ^ m ∈ B`, where `exp g` is
`expSubst g`, then `exp g ∈ B`. -/
lemma expSubst_mem_of_pow_mem {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}
    (hB : IsSeriesGenerator B T) {m : ℕ} (hm : p.Coprime m) {g : ℂ_[p]⟦X⟧}
    (hg_zero : constantCoeff g = 0) (h_pow : expSubst g ^ m ∈ B) : expSubst g ∈ B := by
  -- If `b(0) = 1` and `b ^ m = 1 + X`, then `exp g` is `b` at `(exp g) ^ m - 1`.
  obtain ⟨b, hb_mem, hb_one, hb_pow⟩ := exists_pow_eq_one_add_X hm
  have hm_ne : m ≠ 0 := fun h ↦ (Fact.out : p.Prime).ne_one (by simpa [h] using hm)
  set u : ℂ_[p]⟦X⟧ := expSubst g ^ m - 1 with hu
  have hu_zero : constantCoeff u = 0 := by simp [hu, constantCoeff_subst_exp hg_zero]
  have hs : HasSubst u := .of_constantCoeff_zero' hu_zero
  have h_root : b.subst u = expSubst g := by
    refine eq_of_pow_eq_pow_of_constantCoeff_eq_one hm_ne
      ((constantCoeff_subst_eq hu_zero).trans hb_one)
      (constantCoeff_subst_exp hg_zero) ?_
    rw [← subst_pow hs, hb_pow, ← coe_substAlgHom hs, map_add, map_one, substAlgHom_X, hu]
    ring
  rw [← h_root]
  exact hB.subst_mem hb_mem (sub_mem h_pow (one_mem B)) hu_zero

end IsSeriesGenerator

end New

end SeriesBounds
