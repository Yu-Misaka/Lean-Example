import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.GroupWithZero.Action.Faithful
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.Qify

/-!
# Discriminate of quadratic extensions

This file contains results concerning discriminate of quadratic extensions, i.e.,
extensions of ℚ of degree 2. It can be easily deduced that any quadratic extension
can be viewed as an extension of ℚ by the square root of a square free integer.

# Main results

- `quadratic.repr` : In a quadratic extension `S` over `R` with power basis `base`,
  any element `α` can be written as `r + s * adj`, where `r, s ∈ R` and `adj` is the
  generator of the power basis.

- `Q.repr` : For any element `α` in `ℚ(√d)` (`d` a square free integer that is not 1),
  there exists integers `a`, `b` and natural number `c` such that `α = (a + b * √d) / c`.
  Whats more, `gac(a, b, c) = 1`.

- `Q.minpoly_div` : Under the notation of `Q.repr`, the minimal polynomial of `α` divides
  `X ^ 2 - (2a / c) X + ((a ^ 2 - (b ^ 2) d) / (c ^ 2))`.
  When `α` is not rational, `Q.minpoly_of_not_mem` shows that the above polynomial is
  precisely the minimal polynomial of `α`.

- `minpoly_of_int` : An element `α` in `ℚ(√d)` is an algebraic integer iff its polynomial
  has coefficients in `ℤ`.

- `minpoly_of_int'` : Under the notation of `Q.repr`, if `α` is algebraic integer but not
  rational, then `c ∣ 2 * a` and `c ^ 2 ∣ a ^ 2 - (b ^ 2) * d`.

- `Z₁.ring_of_int'` : Under the notation of `Q.repr`, when `¬ d ≡ 1 [ZMOD 4]`,
  the ring of integers of `ℚ(√d)` (`𝓞 ℚ(√d)`) is `ℤ`-isomorphic to `ℤ[√d]`.

- `Z₁.final` : Under the notation of `Q.repr`, when `¬ d ≡ 1 [ZMOD 4]`,
  the discriminate of `ℚ(√d)` is `4 * d`.

- `Z₂.ring_of_int` : Under the notation of `Q.repr`, when `d ≡ 1 [ZMOD 4]`,
  the ring of integers of `ℚ(√d)` (`𝓞 ℚ(√d)`) is `ℤ`-isomorphic to `ℤ[(1 + √d) / 2]`.

- `Z₂.final` : Under the notation of `Q.repr`, when `d ≡ 1 [ZMOD 4]`,
  the discriminate of `ℚ(√d)` is `d`.

- `quadratic_discr` : The discriminate of `ℚ(√d)` for square free integer `d` is
  `4 * d` when `¬ d ≡ 1 [ZMOD 4]`, and `d` when `d ≡ 1 [ZMOD 4]`. This relax the condition
  that `d` is not 1 in `Z₁.final` and `Z₂.final`.
-/

open IntermediateField Polynomial PowerBasis NumberField

section quadratic

/-- A helper lemma to change the type `Fin l` to `Fin n` in a sum, when `n = l`. -/
theorem finChange {l n : ℕ} (hl : n = l) {T : Type*} {f : Fin l → T} [AddCommMonoid T] :
  ∑ i : Fin l, f i = ∑ i : Fin n, f ((finCongr hl).toFun i) :=
    (Fin.sum_congr' f hl).symm

-- Variables for a general quadratic extension S/R
variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
variable {base : PowerBasis R S} (hdim : 2 = dim base)

include hdim

/-- The first element of the power basis `base` (corresponding to `gen ^ 0`) is 1. -/
private theorem base_equiv_zero : (basis base) (finCongr hdim 0) = 1 := by
  -- Use hdim to prove index is in bounds
  have : (finCongr hdim 0) = ⟨0, by rw [← hdim]; omega⟩ := rfl
  rw [this, basis_eq_pow base _] -- Basis element is power of generator
  simp only [adjoin.powerBasis_gen, pow_zero] -- gen ^ 0 = 1

/-- Abbreviation for the second element of the power basis (the generator `gen ^ 1`). -/
noncomputable abbrev adj := (basis base) (finCongr hdim 1)

/-- In a quadratic extension `S` over `R` with power basis `base`, any element `α` can be
written as `r + s * adj`, where `r, s ∈ R` and `adj` is the generator of the power basis. -/
theorem quadratic.repr (α : S) :
    ∃ r s : R, α = (algebraMap R S) r + s • (adj hdim) := by
  have := Basis.sum_repr (basis base) α -- Express α in the basis `base`
  have foo : ∀ r : R, r • (1 : S) = (algebraMap R S) r := fun r ↦
    (Algebra.algebraMap_eq_smul_one r).symm -- Scalar action is same as algebra map for 1
  rw [finChange hdim, Fin.sum_univ_two, -- Change sum type and expand for Fin 2
    show (finCongr hdim).toFun = finCongr hdim by rfl, base_equiv_zero hdim, foo] at this
  -- The representation is r * base[0] + s * base[1] = r * 1 + s * adj
  exact ⟨((basis base).repr α) (finCongr hdim 0),
    ((basis base).repr α) (finCongr hdim 1), this.symm⟩

end quadratic

-- Let `d` be a square-free integer
variable {d : ℤ} (sqf : Squarefree d)

-- Notation for the polynomial `X ^ 2 - d` over ℚ
local notation: max "poly" => X ^ 2 - C (d : ℚ)
-- Notation for the complex square root
local notation: max "√-" i =>  ((i : ℂ) ^ ((1 / 2) : ℂ))
-- Notation for the polynomial `X ^ 2 - (2a / c) X + (a ^ 2 - (b ^ 2) d) / (c ^ 2)` over ℚ
local notation: max "minpo(" a"," b"," c ")" =>
  X ^ 2 - C ((2 * a : ℚ) / (c : ℚ)) * X + C ((a ^ 2 - (b ^ 2) * d) / (c ^ 2 : ℚ))

/-- Factors the polynomial `minpo(a, b, c)` over the complex numbers.
The roots are `(a ± b√d) / c`. -/
theorem minpoly_break {a b c : ℚ} : Polynomial.map (algebraMap ℚ ℂ) minpo(a, b, c) =
    (X - C ((a + b * √-d) / c)) * (X - C ((a - b * √-d) / c)) := by
  -- Map polynomial operations over ℂ
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_mul, map_C, map_div₀, eq_ratCast, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_intCast, one_div]
  rw [sub_mul, mul_sub, mul_sub, ← C_mul, mul_comm X (C _), sub_sub,
    ← add_sub_assoc, ← add_mul, ← C_add, ← sq, div_add_div_same]
  conv =>
    enter [2, 2, 1, 1] -- Target the coefficient of X
    ring_nf
  conv =>
    enter [2, 2, 2, 2] -- Target the constant coefficient
    ring_nf
    rw [inv_pow, one_div, Complex.cpow_ofNat_inv_pow, ← sub_mul]
  ring_nf

/-- The algebra map from the quadratic field `ℚ(√d)` to `ℂ` is injective. -/
theorem algMap_inj : Function.Injective (algebraMap ℚ⟮√-d⟯ ℂ) :=
  FaithfulSMul.algebraMap_injective ℚ⟮√-d⟯ ℂ

section nontrivial

-- Assume `d` is not 1 (so the extension is nontrivial)
variable (one : d ≠ 1)

namespace Q -- Results specific to the field `ℚ(√d)`

/-- The polynomial `X ^ 2 - d` has degree 2 over ℚ. -/
private theorem poly_natDegree : natDegree poly = 2 := natDegree_X_pow_sub_C
/-- The polynomial `X ^ 2 - d` is monic. -/
private theorem poly_Monic : Monic poly := by monicity!
/-- `√d` (as a complex number) is integral over ℚ, witnessed by `poly`. -/
private theorem integral : IsIntegral ℚ √-d := by
  refine isAlgebraic_iff_isIntegral.1 ⟨poly, Monic.ne_zero poly_Monic, ?_⟩ -- Use poly
  simp only [one_div, map_intCast, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow,
    sub_self] -- Evaluate poly at √d, it's zero

/-- The extension `ℚ(√d)` is finite-dimensional over `ℚ`. -/
instance : Module.Finite ℚ ℚ⟮√-d⟯ := adjoin.finiteDimensional integral
/-- `ℚ(√d)` is a number field. -/
instance : NumberField ℚ⟮√-d⟯ := NumberField.mk

-- Power basis `{1, √d}` for `ℚ(√d)` over ℚ
local notation3 "base" => adjoin.powerBasis integral (x := √-d)
-- Generator `δ = √d` as an element of `ℚ(√d)`
local notation3 "δ" => AdjoinSimple.gen ℚ √-d

/-- The square of the generator `δ` is `d`. -/
private theorem sqd_sq : δ ^ 2 = d := by
  apply SetLike.coe_eq_coe.1 -- Work with the underlying complex numbers
  show (√-d) ^ 2 = d
  simp only [one_div, Complex.cpow_ofNat_inv_pow] -- `√d ^ 2 = d`

include one sqf

/-- For a square-free integer `d ≠ 1`, `a ^ 2 - d ≠ 0` for any rational `a`.
This ensures `√d` is not rational. -/
private theorem rat_sq_sub_ne_zero (a : ℚ) : a ^ 2 - d ≠ 0 := by
  by_contra! h -- Assume `a ^ 2 - d = 0`, so `a ^ 2 = d`
  -- Write `a = num / den`
  apply_fun (· + (d : ℚ)) at h
  rw [sub_add_cancel, zero_add, ← Rat.num_div_den a, div_pow] at h
  apply_fun (· * (a.den : ℚ) ^ 2) at h -- Clear denominators
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    Nat.cast_eq_zero, Rat.den_ne_zero, IsUnit.div_mul_cancel] at h -- Simplify
  norm_cast at h -- h is now `a.num ^ 2 = d * (a.den ^ 2)`
  -- This implies `d` divides `a.num ^ 2`, so `d` must divide `a.num` (since d is square-free)
  -- But since `a = num / den` is reduced, `gcd(num, den) = 1`.
  -- We deduce `|num| = 1` and `den = 1` (requires detailed Squarefree argument).
  have dvd : a.num * a.num ∣ d * (a.den ^ 2) :=
    ⟨1, by rw [mul_one, ← pow_two]; exact h.symm⟩
  replace dvd : a.num.natAbs ∣ a.den ^ 2 := Int.ofNat_dvd_right.1 <|
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right sqf dvd -- Key step using squarefree
  rw [pow_two] at dvd
  -- Since `gcd(num, den) = 1`, `gcd(num, den ^ 2) = 1`.
  -- Since `num | den ^ 2`, we must have `num = 1` or `num = -1`.
  replace dvd : a.num.natAbs = 1 := Nat.Coprime.eq_one_of_dvd (Rat.reduced a) <|
    Nat.Coprime.dvd_of_dvd_mul_left (Rat.reduced a) dvd
  -- Substitute back `|num| = 1` into `(a.num) ^ 2 = d * (a.den) ^ 2`
  rw [show a.num ^ 2 = a.num.natAbs ^ 2 by exact Int.natAbs_eq_iff_sq_eq.mp rfl,
    dvd, show @Nat.cast ℤ instNatCastInt 1 = 1 by rfl, one_pow,
    Int.eq_one_of_mul_eq_one_left (Int.ofNat_zero_le (a.den ^ 2)) h.symm,
    mul_one] at h
  exact one h.symm -- This contradicts `d ≠ 1`

/-- `√d` is not a rational number (since `d` is square-free and not 1). -/
private theorem sqrt_d_not_mem : (√-d) ∉ (algebraMap ℚ ℂ).range := by
  rintro ⟨x, hx⟩ -- Assume `√d = x` for some `x ∈ ℚ`
  absurd rat_sq_sub_ne_zero sqf one x -- This leads to a contradiction
  apply_fun (· ^ 2) at hx -- Square both sides: `d = x ^ 2`
  simp only [eq_ratCast, one_div, Complex.cpow_ofNat_inv_pow] at hx
  norm_cast at hx -- hx is now `x ^ 2 = d`
  rw [hx, sub_self] -- So `x ^ 2 - d = 0`, contradicting `rat_sq_sub_ne_zero`

/-- The polynomial `X ^ 2 - d` is irreducible over ℚ. -/
private theorem poly_irr : Irreducible poly := by
  -- A quadratic polynomial is irreducible iff it has no roots in the base field.
  refine (irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 ?_
  <;> (try rw [poly_natDegree]); (try omega) -- Degree is 2
  · refine Multiset.eq_zero_iff_forall_not_mem.2 (fun a ↦ ?_) -- Show roots multiset is empty
    by_contra! -- Assume `a` is a root
    simp only [mem_roots', ne_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at this
    -- If `a` is a root, then `a ^ 2 - d = 0`
    exact (rat_sq_sub_ne_zero sqf one a) this.2 -- Contradicts previous lemma

/-- The minimal polynomial of `√d` over `ℚ` is `X ^ 2 - d`. -/
private theorem poly_min : minpoly ℚ (√-d) = poly := by
  -- Minimal polynomial is the unique monic irreducible polynomial with the element as a root.
  refine (minpoly.eq_of_irreducible_of_monic (poly_irr sqf one) ?_ poly_Monic).symm
  -- Show `√d` is a root of `poly`
  simp only [one_div, map_intCast, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow,
    sub_self]

/-- The dimension of the power basis `base` (i.e., the degree of the extension) is 2. -/
private theorem base_dim : 2 = dim base :=
  have : Module.finrank ℚ ℚ⟮√-d⟯ = 2 :=
    -- Finrank is the degree of the minimal polynomial
    poly_natDegree ▸ poly_min sqf one ▸ adjoin.finrank integral
  this ▸ finrank base -- Power basis dimension equals field extension degree

/-- The second element of the power basis `base` is the generator `δ = √d`. -/
private theorem base_equiv_one : adj (base_dim sqf one) = δ := by
  have : (finCongr (base_dim sqf one) 1) =
    ⟨1, by rw [← base_dim sqf one]; omega⟩ := rfl -- Index 1 is valid
  rw [adj, this, basis_eq_pow base _] -- Definition of `adj` and basis element
  simp only [adjoin.powerBasis_gen, pow_one] -- `gen ^ 1 = gen = δ`

/-- Any element `α` in `ℚ(√d)` can be written as `r + s * √d` with `r, s ∈ ℚ`. -/
private theorem linear_comb (α : ℚ⟮√-d⟯) : ∃ r s : ℚ, α = r + s * δ := by
  have := quadratic.repr (base_dim sqf one) α -- Apply general quadratic representation
  rwa [base_equiv_one sqf one] at this -- Substitute the generator

/-- Any element `α` in `ℚ(√d)` can be written as `(a + b * √d) / c` with
`a, b ∈ ℤ`, `c ∈ ℕ`, `c ≠ 0`. -/
private theorem int_linear_comb (α : ℚ⟮√-d⟯) :
    ∃ a b : ℤ, ∃ c : ℕ, α = (a + b * δ) / (c : ℚ) ∧ c ≠ 0 := by
  obtain ⟨r, s, hrs⟩ := linear_comb sqf one α -- Get `r, s ∈ ℚ`
  rw [← Rat.num_div_den r, ← Rat.num_div_den s] at hrs -- Write `r, s` as fractions
  -- Combine fractions over a common denominator `r.den * s.den`
  have : α = (r.num * s.den + s.num * r.den * δ) / (r.den * s.den : ℚ) := by
    rw [hrs] -- Substitute `hrs`
    field_simp -- Simplify the expression
    exact mul_right_comm _ δ _ -- Ensure `δ` multiplies the numerator term
  -- Define `a, b, c`
  refine ⟨r.num * s.den, s.num * r.den, r.den * s.den, ⟨?_, Nat.mul_ne_zero r.den_nz s.den_nz⟩⟩
  convert this <;> norm_cast -- Check the expression matches and cast types

/-- Representation of `α ∈ ℚ(√d)` as `(a + b√d) / c` where `a, b ∈ ℤ`, `c ∈ ℕ`, `c ≠ 0`,
and `gcd(a, b, c) = 1` (i.e., no integer other than `±1` divides all three). -/
private theorem repr (α : ℚ⟮√-d⟯) : ∃ a b : ℤ, ∃ c : ℕ,
    α = (a + b * δ) / (c : ℚ) ∧
    c ≠ 0 ∧
    ∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n := by
  obtain ⟨a, b, c, habc, hc_zero⟩ := int_linear_comb sqf one α -- Get `a, b, c`
  set e := (a.gcd b : ℤ).gcd c with def_e -- Calculate `gcd(a, b, c)`
  -- Divide a, b, c by their gcd `e`
  obtain ⟨a', ha⟩ : (e : ℤ) ∣ a := by rw [def_e, Int.gcd_assoc]; exact Int.gcd_dvd_left
  obtain ⟨b', hb⟩ : (e : ℤ) ∣ b := by
    rw [def_e, Int.gcd_comm, ← Int.gcd_assoc]; exact Int.gcd_dvd_right
  obtain ⟨c', hc⟩ : (e : ℤ) ∣ c := by rw [def_e]; exact Int.gcd_dvd_right
  have c_pow : 0 < c' := by -- The new denominator `c'` must be positive
    by_contra! zle -- Assume `c' ≤ 0`
    have : e * c' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.ofNat_zero_le e) zle
    rw [← hc] at this; omega -- `c = e * c' ≤ 0`, contradicts `c > 0` (since `c ∈ ℕ, c ≠ 0`)
  -- Lift `c' : ℤ` to `c'' : ℕ`
  obtain ⟨c'', hc''⟩ : ∃ c'' : ℕ, c'' = c' := CanLift.prf c' <| Int.le_of_lt c_pow
  have e_ne_zero : e ≠ 0 := fun foo ↦ by
    -- If `e = 0`, then `c = 0`
    simp only [foo, CharP.cast_eq_zero, zero_mul, Nat.cast_eq_zero] at hc
    exact hc_zero hc -- Contradicts `c ≠ 0`
  refine ⟨a', b', c'', ⟨?_, ?_⟩⟩ -- Return the new `a', b', c''`
  · -- Check the expression `α = (a' + b' * δ) / c''`
    have : (a' + b' * δ) / (c'' : ℚ) = e * (a' + b' * δ) / (e * (c'' : ℚ)) := by
      -- Multiply numerator and denominator by `e` (as rationals)
      ring_nf
      rw [mul_assoc _ (e : ℚ⟮√-d⟯) _, mul_assoc _ (e : ℚ⟮√-d⟯) _,
        mul_inv_cancel₀ <| Nat.cast_ne_zero.mpr e_ne_zero, mul_one, mul_one]
    have foo : @Nat.cast ℚ Rat.instNatCast c'' = @Int.cast ℚ Rat.instIntCast c' :=
      Rat.ext hc'' rfl -- Cast `c''` to ℚ matches cast `c'` to ℚ
    rw [this, mul_add, ← mul_assoc, foo] -- Distribute `e`
    norm_cast -- Cast types
    rwa [← ha, ← hb, ← hc] -- Substitute back `a = ea'`, `b = eb'`, `c = ec' = ec''`
  · constructor
    · convert_to (c'' : ℤ) ≠ 0
      · exact Int.ofNat_eq_zero.symm
      · rw [hc'']; exact (Int.ne_of_lt c_pow).symm
    · intro n hn
      have : n ∣ (a.gcd b) := Int.dvd_gcd (ha.symm ▸ dvd_mul_of_dvd_right hn.1 e)
        <| hb.symm ▸ dvd_mul_of_dvd_right hn.2.1 e
      have bar := Int.gcd_eq_gcd_ab (a.gcd b) c -- Bezout for `gcd(gcd(a,b), c)`
      rw [← def_e] at bar -- `e = l₁ * gcd(a,b) + l₂ * c`
      set l₁ := ((a.gcd b) : ℤ).gcdA c; set l₂ := ((a.gcd b) : ℤ).gcdB c
      rw [Int.gcd_eq_gcd_ab a b] at bar -- `gcd(a,b) = l₃ * a + l₄ * b`
      set l₃ := a.gcdA b; set l₄ := a.gcdB b
      -- Substitute Bezout for `gcd(a,b)` into Bezout for `e`
      rw [ha, hb, hc, add_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
        ← mul_add (e : ℤ) _, mul_assoc, ← mul_add (e : ℤ) _] at bar
      nth_rw 1 [← mul_one (e : ℤ)] at bar
      rw [Int.mul_eq_mul_left_iff (Int.ofNat_ne_zero.2 e_ne_zero)] at bar
      -- `n` divides `a', b', c''`
      have := Int.dvd_add
        (Int.dvd_add (Dvd.dvd.mul_right hn.1 (l₃ * l₁)) (Dvd.dvd.mul_right hn.2.1 (l₄ * l₁)))
        (Dvd.dvd.mul_right hn.2.2 l₂)
      rw [hc'', ← bar] at this
      exact isUnit_of_dvd_one this

/-- For any `x ∈ ℚ(√d)`, its minimal polynomial over `ℚ` divides the polynomial
`minpo(a, b, c) = X ^ 2 - (2a / c) X + (a ^ 2 - (b ^ 2) d) / (c ^ 2)`,
where `x = (a + b√d) / c` is the representation with `gcd(a, b, c) = 1`. -/
theorem minpoly_div (x : ℚ⟮√-d⟯) : ∃ a b : ℤ, ∃ c : ℕ,
    minpoly ℚ x ∣ minpo(a, b, c) ∧
    c ≠ 0 ∧
    (∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n) ∧
    x = (a + b * δ) / (c : ℚ) := by
  obtain ⟨a, b, c, ⟨hx, hc, hn⟩⟩ := repr sqf one x -- Get the coprime representation
  refine ⟨a, b, c, ⟨minpoly.dvd_iff.2 ?_, hc, hn, hx⟩⟩ -- Use `minpoly.dvd_iff`
  -- We need to show `x` is a root of `minpo(a, b, c)`.
  simp only [hx, Rat.cast_natCast, map_add, map_sub, map_pow, aeval_X, map_mul, aeval_C,
    map_div₀, eq_ratCast, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast, map_natCast,
    Rat.cast_sub, Rat.cast_pow] -- Evaluate the polynomial at `x`
  ring_nf; rw [sqd_sq]; ring -- Simplify the expression, using `δ ^ 2 = d`. It evaluates to 0.

/-- If `x ∈ ℚ(√d)` is not rational (i.e., `b ≠ 0` in the representation), then its minimal
polynomial over `ℚ` *is* `minpo(a, b, c)`. -/
private theorem minpoly_of_not_mem {x : ℚ⟮√-d⟯} : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range →
  ∃ (r : Σ (_ : ℤ) (_ : ℤ), ℕ),
    minpoly ℚ x = minpo(r.1, r.2.1, r.2.2) ∧
    r.2.2 ≠ 0 ∧
    (∀ n : ℤ, n ∣ r.1 ∧ n ∣ r.2.1 ∧ n ∣ r.2.2 → IsUnit n) ∧
    x = (r.1 + r.2.1 * δ) / (r.2.2 : ℚ) := by
  -- Get `a, b, c` and the divisibility
  obtain ⟨a, b, c, ⟨hmin, hc, ⟨hn, hx⟩⟩⟩ := minpoly_div sqf one x
  refine fun h_not_rational ↦ ⟨⟨a, ⟨b, c⟩⟩, ⟨?_, hc, hn, hx⟩⟩ -- Return `a, b, c`
  -- Since `x` is not rational, its minimal polynomial has degree ≥ 2.
  rw [← minpoly.two_le_natDegree_iff (IsIntegral.of_finite ℚ x)] at h_not_rational
  -- minpoly divides `minpo`, both are monic, minpoly has degree ≥ 2, `minpo` has degree 2.
  -- Therefore, they must be equal.
  refine (eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite ℚ x)) ?_ hmin ?_).symm
  · monicity! -- `minpo` is monic
  · compute_degree! -- `minpo` has degree 2, which is ≥ degree of minpoly

/-- Calculates the coefficients `(a, b, c)` such that `minpoly ℚ x = minpo(a, b, c)`
for a non-rational element `x`. -/
noncomputable def calc_min {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range) :
    Σ (_ : ℤ) (_ : ℤ), ℕ :=
  Classical.choose <| minpoly_of_not_mem sqf one hx

/-- The properties satisfied by the coefficients `(a, b, c)` returned by `calc_min`. -/
theorem calc_min_prop {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range) :
  minpoly ℚ x =
    minpo((calc_min sqf one hx).1, (calc_min sqf one hx).2.1, (calc_min sqf one hx).2.2) ∧
  (calc_min sqf one hx).2.2 ≠ 0 ∧
  (∀ n : ℤ, n ∣ (calc_min sqf one hx).1 ∧ n ∣
    (calc_min sqf one hx).2.1 ∧ n ∣ (calc_min sqf one hx).2.2 → IsUnit n) ∧
    x = ((calc_min sqf one hx).1 + (calc_min sqf one hx).2.1 * δ) /
      ((calc_min sqf one hx).2.2 : ℚ) :=
  Classical.choose_spec <| minpoly_of_not_mem sqf one hx

end Q

section aux -- Auxiliary lemmas for integrality conditions

/-- An element `x` in a number field `K` is an algebraic integer iff its minimal polynomial
over `ℚ` has integer coefficients when viewed as a polynomial over `ℚ`.
(More precisely, `minpoly ℚ x` is the image of `minpoly ℤ x` under `map (algebraMap ℤ ℚ)`). -/
theorem minpoly_of_int (x : ℚ⟮√-d⟯) : x ∈ (integralClosure ℤ ℚ⟮√-d⟯) ↔
    minpoly ℚ x = Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ x) := by
  constructor
  -- Forward direction: If `x` is integral, this property holds.
  · exact minpoly.isIntegrallyClosed_eq_field_fractions ℚ (ℚ⟮√-d⟯)
  -- Backward direction: If the poly has ℤ coeffs, then `x` is integral.
  · intro hx
    -- The minimal polynomial over ℤ exists and is monic by definition if the condition holds.
    -- We just need to check it's non-zero.
    refine minpoly.ne_zero_iff.1 (fun hzero ↦ ?_)
    -- If `minpoly ℤ x` were zero, then `minpoly ℚ x `would be zero.
    rw [hzero, algebraMap_int_eq, Polynomial.map_zero] at hx
    -- But `minpoly ℚ x` is non-zero for elements in a finite extension.
    exact False.elim <| (minpoly.ne_zero_of_finite ℚ x) hx

/-- Technical lemma: If `gcd(a, b, c) = 1`, then `gcd(c, a)` is coprime to `b`.
(Using natAbs for gcd arguments). -/
private theorem aux_copri₀ {a b : ℤ} {c : ℕ}
  (hn : ∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n) :
    (c.gcd a.natAbs).Coprime b.natAbs := by
  by_contra not_copri -- Assume `gcd(c, |a|)` and `|b|` are not coprime, i.e., g > 1
  -- `gcd(c, |a|)` divides `|a|`
  have dvd₁ : (c.gcd a.natAbs).gcd b.natAbs ∣ a.natAbs := by
    rw [Nat.gcd_comm, ← Nat.gcd_assoc]
    exact Nat.gcd_dvd_right (b.natAbs.gcd c) a.natAbs
  -- `gcd(c, |a|)` divides `|b|`
  have dvd₂ : (c.gcd a.natAbs).gcd b.natAbs ∣ b.natAbs :=
    Nat.gcd_dvd_right (c.gcd a.natAbs) b.natAbs
  -- `gcd(c, |a|)` divides `c`
  have dvd₃ : (c.gcd a.natAbs).gcd b.natAbs ∣ c := by
    rw [Nat.gcd_assoc]
    exact Nat.gcd_dvd_left c (a.natAbs.gcd b.natAbs)
  -- Apply the hypothesis `hn` with `n = gcd(c, |a|)` (cast to ℤ)
  replace hn := hn ((c.gcd a.natAbs).gcd b.natAbs)
    ⟨Int.ofNat_dvd_left.2 dvd₁, Int.ofNat_dvd_left.2 dvd₂, Int.ofNat_dvd.2 dvd₃⟩
  -- `hn` implies `gcd(c, |a|)` is a unit. In ℕ, this means `gcd(c, |a|) = 1`.
  rw [Int.ofNat_isUnit, Nat.isUnit_iff] at hn
  -- This contradicts `gcd(c, |a|) > 1` (from `not_copri`).
  exact not_copri hn

/-- Technical lemma: If `n = a / c` where `n, a ∈ ℤ` and `c ∈ ℕ+`, then `c ∣ a`. -/
private theorem aux_dvd (n : ℤ) {a : ℤ} {c : ℕ} (hc : c ≠ 0) :
    n = (a : ℚ) / (c : ℚ) → (c : ℤ) ∣ a := fun h ↦ by
  refine ⟨n, ?_⟩ -- We need to show `a = c * n`
  qify -- Convert goal to ℚ
  rw [h] -- Substitute `n = a / c`
  exact (mul_div_cancel_of_imp' fun foo ↦ -- Simplify `(a / c) * c = a`
    False.elim (hc <| Rat.natCast_eq_zero.mp foo)).symm -- Requires `c ≠ 0`

include sqf in
/-- Technical lemma: If `gcd(a, b, c) = 1` and `c ^ 2 ∣ a ^ 2 - (b ^ 2) d`, then
`gcd(c, a) = 1`. -/
private theorem aux_copri₁ {a b : ℤ} {c : ℕ}
  (hn : ∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n)
  (hdiv : (c ^ 2 : ℤ) ∣ (a ^ 2 - b ^ 2 * d)) :
    c.Coprime a.natAbs := by
  by_contra! -- Assume `gcd(c, |a|) > 1`
  obtain ⟨k', hk'⟩ := hdiv -- `a ^ 2 - (b ^ 2) d = (c ^ 2) k'`
  -- Rearrange to `(b ^ 2) d = a ^ 2 - (c ^ 2) k'`
  apply_fun (- (- a ^ 2 + · )) at hk'
  simp only [Pi.neg_apply, neg_add_rev, neg_sub, neg_neg, sub_add_cancel] at hk'
  -- Show `gcd(c, |a|) ^ 2` divides `(b ^ 2) d`
  have hk'' : ((c.gcd a.natAbs) ^ 2 : ℤ) ∣ b ^ 2 * d := by
    rw [hk'] -- Substitute expression for `(b ^ 2) d`
    -- Show `gcd(c, |a|) ^ 2 ∣ a ^ 2` and `gcd(c, |a|) ^ 2 ∣ - (c ^ 2) k'`
    refine (Int.dvd_add_right ?_).2 ?_
    · -- `gcd(c, |a|) ^ 2 ∣ - (c ^ 2) k'`
      refine Int.dvd_neg.2 <| Dvd.dvd.mul_right ?_ k'
      -- Show `gcd(c, |a|) ^ 2 ∣ c ^ 2`
      exact (Int.pow_dvd_pow_iff (Nat.zero_ne_add_one 1).symm).2
        <| Int.ofNat_dvd.2 <| Nat.gcd_dvd_left c a.natAbs
    · -- `gcd(c, |a|) ^ 2 ∣ a ^ 2`
      exact (Int.pow_dvd_pow_iff (Nat.zero_ne_add_one 1).symm).2
        <| Int.ofNat_dvd_left.mpr <| Nat.gcd_dvd_right c a.natAbs
  -- Since `gcd(c, |a|) ^ 2 ∣ (b ^ 2) d` and `gcd(gcd(c, |a|), b) = 1` (from `aux_copri₀`),
  -- we must have `gcd(c, |a|) ^ 2 ∣ d`.
  replace hk'' := Nat.Coprime.dvd_of_dvd_mul_left
    -- Need `gcd(gcd(c, |a|) ^ 2, b ^ 2) = 1`. This follows from `gcd(gcd(c, |a|), b) = 1`.
    (Nat.Coprime.pow 2 2 (aux_copri₀ hn)) <|
      -- Convert divisibility to ℕ
      by rwa [← Int.natAbs_pow b 2, ← Int.natAbs_mul, ← Int.ofNat_dvd_left]
  -- Since `d` is square-free and `gcd(c, |a|) ^ 2 ∣ d`, we must have `gcd(c, |a|) = 1`.
  exact this <| Nat.isUnit_iff.1 <|
    (Int.squarefree_natAbs.2 sqf) (c.gcd a.natAbs) (by rwa [← sq])

include sqf in
/-- If `4 ∣ a ^ 2 - (b ^ 2) d` and `gcd(a, b, 2) = 1`, then `a` and `b` must both be odd. -/
theorem aux_congruent {a b : ℤ}
  (hdvd : (2 : ℤ) ^ 2 ∣ a ^ 2 - b ^ 2 * d)
  (hn : ∀ (n : ℤ), n ∣ a ∧ n ∣ b ∧ n ∣ (2 : ℤ) → IsUnit n) :
    Odd a ∧ Odd b := by
  have hc : 2 ≠ 0 := (Nat.zero_ne_add_one 1).symm
  have odd_a : Odd a :=
    Int.natAbs_odd.1 <| Nat.Coprime.odd_of_left (aux_copri₁ sqf hn hdvd)
  -- `a ^ 2 - (b ^ 2) d` is even (divisible by 4)
  have even_ab : Even (a ^ 2 - b ^ 2 * d) :=
    even_iff_two_dvd.mpr <| dvd_trans (dvd_pow_self 2 hc) hdvd
  -- `a ^ 2 - (b ^ 2) d` is even. So Odd - Even = Odd. Thus `(b ^ 2) d` must be odd.
  have odd_b := Odd.sub_even ((Int.odd_pow' hc).2 odd_a) even_ab
  -- Thus `b ^ 2` is odd, hence `b` is odd.
  rw [sub_sub_cancel] at odd_b
  exact ⟨odd_a, Int.Odd.of_mul_right <| Int.Odd.of_mul_left odd_b⟩

include sqf in
/-- If `4 ∣ a ^ 2 - (b ^ 2) d` and `gcd(a, b, 2) = 1`, then `d ≡ 1 [ZMOD 4]`. -/
theorem congruent {a b : ℤ}
  (hdvd : (2 : ℤ) ^ 2 ∣ a ^ 2 - b ^ 2 * d)
  (hn : ∀ (n : ℤ), n ∣ a ∧ n ∣ b ∧ n ∣ (2 : ℤ) → IsUnit n) :
    d ≡ 1 [ZMOD 4] := by
  -- We know `a` and `b` are odd from `aux_congruent`.
  obtain ⟨odd_a, odd_b⟩ := aux_congruent sqf hdvd hn
  -- `a ^ 2 - (b ^ 2) d ≡ 0 [ZMOD 4]`
  replace hzero : a ^ 2 - b ^ 2 * d ≡ 0 [ZMOD 4] :=
    Int.ModEq.symm (Dvd.dvd.zero_modEq_int hdvd)
  -- If `a, b` are odd, then `a ^ 2 ≡ 1 [ZMOD 4]` and `b ^ 2 ≡ 1 [ZMOD 4]`.
  have mod_b_sq : b ^ 2 ≡ 1 [ZMOD 4] := Int.sq_mod_four_eq_one_of_odd odd_b
  -- Substitute into the congruence: `a ^ 2 ≡ d [ZMOD 4]`
  replace hzero := Int.ModEq.add hzero <| Int.ModEq.mul_right d mod_b_sq
  simp only [sub_add_cancel, one_mul, zero_add] at hzero
  -- Since `a ^ 2 ≡ 1 [ZMOD 4]`, we have `d ≡ 1 [ZMOD 4]`.
  exact hzero.symm.trans <| Int.sq_mod_four_eq_one_of_odd odd_a

/-- If `x = (a + b√d) / c` (with `gcd = 1`) is an algebraic integer and not rational,
then `c` must divide `2`, and `c ^ 2` must divide `a ^ 2 - (b ^ 2) d`. -/
theorem minpoly_of_int' {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range)
    (h : x ∈ (integralClosure ℤ ℚ⟮√-d⟯)) :
  (Q.calc_min sqf one hx).2.2 ∣ 2 ∧
  ((Q.calc_min sqf one hx).2.2 : ℤ) ^ 2 ∣
    (Q.calc_min sqf one hx).1 ^ 2 - (Q.calc_min sqf one hx).2.1 ^ 2 * d := by
  -- Since `x` is integral, `minpoly ℚ x` has integer coefficients.
  rw [minpoly_of_int] at h
  -- Get the representation `a, b, c` and the minimal polynomial.
  obtain ⟨hmin, hc, hn⟩ := Q.calc_min_prop sqf one hx
  -- `hmin` is: `minpoly ℚ x = X ^ 2 - (2 a / c) X + (a ^ 2 - (b ^ 2) d) / (c ^ 2)`
  -- So `Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ x)` =
  -- `X ^ 2 - (2 a / c) X + (a ^ 2 - (b ^ 2) d) / (c ^ 2)`
  rw [h] at hmin
  -- Extract coefficients.
  have hmin₁ := hmin
  apply_fun (- ·.coeff 1) at hmin₁ -- Coefficient of `X`
  simp only [coeff_map, eq_intCast, coeff_add, coeff_sub, coeff_X_pow, OfNat.one_ne_ofNat,
    ↓reduceIte, coeff_mul_X, coeff_C_zero, zero_sub, coeff_C_succ, add_zero, neg_neg] at hmin₁
  -- `hmin₁` : `-(minpoly ℤ x).coeff 1 = 2a / c`
  have hmin₀ := hmin
  apply_fun (·.coeff 0) at hmin₀ -- Constant coefficient
  simp only [coeff_map, eq_intCast, coeff_add, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat,
    ↓reduceIte, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, sub_self,
    zero_add] at hmin₀
  -- `hmin₀` : `(minpoly ℤ x).coeff 0` = `(a ^ 2 - (b ^ 2) d) / (c ^ 2)`
  -- Since coeffs of `minpoly ℤ x` are integers, use `aux_dvd`.
  replace hmin₁ : ((Q.calc_min sqf one hx).2.2 : ℤ) ∣ 2 * (Q.calc_min sqf one hx).1 :=
    aux_dvd (- (minpoly ℤ x).coeff 1) hc
    <| by convert hmin₁; simp only [Int.cast_mul, Int.cast_ofNat]
  replace hmin₀ : ((Q.calc_min sqf one hx).2.2 ^ 2 : ℤ) ∣ ((Q.calc_min sqf one hx).1 ^ 2 -
      (Q.calc_min sqf one hx).2.1 ^ 2 * d) := aux_dvd ((minpoly ℤ x).coeff 0)
    (pow_ne_zero 2 hc) <| by simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
      one_mul, Nat.cast_mul, ← sq]
  -- Since `gcd(c, a) = 1` (from `aux_copri₁`), and `c ∣ 2a`, we must have `c ∣ 2`.
  exact ⟨Int.ofNat_dvd.1 <| Int.dvd_of_dvd_mul_left_of_gcd_one hmin₁
    (aux_copri₁ sqf hn.1 hmin₀), hmin₀⟩

/-- Integers are in the ℤ-algebra generated by any element `c`. -/
private theorem adjoin_mem₀ {a : ℤ} {c : ℂ}: (a : ℂ) ∈ Algebra.adjoin ℤ {c} :=
  bot_le (a := Algebra.adjoin ℤ {c}) <| Subalgebra.intCast_mem ⊥ a

/-- If `x ∈ ℚ` is an algebraic integer, then `x ∈ ℤ`.
So `x` (as a complex number) is in `Algebra.adjoin ℤ {c}` for any `c`. -/
theorem adjoin_mem₁ {x : ℚ⟮√-d⟯} {c : ℂ} (hx : x ∈ (algebraMap ℚ ℚ⟮√-d⟯).range)
    (h : x ∈ (integralClosure ℤ ℚ⟮√-d⟯)) : x.1 ∈ Algebra.adjoin ℤ {c} := by
  rw [minpoly_of_int] at h -- `minpoly ℚ x` has ℤ coeffs
  -- If `x` is rational, its minimal polynomial has degree 1.
  have minpoly_deg := minpoly.natDegree_eq_one_iff.2 hx
  rw [h, natDegree_map_eq_of_injective, minpoly.natDegree_eq_one_iff] at minpoly_deg
  swap; exact RingHom.injective_int (algebraMap ℤ ℚ)
  obtain ⟨x', hx'⟩ := minpoly_deg
  rw [← hx', algebraMap_int_eq, eq_intCast, SubringClass.coe_intCast]
  exact Subsemiring.subset_closure (Set.subset_union_left (Set.mem_range_self x'))

/-- Rationals are in the ℚ-algebra generated by any element `c`. -/
theorem adjoin_mem₂ {a : ℚ} {c : ℂ}: (a : ℂ) ∈ ℚ⟮c⟯ := by
  -- ℚ is the bottom subalgebra over ℚ
  suffices (a : ℂ) ∈ (⊥ : Subalgebra ℚ ℂ) from (bot_le (a := ℚ⟮c⟯)) this
  apply SetLike.mem_of_subset
  · simp only [Algebra.coe_bot]; rfl -- The bottom subalgebra is the image of ℚ
  · simp only [Set.mem_range, eq_ratCast, Rat.cast_inj, exists_eq] -- `a` is in the image of ℚ

/-- If `x = a + b√d` (i.e., `c = 1`) is an integer, then `x ∈ ℤ[√d]`. -/
theorem adjoin_mem₃ {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range)
    (hone : (Q.calc_min sqf one hx).2.2 = 1) : x.1 ∈ Algebra.adjoin ℤ {√-d} := by
  -- Get the representation and minimal polynomial
  obtain ⟨hmin, -, -⟩ := Q.calc_min_prop sqf one hx
  -- Map the minimal polynomial equation to ℂ
  apply_fun (Polynomial.map (algebraMap ℚ ℂ) · ) at hmin
  -- Factor the polynomial over ℂ
  rw [minpoly_break] at hmin
  -- Evaluate at `x`
  apply_fun (aeval (x : ℂ) · ) at hmin
  simp only [aeval_map_algebraMap, Subalgebra.aeval_coe, minpoly.aeval, ZeroMemClass.coe_zero,
    Rat.cast_intCast, one_div, hone, Nat.cast_one, Rat.cast_one, div_one, map_add, map_intCast,
    map_mul, map_sub, coe_aeval_eq_eval, eval_mul, eval_sub, eval_X, eval_add, eval_intCast,
    eval_C, zero_eq_mul] at hmin -- `x` is a root, simplify using `c = 1`
  -- `x = a + b√d` or `x = a - b√d` (where `a, b` are from `calc_min`)
  rcases hmin with hx₁ | hx₁ <;> rw [sub_eq_zero.1 hx₁]
  · -- Case `x = a + b√d`
    refine add_mem adjoin_mem₀ <| mul_mem adjoin_mem₀ ?_ -- `a ∈ ℤ[√d], b ∈ ℤ[√d]`
    simpa only [one_div] using Algebra.self_mem_adjoin_singleton ℤ √-d -- `√d ∈ ℤ[√d]`
  · -- Case `x = a - b√d`
    refine sub_mem adjoin_mem₀ <| mul_mem adjoin_mem₀ ?_
    simpa only [one_div] using Algebra.self_mem_adjoin_singleton ℤ √-d

end aux

namespace Z₁ -- Case 1: `d ≡ 2 or 3 (mod 4)`, i.e., `¬(d ≡ 1 [ZMOD 4])`

-- Polynomial `X  ^ 2 - d` over ℤ
local notation "polyz" => X ^ 2 - C d

/-- Degree of `X  ^ 2 - d` over ℤ is 2. -/
private theorem polyz_natDegree : natDegree polyz = 2 := natDegree_X_pow_sub_C
/-- `X  ^ 2 - d` is monic over ℤ. -/
private theorem polyz_Monic : Monic polyz := by monicity!

/-- `√d` is integral over ℤ, witnessed by `polyz`. -/
theorem integralz : IsIntegral ℤ √-d := by
  refine ⟨polyz, ⟨polyz_Monic, ?_⟩⟩
  · simp only [algebraMap_int_eq, one_div, eq_intCast, eval₂_sub, eval₂_X_pow,
    Complex.cpow_ofNat_inv_pow] -- Evaluate `polyz` at `√d`
    -- Need `√d ^ 2 - d = 0`
    show d - eval₂ (Int.castRingHom ℂ) ((d : ℂ) ^ (2⁻¹ : ℂ)) (C d) = 0
    rw [eval₂_C, eq_intCast, sub_self]

-- Power basis `{1, √d}` for `ℤ[√d]` over ℤ
local notation3 "zbase" => Algebra.adjoin.powerBasis' (@integralz d)

/-- The degree of the minimal polynomial of `√d` over `ℤ` is at most 2. -/
private theorem min_polyz_natDegree_le : (minpoly ℤ √-d).natDegree ≤ 2 := by
  rw [← @polyz_natDegree d] -- Use `polyz` degree
  -- minpoly divides `polyz`
  refine natDegree_le_of_dvd ?_ (X_pow_sub_C_ne_zero (Nat.zero_lt_two) d)
  refine minpoly.isIntegrallyClosed_dvd integralz ?_ -- Check `√d` is root of `polyz`
  simp only [one_div, eq_intCast, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow,
    map_intCast, sub_self]

/-- The generator `√d` as an element of the ℤ-algebra `ℤ[√d]`. -/
noncomputable abbrev δ : Algebra.adjoin ℤ {√-d} :=
  ⟨√-d, SetLike.mem_coe.1 <| Algebra.subset_adjoin <| Set.mem_singleton √-d⟩

/-- `δ ^ 2 = d` in the ring `ℤ[√d]`. -/
private theorem sqd_sq : (@δ d) ^ 2 = d := by
  apply SetLike.coe_eq_coe.1 -- Work with underlying complex numbers
  show (√-d) ^ 2 = d
  simp only [one_div, Complex.cpow_ofNat_inv_pow]

include sqf one

/-- The polynomial `X  ^ 2 - d` is irreducible over `ℤ`. -/
private theorem irr_polyz : Irreducible polyz := by
  -- Use Gauss's lemma: irreducible over ℤ iff irreducible over ℚ
  refine (Monic.irreducible_iff_irreducible_map_fraction_map
    (@polyz_Monic d) (K := ℚ)).2 ?_
  -- Need irreducibility of `X  ^ 2 - d` over ℚ
  convert Q.poly_irr sqf one
  simp only [algebraMap_int_eq, eq_intCast, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_intCast, map_intCast] -- Check map `ℤ → ℚ` gives the right polynomial

/-- The degree of the minimal polynomial of `√d` over `ℤ` is exactly 2. -/
private theorem min_polyz_natDegree : (minpoly ℤ √-d).natDegree = 2 := by
  refine le_antisymm min_polyz_natDegree_le ?_ -- We know ≤ 2, need ≥ 2
  -- Degree is ≥ 2 iff the element is not in the base ring (ℤ).
  -- We map to ℂ and check it's not rational.
  rw [minpoly.two_le_natDegree_iff (@integralz d)]
  rintro ⟨x, hx : (algebraMap ℚ ℂ) x = √-d⟩ -- Assume `√d` is rational
  have := Q.sqrt_d_not_mem sqf one -- We know `√d` is not rational
  rw [← hx] at this
  exact this <| RingHom.mem_range_self (algebraMap ℚ ℂ) x -- Contradiction

/-- The dimension of the power basis `zbase` (for `ℤ[√d]` over ℤ) is 2. -/
private theorem base_dim : 2 = dim zbase := by
  rw [Algebra.adjoin.powerBasis'_dim, min_polyz_natDegree sqf one] -- Dim = degree of minpoly

/-- The second element of the power basis `zbase` is the generator `δ = √d`. -/
private theorem base_equiv_one : adj (base_dim sqf one) = δ := by
  have : (finCongr (base_dim sqf one) 1) =
    ⟨1, by rw [← base_dim sqf one]; omega⟩ := rfl -- Index 1 is valid
  rw [adj, this, basis_eq_pow zbase _] -- Def of adj and basis element
  simp only [adjoin.powerBasis_gen, pow_one] -- `gen ^ 1 = gen`
  exact Algebra.adjoin.powerBasis'_gen integralz -- Generator of basis is the element itself

/-- Any element `α` in `ℤ[√d]` can be written as `r + s * √d` with `r, s ∈ ℤ`. -/
private theorem int_linear_comb (α : Algebra.adjoin ℤ {√-d}) :
    ∃ r s : ℤ, α = r + s * (@δ d) := by
  have := quadratic.repr (base_dim sqf one) α -- Apply general quadratic representation over ℤ
  rw [base_equiv_one sqf one] at this -- Substitute the generator
  simp only [algebraMap_int_eq, eq_intCast, SetLike.mk_smul_mk, one_div, zsmul_eq_mul] at this -- Simplify AlgebraMap and smul
  convert this
  simp only [MulMemClass.coe_mul, SubringClass.coe_intCast, one_div]

/-- Elements of `ℤ[√d]` (viewed as complex numbers) are contained in `ℚ(√d)`. -/
private theorem adjoin_mem₄ (α : Algebra.adjoin ℤ {√-d}) : α.1 ∈ ℚ⟮√-d⟯ := by
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one α -- Get `r, s ∈ ℤ` representation
  rw [hrs] -- Substitute
  -- Map to ℂ
  simp only [one_div, AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul]
  -- `r + s√d ∈ ℚ(√d)` since `r, s ∈ ℤ ⊂ ℚ ` and `√d ∈ ℚ(√d)`
  exact add_mem adjoin_mem₂ <| mul_mem adjoin_mem₂ <| mem_adjoin_simple_self ℚ _

/-- Elements of `ℤ[√d]` are algebraic integers in `ℚ(√d)`. -/
private theorem adjoin_of_ring_of_int (x : ℚ⟮√-d⟯) (h : x.1 ∈ Algebra.adjoin ℤ {√-d}) :
    x ∈ (integralClosure ℤ ℚ⟮√-d⟯) := by
  -- Represent `x` as `r + sδ` with `r, s ∈ ℤ`
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one ⟨x, h⟩
  have : x = r + s * (AdjoinSimple.gen ℚ √-d) :=
    Subtype.val_inj.1 <| by apply Subtype.val_inj.2 hrs -- Match types
  rw [this]
  -- Integers `r, s` are integral. `δ = √d` is integral (`integralz`).
  -- The integral closure is a ring, so `r + sδ` is integral.
  refine add_mem isIntegral_algebraMap <| mul_mem isIntegral_algebraMap ?_
  rw [mem_integralClosure_iff, ← isIntegral_algebraMap_iff (@algMap_inj d),
    AdjoinSimple.algebraMap_gen ℚ (√-d)] -- Check if `AdjoinSimple.gen` is integral
  exact integralz -- Yes, `√d` is integral over ℤ

/-- `ℤ[√d]` is a free ℤ-module of rank 2. -/
instance : Module.Free ℤ (Algebra.adjoin ℤ {√-d}) := ⟨⟨Fin (dim zbase), basis zbase⟩⟩

-- Calculate entries of the trace matrix for the basis `{1, √d}`
/-- `Trace(1 * 1) = Trace(1) = 2`. -/
private theorem traceForm_11 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) 1 1 = 2 := by
  rw [Algebra.traceForm_apply, one_mul, -- Def of trace form
    ← @algebraMap.coe_one ℤ (Algebra.adjoin ℤ {√-d}) .., -- `1 = algebraMap 1`
    Algebra.trace_algebraMap, finrank zbase, -- `Trace(algebraMap r) = dim * r`
    ← base_dim sqf one, nsmul_eq_mul, Nat.cast_ofNat, mul_one] -- `dim = 2`

/-- `Trace(1 * δ) = Trace(δ) = 0`. -/
private theorem traceForm_1δ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) 1 δ = 0 := by
  rw [Algebra.traceForm_apply, one_mul, Algebra.trace_eq_matrix_trace (basis zbase)
    δ, Matrix.trace, finChange (base_dim sqf one)] -- Use matrix trace definition
  -- Sum diagonal entries
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  -- Suppose matrix of left multiplication by `δ` in basis `{1, δ}` is `M`
  -- Need `M₀₀` and `M₁₁`
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one), mul_one]
  have neq : finCongr (base_dim sqf one) 0 ≠
    finCongr (base_dim sqf one) 1 := ne_of_beq_false rfl
  -- Calculate `M₀₀ = (repr δ)₀`
  have := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one) 1) -- Basis element `δ`
    (finCongr (base_dim sqf one) 0) -- Index 0
  rw [ite_cond_eq_false _ _ (eq_false neq.symm)] at this -- `(repr δ)₀ = 0`
  rw [← base_equiv_one sqf one, adj, this, zero_add] -- `M₀₀ = 0`
  -- Calculate `M₁₁ = (repr (δ * δ))₁`
  rw [← adj, base_equiv_one sqf one, ← sq, sqd_sq] -- `δ * δ = d`
  -- Need `(repr d)₁`. Since `d = d * 1 + 0 * δ`, `(repr d)₁ = 0`.
  have cast : @Int.cast (Algebra.adjoin ℤ {√-d}) AddGroupWithOne.toIntCast d =
    ((algebraMap ℤ (Algebra.adjoin ℤ {√-d})) d) * 1 := by -- `d = d * 1`
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  replace this := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one) 0) -- Basis element 1
    (finCongr (base_dim sqf one) 1) -- Index 1
  rw [ite_cond_eq_false _ _ (eq_false neq)] at this -- `(repr 1)₁ = 0`
  -- `(repr d)₁ = d * (repr 1)₁ = 0`
  rw [cast, Basis.repr_smul', ← base_equiv_zero (base_dim sqf one), this, mul_zero]
  -- Trace = `M₀₀ + M₁₁ = 0 + 0 = 0`

/-- `Trace(δ * 1) = Trace(δ) = 0`. -/
private theorem traceForm_δ1 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) δ 1 = 0 := by
  -- via symmetric
  simpa only [Algebra.traceForm_apply, mul_one, one_mul] using traceForm_1δ sqf one

/-- `Trace(δ * δ) = Trace(d) = 2d`. -/
private theorem traceForm_δδ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) δ δ = 2 * d := by
  rw [Algebra.traceForm_apply, ← sq, sqd_sq,
    Algebra.trace_eq_matrix_trace (basis zbase) d,
    Matrix.trace, finChange (base_dim sqf one)]
  -- Sum diagonal
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  -- Suppose matrix of left multiplication by `d` is `M`
  -- Need `M₀₀` and `M₁₁`
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one), mul_one]
  -- Calculate `M₀₀ = (repr d)₀`
  have := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one) 0) -- Basis element 1
    (finCongr (base_dim sqf one) 0) -- Index 0
  -- `(repr 1)₀ = 1`
  rw [ite_cond_eq_true _ _ (eq_self (finCongr (base_dim sqf one) 0))] at this
  have cast : @Int.cast (Algebra.adjoin ℤ {√-d}) AddGroupWithOne.toIntCast d =
    ((algebraMap ℤ (Algebra.adjoin ℤ {√-d})) d) * 1 := by -- `d = d * 1`
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  nth_rw 1 [cast]
  -- `(repr d)₀ = d * (repr 1)₀ = d`
  rw [Basis.repr_smul', ← base_equiv_zero (base_dim sqf one), this, mul_one]
  -- Calculate `M₁₁ = (repr (d * δ))₁`
  replace cast : @Int.cast (Algebra.adjoin ℤ {√-d}) AddGroupWithOne.toIntCast d =
    ((algebraMap ℤ (Algebra.adjoin ℤ {√-d})) d) := by -- Cast `d`
      rw [algebraMap_int_eq, eq_intCast]
  replace this := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one) 1) -- Basis element `δ`
    (finCongr (base_dim sqf one) 1) -- Index 1
  -- `(repr δ)₁ = 1`
  rw [ite_cond_eq_true _ _ (eq_self (finCongr (base_dim sqf one) 1))] at this
  -- `(repr (d * δ))₁ = d * (repr δ)₁ = d`
  -- Trace = `M₀₀ + M₁₁ = d + d = 2d`
  rw [cast, Basis.repr_smul', this, mul_one, Int.two_mul d]

/-- The trace matrix for the basis `{1, δ}` is `[[2, 0], [0, 2d]]`. -/
private def traceMat : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 2 * d]

/-- The trace matrix calculated using `Algebra.traceMatrix` matches `traceMat`. -/
private theorem mat_conv :
  (Matrix.reindexAlgEquiv ℤ ℤ (finCongr (base_dim sqf one)).symm)
    (Algebra.traceMatrix ℤ (basis zbase)) = @traceMat d := Matrix.ext fun i j ↦ by
  fin_cases i <;> fin_cases j -- Check all 4 entries
  all_goals simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one)]
    exact traceForm_11 sqf one
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one), ← adj,
      base_equiv_one sqf one]
    exact traceForm_1δ sqf one
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one), ← adj,
      base_equiv_one sqf one]
    exact traceForm_δ1 sqf one
  · rw [Algebra.traceMatrix, Matrix.of_apply, ← adj, base_equiv_one sqf one]
    exact traceForm_δδ sqf one

/-- The discriminant of the ℤ-basis `{1, √d}` is `det(traceMatrix) = 4d`. -/
private theorem discr_z : Algebra.discr ℤ (basis zbase) = 4 * d := by
  have := Matrix.det_reindexAlgEquiv ℤ ℤ (finCongr (base_dim sqf one)).symm
    (Algebra.traceMatrix ℤ (basis zbase)) -- Det is invariant under reindexing
  rw [Algebra.discr_def, ← this, mat_conv sqf one, traceMat, Matrix.det_fin_two_of,
    mul_zero, sub_zero, ← mul_assoc]; rfl -- Calculate `det([[2, 0], [0, 2d]])`

-- We are in the case `¬ (d ≡ 1 [ZMOD 4])`
variable (hd : ¬ d ≡ 1 [ZMOD 4])

include hd

/-- The ring of integers of `ℚ(√d)` is `ℤ[√d]` when `¬ (d ≡ 1 [ZMOD 4])`. -/
theorem ring_of_int (x : ℚ⟮√-d⟯) : x ∈ (integralClosure ℤ ℚ⟮√-d⟯) ↔
  x.1 ∈ Algebra.adjoin ℤ {√-d} := by
  constructor
  · intro h -- Assume `x` is an integer
    by_cases hx : x ∈ (algebraMap ℚ ℚ⟮√-d⟯).range -- Case 1: `x` is rational
    · exact adjoin_mem₁ hx h -- Rational integer is in ℤ, hence in ℤ[√d]
    · -- Case 2: `x` is not rational. Use `x = (a + b√d) / c` representation.
      -- `c ∣ 2` and `c ^ 2 ∣ a ^ 2 - (b ^ 2) d`
      obtain ⟨c_div, hmin₀⟩ := minpoly_of_int' sqf one hx h
      obtain ⟨-, hc, hn⟩ := Q.calc_min_prop sqf one hx -- Get `a, b, c` properties
      have c_le := Nat.le_of_dvd Nat.zero_lt_two c_div -- `c ∣ 2` means `c = 1` or `c = 2`
      set c := (Q.calc_min sqf one hx).2.2
      match hmatch : c with
      | 0 => exact False.elim (hc rfl) -- `c ≠ 0`
      | 1 => exact adjoin_mem₃ sqf one hx hmatch -- If `c = 1, x = a + b√d ∈ ℤ[√d]`
      | 2 => -- If `c = 2`, we have `4 | a ^ 2 - (b ^ 2) d` and `gcd(a, b, 2) = 1`.
             -- This implies `d ≡ 1 [ZMOD 4]` by `congruent`.
        -- Contradicts assumption `¬(d ≡ 1 [ZMOD 4])`
        exact False.elim <| hd <| congruent sqf hmin₀ hn.1
  · exact adjoin_of_ring_of_int sqf one x -- Converse: elements of `ℤ[√d]` are integers

/-- The ring of integers `𝓞 ℚ(√d)` is ℤ-algebra isomorphic to `ℤ[√d]`
when `¬ (d ≡ 1 [ZMOD 4])`. -/
noncomputable def ring_of_int' : 𝓞 ℚ⟮√-d⟯ ≃ₐ[ℤ] Algebra.adjoin ℤ {√-d} where
  toFun x := ⟨x, (ring_of_int sqf one hd x).1 x.2⟩ -- Map integer `x` to itself in ℤ[√d]
  invFun y := ⟨⟨y.1, adjoin_mem₄ sqf one y⟩, -- Map `y ∈ ℤ[√d]` to `⟨y.1, _⟩` in `𝓞 ℚ(√d)`
    (ring_of_int sqf one hd ⟨y.1, adjoin_mem₄ sqf one y⟩).2 y.2⟩ -- Proof it's an integer
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- An integral basis for `𝓞 ℚ(√d)` obtained by mapping the basis `{1, √d}` of `ℤ[√d]`. -/
noncomputable abbrev intbase :=
  PowerBasis.map zbase (ring_of_int' sqf one hd).symm

/-- The discriminant of `ℚ(√d)` is `4d` when `¬ (d ≡ 1 [ZMOD 4])`. -/
theorem final : NumberField.discr ℚ⟮√-d⟯ = 4 * d := by
  -- Discriminant is invariant under isomorphism, use the basis for ℤ[√d].
  -- Use basis mapped from `zbase`
  rw [← discr_eq_discr ℚ⟮√-d⟯ (intbase sqf one hd).basis, intbase]
  simp only [map_dim, map_basis] -- Properties of `PowerBasis.map`
  have : (basis zbase).map (ring_of_int' sqf one hd).symm.toLinearEquiv =
    (ring_of_int' sqf one hd).symm ∘ (basis zbase) := by
    funext x
    simp only [Algebra.adjoin.powerBasis'_dim, Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Function.comp_apply]
  rw [this, ← Algebra.discr_eq_discr_of_algEquiv (basis zbase) (ring_of_int' sqf one hd).symm] -- Discr invariant under `AlgEquiv`
  exact discr_z sqf one -- Use the calculated discriminant for `zbase`

end Z₁

namespace Z₂ -- Case 2: `d ≡ 1 [ZMOD 4]`

variable (hd : d ≡ 1 [ZMOD 4])

variable (d) in
/-- Define `k = (d - 1) / 4`, which is an integer since `d ≡ 1 [ZMOD 4]`. -/
noncomputable def k : ℤ := (d - 1) / 4

variable (d) in
/-- The polynomial `X ^ 2 - X - k` over ℤ. -/
noncomputable abbrev polyz : ℤ[X] := X ^ 2 - C 1 * X - C (k d)

/-- Degree of `polyz` is 2. -/
theorem polyz_natDegree : (polyz d).natDegree = 2 := by
  unfold polyz; compute_degree!

/-- `polyz` is monic. -/
theorem polyz_Monic : (polyz d).Monic := by
  unfold polyz; monicity!

-- The generator for this case
local notation "γ" => (1 + √-d) / 2

include hd in
/-- Property defining `k`: `4k = d - 1`. -/
theorem hk : 4 * (k d) = d - 1 := by
  have := Int.ModEq.sub hd (show 1 ≡ 1 [ZMOD 4] by rfl)
  rw [sub_self, Int.modEq_zero_iff_dvd] at this
  exact Int.mul_ediv_cancel_of_dvd this

include hd in
/-- `γ` is a root of `polyz`. -/
theorem eval_zero : eval₂ (algebraMap ℤ ℂ) γ (polyz d) = 0 := by
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_one, one_mul, eval₂_sub, eval₂_X_pow,
    eval₂_X] -- Evaluate `polyz` at `γ`
  conv =>
    enter [1, 2]
    change eval₂ (algebraMap ℤ ℂ) γ (C (k d)) -- Target constant term eval
    rw [eval₂_C, algebraMap_int_eq, eq_intCast] -- Evaluate `C k`
  ring_nf -- Simplify `γ ^ 2 - γ - k`
  simp only [one_div, Complex.cpow_ofNat_inv_pow] -- `√d ^ 2 = d`
  have : (-1 / 4 + ((d : ℂ) * 4⁻¹ - (k d))) * 4 = 0 := by -- Calculation check in ℂ
    rw [add_mul, div_mul, div_self (OfNat.zero_ne_ofNat 4).symm, div_one,
      sub_mul, mul_assoc] -- Distribute (· * 4)
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, mul_one] -- Simplify 4 * 1 / 4 = 1
    norm_cast -- Cast to ℤ
    rw [mul_comm _ 4, hk hd, sub_sub_cancel]; rfl -- Use `4k = d - 1`
  exact (mul_eq_zero_iff_right (OfNat.zero_ne_ofNat 4).symm).1 this -- Result is zero

/-- The element `√d` is contained in `ℤ[γ]`. Specifically, `√d = 2γ - 1`. -/
private theorem adjoin_mem₄ : (AdjoinSimple.gen ℚ (√-d)).1 ∈ Algebra.adjoin ℤ {γ} := by
  suffices (AdjoinSimple.gen ℚ (√-d)).1 = 2 * γ - 1 from by -- Check relation
    rw [this]
    -- `2γ - 1 ∈ ℤ[γ]` because `2 ∈ ℤ, γ ∈ ℤ[γ], 1 ∈ ℤ`.
    refine sub_mem (mul_mem adjoin_mem₀ <| Algebra.self_mem_adjoin_singleton ℤ _) ?_
    convert @adjoin_mem₀ 1 γ -- Check `1 ∈ ℤ[γ]`
    exact Int.cast_one.symm
  -- Verify `√d = 2 * (1 + √d) / 2 - 1`
  rw [AdjoinSimple.coe_gen, one_div, mul_div_cancel₀ _ (NeZero.ne' 2).symm,
    add_sub_cancel_left]

/-- If `a, b` are odd, then `(a + b√d) / 2` is in `ℤ[γ]`. -/
private theorem adjoin_mem₅ {a b : ℤ} (hodd : Odd a ∧ Odd b) :
    (a + b * (AdjoinSimple.gen ℚ (√-d)).1) / 2 ∈ Algebra.adjoin ℤ {γ} := by
  -- Write `a = 2k₁ + 1, b = 2k₂ + 1`
  obtain ⟨⟨k₁, ka⟩, ⟨k₂, kb⟩⟩ := hodd
  rw [ka, kb] -- Substitute
  conv =>
    enter [2] -- Target the expression
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, AdjoinSimple.coe_gen,
      add_div]
    rw [← mul_div, mul_div_cancel₀ _ (NeZero.ne' 2).symm, add_mul, add_div, one_mul,
      mul_assoc, ← mul_div, mul_div_cancel₀ _ (NeZero.ne' 2).symm, ← add_assoc, add_comm,
      ← add_assoc, ← add_assoc, add_comm _ (1 / 2), ← add_assoc, ← add_div]
    -- This leads to `(k₁ - k₂) + (2k₂ + 1) * γ`, which is in `ℤ[γ]`
  exact add_mem (add_mem (Algebra.self_mem_adjoin_singleton ℤ _) adjoin_mem₀)
    <| mul_mem adjoin_mem₀ adjoin_mem₄ -- Check membership using closure properties

variable (d) in
/-- `polyz` mapped to ℚ[X]. -/
noncomputable abbrev polyq := Polynomial.map (algebraMap ℤ ℚ) (polyz d)

/-- Degree of `polyq` is 2. -/
private theorem polyq_natDegree : (polyq d).natDegree = 2 := by
  unfold polyq
  simp only [algebraMap_int_eq, Polynomial.map_sub, eq_intCast, Int.cast_one, one_mul,
    Polynomial.map_pow, map_X, Polynomial.map_intCast] -- Map coefficients
  compute_degree!

include hd

/-- `γ` is integral over ℤ, witnessed by `polyz`. -/
theorem integralz : IsIntegral ℤ γ := ⟨polyz d, ⟨polyz_Monic, eval_zero hd⟩⟩

-- Power basis `{1, γ}` for ℤ[γ] over ℤ
local notation3 "zbase" => Algebra.adjoin.powerBasis' (integralz hd)

/-- `ℤ[γ]` is a free ℤ-module. -/
theorem free_mod : Module.Free ℤ (Algebra.adjoin ℤ {γ}) := ⟨⟨Fin (dim zbase), basis zbase⟩⟩

/-- The degree of the minimal polynomial of `γ` over `ℤ` is at most 2. -/
private theorem min_polyz_natDegree_le : (minpoly ℤ γ).natDegree ≤ 2 := by
  rw [← polyz_natDegree] -- Use `polyz` degree
  exact natDegree_le_of_dvd -- minpoly divides `polyz`
    -- `γ` is root of `polyz`
    (minpoly.isIntegrallyClosed_dvd (integralz hd) <| eval_zero hd)
      -- `polyz` is non-zero
      <| Monic.ne_zero_of_ne Int.zero_ne_one <| polyz_Monic

/-- The generator `γ` as an element of the ℤ-algebra `ℤ[γ]`. -/
noncomputable abbrev δ : Algebra.adjoin ℤ {γ} :=
  ⟨γ, SetLike.mem_coe.1 <| Algebra.subset_adjoin <| Set.mem_singleton γ⟩

/-- Relation satisfied by `δ = γ`: `δ ^ 2 = k + δ`. -/
private theorem break_sq :
    ((@δ d) ^ 2) = (k d) * 1 + 1 * (@δ d) := by
  apply Subtype.val_inj.1 -- Work with underlying complex numbers `γ`
  simp only [SubmonoidClass.mk_pow, mul_one, one_mul, AddMemClass.coe_add,
    SubringClass.coe_intCast] -- Map to ℂ
  -- `γ ^ 2 = (1 + √d) ^ 2 / 4`
  have : ((1 + (d : ℂ) ^ (1 / 2 : ℂ)) / 2) ^ 2 = ((1 + (d : ℂ) ^ (1 / 2 : ℂ)) ^ 2) / 4 := by
    rw [div_pow]; congr; norm_cast
  rw [this]
  refine mul_right_cancel₀ (b := 4) (OfNat.zero_ne_ofNat 4).symm ?_
  rw [div_mul_cancel₀ _ (OfNat.zero_ne_ofNat 4).symm, add_mul]
  norm_cast -- Cast `↑(k hd) * 4` to `↑(k hd * 4)` where possible
  rw [mul_comm (k d) _, hk hd, show (4 : ℂ) = (2 : ℂ) * 2 by norm_cast, ← mul_assoc,
    div_mul_cancel₀ _ (NeZero.ne' 2).symm, add_mul, one_mul, sq, add_mul, one_mul, mul_add,
    mul_one, ← sq]
  simp only [one_div, Complex.cpow_ofNat_inv_pow, Int.cast_sub, Int.cast_one]; group

/-- Relation `δ ^ 3 = k + (1 + k) δ`. -/
private theorem break_trip : (@δ d) * (@δ d) * (@δ d) = (k d) + (1 + (k d)) * (@δ d) := by
  -- `δ ^ 3 = δ * δ ^ 2 = δ (k + δ) = k δ + δ ^ 2 = k δ + k + δ = k + (k + 1) δ`
  rw [← sq, break_sq hd, mul_one, one_mul, add_mul, ← sq, break_sq hd]; group

include sqf one

/-- For `d ≡ 1 [ZMOD 4]`, `a ^ 2 - a - k ≠ 0` for any rational `a`.
This implies `γ` is not rational. -/
private theorem rat_sq_sub_ne_zero (a : ℚ) : a ^ 2 - a - (k d) ≠ 0 := by
  by_contra! h -- Assume `a ^ 2 - a - k = 0`
  apply_fun (· * 4) at h -- Multiply by 4
  rw [sub_mul, zero_mul] at h
  norm_cast at h
  rw [mul_comm (k d) 4, hk hd, sub_eq_zero] at h -- `4a ^ 2 - 4a = 4k = d - 1`
  apply_fun (· + 1) at h -- Add 1 to both sides
  rw [Int.cast_sub, Int.cast_one, sub_add_cancel, sub_mul] at h -- `4a ^ 2 - 4a + 1 = d`
  have eq_sq : a ^ 2 * 4 - a * 4 + 1 = (2 * a - 1) ^ 2 := by -- Recognize LHS as a square
    rw [sq, sq, sub_mul, mul_sub, one_mul, mul_one, sub_sub, ← add_sub_assoc,
      sub_sub_eq_add_sub, ← mul_two, mul_comm 2 a, ← mul_assoc, mul_comm (a * 2) a,
      ← mul_assoc, add_sub_right_comm, mul_assoc _ _ 2, mul_assoc _ _ 2]
    norm_cast
  rw [eq_sq, ← sub_eq_zero] at h -- `(2a - 1) ^ 2 - d = 0`
  -- This contradicts `rat_sq_sub_ne_zero` from the `Q` namespace with input `2a - 1`.
  exact (Q.rat_sq_sub_ne_zero sqf one (2 * a - 1)) h

/-- `polyz = X ^ 2 - X - k` is irreducible over ℤ. -/
private theorem polyz_irr : Irreducible (polyz d) := by
  -- Use Gauss's lemma
  refine Monic.irreducible_of_irreducible_map (algebraMap ℤ ℚ)
    (polyz d) polyz_Monic <|
    -- Check irreducibility of `polyq = X ^ 2 - X - k` over ℚ
    (irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 ?_
  <;> (try rw [polyq_natDegree]); (try omega) -- Degree is 2
  · refine Multiset.eq_zero_iff_forall_not_mem.2 (fun a ↦ ?_) -- Show no roots in ℚ
    by_contra! -- Assume `a` is a root
    simp only [algebraMap_int_eq, Polynomial.map_sub, eq_intCast, Int.cast_one, one_mul,
      Polynomial.map_pow, map_X, Polynomial.map_intCast, mem_roots', ne_eq, IsRoot.def,
      eval_sub, eval_pow, eval_X, eval_intCast] at this
    -- If `a` is a root, then `a ^ 2 - a - k = 0`
    exact (rat_sq_sub_ne_zero sqf one hd a) this.2 -- Contradicts previous lemma

/-- The degree of the minimal polynomial of `γ` over `ℤ` is exactly 2. -/
private theorem min_polyz_natDegree : (minpoly ℤ γ).natDegree = 2 := by
  refine le_antisymm (min_polyz_natDegree_le hd) ?_ -- Know ≤ 2, need ≥ 2
  -- Need to show `γ` is not in ℤ (or even ℚ).
  rw [minpoly.two_le_natDegree_iff (integralz hd)]
  rintro ⟨x, hx : x = γ⟩ -- Assume `γ` is rational, `γ = x ∈ ℚ`
  -- If `γ = x`, then `2x = 1 + √d`, so `2x - 1 = √d`
  apply_fun (· * 2) at hx
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hx -- `2γ = 1 + √d`
  apply_fun ((-1 + ·) ^ 2) at hx -- Square `(2γ - 1)`
  -- `(2γ - 1) ^ 2 = √d ^ 2 = d`
  simp only [Pi.pow_apply, one_div, neg_add_cancel_left, Complex.cpow_ofNat_inv_pow] at hx
  rw [← sub_eq_zero] at hx -- `(2γ - 1) ^ 2 - d = 0`
  replace hx : (-1 + (x : ℚ) * 2) ^ 2 - (d : ℚ) = 0 := by
    norm_cast; norm_cast at hx
  -- This contradicts `Q.rat_sq_sub_ne_zero`.
  exact Q.rat_sq_sub_ne_zero sqf one (-1 + (x : ℚ) * 2) hx

/-- The dimension of the power basis `zbase` (for ℤ[γ] over ℤ) is 2. -/
private theorem base_dim : 2 = dim zbase := by
  rwa [Algebra.adjoin.powerBasis'_dim, min_polyz_natDegree sqf one] -- Dim = degree of minpoly

/-- The second element of the power basis `zbase` is the generator `δ = γ`. -/
private theorem base_equiv_one : adj (base_dim sqf one hd) = δ := by
  have : finCongr (base_dim sqf one hd) 1 =
    ⟨1, by rw [← base_dim sqf one hd]; omega⟩ := rfl
  rw [adj, this, basis_eq_pow zbase _] -- Def of `adj` and basis element
  simp only [adjoin.powerBasis_gen, pow_one] -- `gen ^ 1 = gen`
  -- Generator of basis is the element itself
  exact Algebra.adjoin.powerBasis'_gen <| integralz hd

/-- Any element `α` in `ℤ[γ]` can be written as `r + s * γ` with `r, s ∈ ℤ`. -/
private theorem int_linear_comb (α : Algebra.adjoin ℤ {γ}) :
    ∃ r s : ℤ, α = r + s * (@δ d) := by
  -- Apply general quadratic representation over ℤ
  have := quadratic.repr (base_dim sqf one hd) α
  rw [base_equiv_one sqf one] at this -- Substitute the generator
  -- Simplify AlgebraMap and smul
  simp only [algebraMap_int_eq, eq_intCast, SetLike.mk_smul_mk, one_div, zsmul_eq_mul] at this
  convert this -- Check result matches
  simp only [MulMemClass.coe_mul, SubringClass.coe_intCast, one_div]
  exact hd

/-- Elements of `ℤ[γ]` (viewed as complex numbers) are contained in `ℚ(√d)`. -/
private theorem adjoin_mem₆ (α : Algebra.adjoin ℤ {γ}) : α.1 ∈ ℚ⟮√-d⟯ := by
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one hd α -- Get `r, s ∈ ℤ` representation
  rw [hrs]
  -- `γ = (1 + √d) / 2`. `1 ∈ ℚ(√d), √d ∈ ℚ(√d), 2 ∈ ℚ`. So `γ ∈ ℚ(√d)`.
  exact add_mem adjoin_mem₂ <| mul_mem adjoin_mem₂ <|
    div_mem (add_mem (IntermediateField.one_mem _)
      (mem_adjoin_simple_self ℚ _)) adjoin_mem₂

/-- `γ` viewed as an element of `ℚ(√d)`. -/
noncomputable abbrev δ' : ℚ⟮√-d⟯ := by
  -- Check `γ ∈ ℚ(√d)`
  refine ⟨γ, div_mem (add_mem ?_ (mem_adjoin_simple_self ℚ _)) adjoin_mem₂⟩
  convert (@adjoin_mem₂ 1 √-d) -- Check `1 ∈ ℚ(√d)`
  exact Rat.cast_one.symm

/-- Elements of `ℤ[γ]` are algebraic integers in `ℚ(√d)`. -/
private theorem adjoin_of_ring_of_int (x : ℚ⟮√-d⟯) (h : x.1 ∈ Algebra.adjoin ℤ {γ}) :
    x ∈ (integralClosure ℤ ℚ⟮√-d⟯) := by
  -- Represent `x = r + sδ` (`δ = γ` here)
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one hd ⟨x, h⟩
  have : x = r + s * (@δ' d) := -- Match types
    Subtype.val_inj.1 (by apply Subtype.val_inj.2 hrs)
  rw [this]
  -- `r, s` are integral. `δ' = γ` is integral (`integralz hd`).
  -- Closure is a ring, so `r + sδ'` is integral.
  refine add_mem isIntegral_algebraMap (mul_mem isIntegral_algebraMap ?_)
  -- Check if `δ'` is integral
  rw [mem_integralClosure_iff, ← isIntegral_algebraMap_iff (@algMap_inj d)]
  exact (integralz hd)

-- Calculate entries of the trace matrix for the basis `{1, γ}`
/-- `Trace(1 * 1) = Trace(1) = 2`. -/
private theorem traceForm_11 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) 1 1 = 2 := by
  rwa [Algebra.traceForm_apply, one_mul, ← @algebraMap.coe_one ℤ (Algebra.adjoin ℤ {γ}) ..,
    @Algebra.trace_algebraMap ℤ (Algebra.adjoin ℤ {γ}) _ _ _ _ (free_mod hd) 1,
    finrank zbase, ← base_dim sqf one, nsmul_eq_mul, Nat.cast_ofNat, mul_one]

/-- Helper: The coefficient of `γ` in the representation of `k` is 0.
(`k = k * 1 + 0 * γ`). -/
private theorem aux_traceForm_1δ :
    ((basis zbase).repr (k d)) (finCongr (base_dim sqf one hd) 1) = 0 := by
  have cast : @Int.cast (Algebra.adjoin ℤ {γ}) AddGroupWithOne.toIntCast (k d) =
    ((algebraMap ℤ (Algebra.adjoin ℤ {γ})) (k d)) * 1 := by -- `k = k * 1`
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  have neq : finCongr (base_dim sqf one hd) 0 ≠
    finCongr (base_dim sqf one hd) 1 := ne_of_beq_false rfl
  replace this := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one hd) 0) -- Basis element 1
    (finCongr (base_dim sqf one hd) 1) -- Index 1
  rw [ite_cond_eq_false _ _ (eq_false neq)] at this -- `(repr 1)₁ = 0`
  -- `(repr k)₁ = k * (repr 1)₁ = 0`
  rw [cast, Basis.repr_smul', ← base_equiv_zero (base_dim sqf one hd), this, mul_zero]

/-- Helper: The coefficient of `γ` in the representation of `γ ^ 2` is 1.
(`γ ^ 2 = k * 1 + 1 * γ`). -/
private theorem aux_traceForm_1δ' :
    ((basis zbase).repr (δ * δ)) (finCongr (base_dim sqf one hd) 1) = 1 := by
  rw [← sq, break_sq hd] -- `γ ^ 2 = k * 1 + 1 * γ`
  simp only [mul_one, one_mul, map_add, Fin.isValue, Finsupp.coe_add, Pi.add_apply]
  -- Need `(repr k)₁ + (repr γ)₁`
  have neq : finCongr (base_dim sqf one hd) 0 ≠
    finCongr (base_dim sqf one hd) 1 := ne_of_beq_false rfl
  replace this := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one hd) 1) -- Basis element `γ`
    (finCongr (base_dim sqf one hd) 1) -- Index 1
  -- `(repr γ)₁ = 1`
  rw [ite_cond_eq_true _ _ (eq_self (finCongr (base_dim sqf one hd) 1))] at this
  -- `(repr k)₁ = 0`. Result `0 + 1 = 1`.
  rw [← base_equiv_one sqf one hd, adj, this, aux_traceForm_1δ sqf one hd, zero_add]

/-- Helper: The coefficient of 1 in the representation of `γ` is 0.
(`γ = 0 * 1 + 1 * γ`). -/
private theorem aux_traceForm_1δ'' :
    ((basis zbase).repr δ) (finCongr (base_dim sqf one hd) 0) = 0 := by
  have neq : finCongr (base_dim sqf one hd) 0 ≠
      finCongr (base_dim sqf one hd) 1 := ne_of_beq_false rfl
  have := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one hd) 1) -- Basis element `γ`
    (finCongr (base_dim sqf one hd) 0) -- Index 0
  rw [ite_cond_eq_false _ _ (eq_false neq.symm)] at this -- `(repr γ)₀ = 0`
  rw [← base_equiv_one sqf one hd, adj, this]

/-- `Trace(1 * γ) = Trace(γ) = 1`. -/
private theorem traceForm_1δ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) 1 δ = 1 := by
  rw [Algebra.traceForm_apply, one_mul, Algebra.trace_eq_matrix_trace (basis zbase)
    δ, Matrix.trace, finChange (base_dim sqf one hd)] -- Use matrix trace
  -- Sum diagonal
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  -- Suppose matrix of left multiplication by `γ` in basis `{1, γ}` is M
  -- Need `M₀₀` and `M₁₁`
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one hd), mul_one]
  -- `M₀₀ = (repr γ)₀`, `M₁₁ = (repr (γ * γ))₁`
  rw [aux_traceForm_1δ'' sqf one hd, zero_add, ← adj, base_equiv_one sqf one hd]
  -- Trace = `M₀₀ + M₁₁ = 0 + 1 = 1`
  exact aux_traceForm_1δ' sqf one hd

/-- `Trace(γ * 1) = Trace(γ) = 1`. -/
private theorem traceForm_δ1 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) δ 1 = 1 := by
  -- via symmetric
  simpa only [Algebra.traceForm_apply, mul_one, one_mul] using traceForm_1δ sqf one hd

/-- Helper: The coefficient of 1 in the representation of `γ ^ 2` is `k`.
(`γ ^ 2 = k * 1 + 1 * γ`). -/
private theorem aux_traceForm_δδ :
    ((basis zbase).repr (δ * δ)) (finCongr (base_dim sqf one hd) 0) = (k d) := by
  rw [← sq, break_sq hd]
  simp only [mul_one, one_mul, map_add, Fin.isValue, Finsupp.coe_add, Pi.add_apply]
  -- Need `(repr k)₀ + (repr γ)₀`
  have cast : @Int.cast (Algebra.adjoin ℤ {γ}) AddGroupWithOne.toIntCast (k d) =
    ((algebraMap ℤ (Algebra.adjoin ℤ {γ})) (k d)) * 1 := by -- `k = k * 1`
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  replace this := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one hd) 0) -- Basis element 1
    (finCongr (base_dim sqf one hd) 0) -- Index 0
  -- `(repr 1)₀ = 1`
  rw [ite_cond_eq_true _ _ (eq_self (finCongr (base_dim sqf one hd) 0))] at this
  rw [aux_traceForm_1δ'' sqf one hd, cast, Basis.repr_smul',
    ← base_equiv_zero (base_dim sqf one hd), this, mul_one, add_zero]

/-- `Trace(γ * γ) = Trace(γ ^ 2) = Trace(k + γ) = Trace(k) + Trace(γ) = 2k + 1`. -/
private theorem traceForm_δδ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) δ δ = 1 + 2 * (k d) := by
  rw [Algebra.traceForm_apply, Algebra.trace_eq_matrix_trace (basis zbase)
    _, Matrix.trace, finChange (base_dim sqf one hd)]
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one hd), mul_one, aux_traceForm_δδ sqf one hd,
    ← adj, base_equiv_one sqf one hd, break_trip hd]
  simp only [map_add, Fin.isValue, Finsupp.coe_add, Pi.add_apply]
  rw [aux_traceForm_1δ sqf one hd, zero_add, ← base_equiv_one sqf one hd, adj]
  replace cast : @OfNat.ofNat (Algebra.adjoin ℤ {γ}) 1 One.toOfNat1 +
    @Int.cast (Algebra.adjoin ℤ {γ}) AddGroupWithOne.toIntCast (k d) =
    ((algebraMap ℤ (Algebra.adjoin ℤ {γ})) (1 + (k d))) := by
      rw [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_one]
  have := Basis.repr_self_apply (basis zbase)
    (finCongr (base_dim sqf one hd) 1) -- Basis element `γ`
    (finCongr (base_dim sqf one hd) 1) -- Index 1
  -- `(repr γ)₁ = 1`
  rw [ite_cond_eq_true _ _ (eq_self (finCongr (base_dim sqf one hd) 1))] at this
  -- `(repr (1+k) * γ)₁ = (1 + k) * (repr γ)₁ = 1 + k`
  rw [cast, Basis.repr_smul', this, mul_one, add_comm, add_assoc, Int.two_mul (k d)]

variable (d) in
/-- The trace matrix for the basis `{1, γ}` is `[[2, 1], [1, 1 + 2k]]`. -/
noncomputable def traceMat : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1 + 2 * (k d)]

/-- The trace matrix calculated using `Algebra.traceMatrix` matches `traceMat`. -/
private theorem mat_conv :
  (Matrix.reindexAlgEquiv ℤ ℤ (finCongr (base_dim sqf one hd)).symm)
    (Algebra.traceMatrix ℤ (basis zbase)) = traceMat d := Matrix.ext fun i j ↦ by
  fin_cases i <;> fin_cases j -- Check all 4 entries
  all_goals simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one hd)]
    exact traceForm_11 sqf one hd
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one hd), ← adj,
      base_equiv_one sqf one hd]
    exact traceForm_1δ sqf one hd
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one hd), ← adj,
      base_equiv_one sqf one hd]
    exact traceForm_δ1 sqf one hd
  · rw [Algebra.traceMatrix, Matrix.of_apply, ← adj, base_equiv_one sqf one hd]
    exact traceForm_δδ sqf one hd

/-- The discriminant of the ℤ-basis `{1, γ}` is
`det(traceMatrix) = 2(1 + 2k) - 1 * 1 = 2 + 4k - 1 = 1 + 4k = d`. -/
private theorem discr_z : Algebra.discr ℤ (basis zbase) = d := by
  have := Matrix.det_reindexAlgEquiv ℤ ℤ (finCongr (base_dim sqf one hd)).symm
    (Algebra.traceMatrix ℤ (basis zbase)) -- Det is invariant under reindexing
  rw [Algebra.discr_def, ← this, mat_conv sqf one hd, traceMat, Matrix.det_fin_two_of,
    mul_add, mul_one, mul_one, ← mul_assoc, show (2 : ℤ) * 2 = 4 by rfl, hk hd]; group

/-- The ring of integers of `ℚ(√d)` is `ℤ[γ]` = `ℤ[(1 + √d) / 2]` when `d ≡ 1 [ZMOD 4]`. -/
theorem ring_of_int (x : ℚ⟮√-d⟯) : x ∈ (integralClosure ℤ ℚ⟮√-d⟯) ↔
  x.1 ∈ Algebra.adjoin ℤ {γ} := by
  constructor
  · intro h -- Assume `x` is an integer
    by_cases hx : x ∈ (algebraMap ℚ ℚ⟮√-d⟯).range -- Case 1: `x` is rational
    · exact adjoin_mem₁ hx h -- Rational integer is in `ℤ ⊂ ℤ[γ]`
    · -- Case 2: `x` is not rational. Use `x = (a + b√d) / c` representation.
      -- `c ∣ 2 and c ^ 2 ∣ a ^ 2 - (b ^ 2) d`
      obtain ⟨c_div, hdvd⟩ := minpoly_of_int' sqf one hx h
      obtain ⟨hm, hc, ⟨hn₁, hn₂⟩⟩ := Q.calc_min_prop sqf one hx -- Get `a, b, c` properties
      have c_le := Nat.le_of_dvd Nat.zero_lt_two c_div -- `c = 1` or `c = 2`
      set c := (Q.calc_min sqf one hx).2.2
      match hmatch : c with
      | 0 => exact False.elim (hc rfl) -- `c ≠ 0`
      | 1 => -- If `c = 1, x = a + b√d`. Need `a + b√d ∈ ℤ[γ]`.
             -- Since `√d = 2γ - 1, a + b√d = a + b(2γ - 1) = (a - b) + 2bγ ∈ ℤ[γ]`.
        simp only [Nat.cast_one, Rat.cast_one, div_one] at hn₂
        rw [hn₂]
        -- `a ∈ ℤ[γ], b ∈ ℤ[γ], √d ∈ ℤ[γ]`
        exact add_mem adjoin_mem₀ <| mul_mem adjoin_mem₀ adjoin_mem₄
      | 2 => -- If `c = 2, x = (a + b√d) / 2`.
             -- We have `4 ∣ a ^ 2 - (b ^ 2) d` and `gcd(a, b, 2) = 1`.
             -- By `aux_congruent`, `a` and `b` must be odd.
             -- By `adjoin_mem₅`, if `a, b` odd, then `(a + b√d) / 2 ∈ ℤ[γ]`.
        rw [hn₂]
        exact adjoin_mem₅ <| aux_congruent sqf hdvd hn₁
  · exact adjoin_of_ring_of_int sqf one hd x -- Converse: elements of ℤ[γ] are integers

/-- The ring of integers `𝓞 ℚ(√d)` is ℤ-algebra isomorphic to `ℤ[γ]` when `d ≡ 1 [ZMOD 4]`. -/
noncomputable def ring_of_int' : 𝓞 ℚ⟮√-d⟯ ≃ₐ[ℤ] Algebra.adjoin ℤ {γ} where
  toFun x := ⟨x, (ring_of_int sqf one hd x).1 x.2⟩ -- Map integer `x` to itself in ℤ[γ]
  invFun y := ⟨⟨y.1, adjoin_mem₆ sqf one hd y⟩, -- Map `y ∈ ℤ[γ]` to `⟨y.1, _⟩` in `𝓞 ℚ(√d)`
    (ring_of_int sqf one hd ⟨y.1, adjoin_mem₆ sqf one hd y⟩).2 y.2⟩ -- Proof it's an integer
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- An integral basis for `𝓞 ℚ(√d)` obtained by mapping the basis `{1, γ}` of `ℤ[γ]`. -/
noncomputable abbrev intbase :=
  PowerBasis.map zbase (ring_of_int' sqf one hd).symm

/-- The discriminant of `ℚ(√d)` is `d` when `d ≡ 1 [ZMOD 4]`. -/
theorem final : NumberField.discr ℚ⟮√-d⟯ = d := by
  -- Discriminant is invariant under isomorphism, use the basis for ℤ[γ].
  rw [← discr_eq_discr ℚ⟮√-d⟯ (intbase sqf one hd).basis, intbase]
  simp only [map_dim, map_basis] -- Properties of `PowerBasis.map`
  have : (basis zbase).map (ring_of_int' sqf one hd).symm.toLinearEquiv =
    (ring_of_int' sqf one hd).symm ∘ (basis zbase) := by -- How map interacts with basis
    funext x
    simp only [Algebra.adjoin.powerBasis'_dim, Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Function.comp_apply]
  rw [this, ← Algebra.discr_eq_discr_of_algEquiv (basis zbase) (ring_of_int' sqf one hd).symm] -- Discr invariant under `AlgEquiv`
  exact discr_z sqf one hd -- Use the calculated discriminant for `zbase`

end Z₂

end nontrivial

include sqf in
/-- The discriminant of the quadratic field `ℚ(√d)` for square-free `d`.
- If `d ≡ 1 [ZMOD 4]`, the discriminant is `d`.
- If `¬ d ≡ 1 [ZMOD 4]`, the discriminant is `4d`. -/
theorem quadratic_discr :
    (  d ≡ 1 [ZMOD 4] → NumberField.discr ℚ⟮√-d⟯ = d) ∧
    (¬ d ≡ 1 [ZMOD 4] → NumberField.discr ℚ⟮√-d⟯ = 4 * d) := by
  by_cases one : d ≠ 1 -- The previous proofs assumed `d ≠ 1`.
  · -- Case `d ≠ 1`: Apply results from `Z₁` and `Z₂`.
    exact ⟨Z₂.final sqf one, Z₁.final sqf one⟩
  · -- Case `d = 1`: `ℚ(√1) = ℚ(1) = ℚ`.
    simp only [ne_eq, Decidable.not_not] at one
    constructor
    · -- If `d ≡ 1 [ZMOD 4]` (which 1 is), then `discr = d = 1`.
      intro hcong
      rw [one, ← discr_rat] -- `discr ℚ = 1`
      -- Show `ℚ(√1) = ℚ`
      refine discr_eq_discr_of_algEquiv _ ?_
      rw [discr_rat]
      -- `ℚ(√1) = ℚ(1) = ℚ = ⊥` (as subfield of ℂ)
      have : ℚ⟮((1 : ℤ) ^ (1 / 2 : ℂ) : ℂ)⟯ = ⊥ := by
        rw [← le_bot_iff, adjoin_le_iff]
        simp only [Int.cast_one, one_div, Complex.one_cpow, Set.singleton_subset_iff,
          SetLike.mem_coe]
        exact IntermediateField.one_mem _
      -- Use `equiv ℚ(√1) = ⊥` and `⊥ = ℚ`
      exact (equivOfEq this).trans (botEquiv ℚ ℂ)
    · -- If `¬(d ≡ 1 [ZMOD 4])` (which is false for `d = 1`), the implication is true.
      intro hcong
      rw [one] at hcong; tauto -- `1 ≡ 1 [ZMOD 4]`, so `¬(1 ≡ 1 [ZMOD 4])` is false.
