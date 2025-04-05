import Mathlib

open IntermediateField Polynomial PowerBasis NumberField

namespace finChange

variable {l : ℕ} {n : ℕ} (hl : l = n)

include hl in
def equi : Fin n ≃ Fin l := finCongr hl.symm

private theorem bi : Function.Bijective (equi hl).invFun :=
  Function.bijective_iff_has_inverse.2 ⟨(equi hl).toFun,
    ⟨(equi hl).right_inv, (equi hl).left_inv⟩⟩

theorem change {T : Type*} {f : Fin l → T} [AddCommMonoid T] :
  ∑ i : Fin l, f i = ∑ i : Fin n, f ((equi hl).toFun i) :=
    Function.Bijective.finset_sum (equi hl).invFun (bi hl) f
      (fun x ↦ f ((equi hl).toFun x)) (fun _ ↦ rfl)

end finChange

section quadratic

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
variable {base : PowerBasis R S} (hdim : dim base = 2)

include hdim

private theorem base_equiv_zero : (basis base) (finChange.equi hdim 0) = 1 := by
  have : (finChange.equi hdim 0) = ⟨0, by rw [hdim]; omega⟩ := rfl
  rw [this, basis_eq_pow base ⟨0, by rw [hdim]; omega⟩]
  simp only [adjoin.powerBasis_gen, pow_zero]

include base

noncomputable abbrev adj := (basis base) (finChange.equi hdim 1)

theorem quadratic.repr (α : S) :
    ∃ r s : R, α = (algebraMap R S) r + s • (adj hdim) := by
  have := Basis.sum_repr (PowerBasis.basis base) α
  rw [finChange.change hdim, Fin.sum_univ_two] at this
  have foo : ∀ r : R, r • (1 : S) = (algebraMap R S) r := fun r ↦
    (Algebra.algebraMap_eq_smul_one r).symm
  rw [show (finChange.equi hdim).toFun = finChange.equi hdim by rfl,
    base_equiv_zero hdim, foo] at this
  exact ⟨((basis base).repr α) (finChange.equi hdim 0),
    ((basis base).repr α) (finChange.equi hdim 1), this.symm⟩

end quadratic

variable {d : ℤ} (sqf : Squarefree d)

local notation: max "poly" => X ^ 2 - C (d : ℚ)
local notation: max "√-" i =>  ((i : ℂ) ^ ((1 / 2) : ℂ))
local notation: max "minpo(" a"," b"," c ")" =>
  X ^ 2 - C ((2 * a : ℚ) / (c : ℚ)) * X + C ((a ^ 2 - (b ^ 2) * d) / (c ^ 2 : ℚ))

theorem minpoly_break {a b c : ℚ} : Polynomial.map (algebraMap ℚ ℂ) minpo(a, b, c) =
    (X - C ((a + b * √-d) / c)) * (X - C ((a - b * √-d) / c)) := by
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_mul,
    map_C, map_div₀, eq_ratCast, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_intCast, one_div]
  rw [sub_mul, mul_sub, mul_sub, ← C_mul, mul_comm X (C _), sub_sub,
    ← add_sub_assoc, ← add_mul, ← C_add, ← sq, div_add_div_same]
  conv =>
    enter [2, 2, 1, 1]
    ring_nf
  conv =>
    enter [2, 2, 2, 2]
    ring_nf
    rw [inv_pow, one_div, Complex.cpow_ofNat_inv_pow, ← sub_mul]
  ring_nf

theorem algMap_inj : Function.Injective (algebraMap ℚ⟮√-d⟯ ℂ) :=
  FaithfulSMul.algebraMap_injective ℚ⟮√-d⟯ ℂ

section nontrivial

variable (one : d ≠ 1)

namespace Q

private theorem poly_natDegree : natDegree poly = 2 := natDegree_X_pow_sub_C
private theorem poly_Monic : Monic poly := by monicity!
private theorem integral : IsIntegral ℚ √-d := by
  refine isAlgebraic_iff_isIntegral.1 ⟨poly, Monic.ne_zero poly_Monic, ?_⟩
  simp only [one_div, map_intCast, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow,
    sub_self]

instance : Module.Finite ℚ ℚ⟮√-d⟯ := adjoin.finiteDimensional integral
instance : NumberField ℚ⟮√-d⟯ := NumberField.mk

local notation3 "base" => IntermediateField.adjoin.powerBasis integral (x := √-d)
local notation3 "δ" => AdjoinSimple.gen ℚ √-d

private theorem sqd_sq : δ ^ 2 = d := by
  apply SetLike.coe_eq_coe.1
  show (√-d) ^ 2 = d
  simp only [one_div, Complex.cpow_ofNat_inv_pow]

include one sqf

private theorem rat_sq_sub_ne_zero (a : ℚ) : a ^ 2 - d ≠ 0 := by
  by_contra!
  apply_fun (· + (d : ℚ)) at this
  rw [sub_add_cancel, zero_add, ← Rat.num_div_den a, div_pow] at this
  apply_fun (· * (a.den : ℚ) ^ 2) at this
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    Nat.cast_eq_zero, Rat.den_ne_zero, IsUnit.div_mul_cancel] at this
  norm_cast at this
  have dvd : a.num * a.num ∣ d * (a.den ^ 2) :=
    ⟨1, by rw [mul_one, ← pow_two]; exact this.symm⟩
  replace dvd : a.num.natAbs ∣ a.den ^ 2 := Int.ofNat_dvd_right.1 <|
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right sqf dvd
  rw [pow_two] at dvd
  replace dvd : a.num.natAbs = 1 := Nat.Coprime.eq_one_of_dvd (Rat.reduced a) <|
    Nat.Coprime.dvd_of_dvd_mul_left (Rat.reduced a) dvd
  rw [show a.num ^ 2 = a.num.natAbs ^ 2 by exact Int.natAbs_eq_iff_sq_eq.mp rfl,
    dvd, show @Nat.cast ℤ instNatCastInt 1 = 1 by rfl, one_pow] at this
  rw [Int.eq_one_of_mul_eq_one_left (Int.ofNat_zero_le (a.den ^ 2)) this.symm, mul_one] at this
  exact one this.symm

private theorem sqrt_d_not_mem : (√-d) ∉ (algebraMap ℚ ℂ).range := by
  rintro ⟨x, hx⟩
  absurd rat_sq_sub_ne_zero sqf one x
  apply_fun (· ^ 2) at hx
  simp only [eq_ratCast, one_div, Complex.cpow_ofNat_inv_pow] at hx
  norm_cast at hx
  rw [hx, sub_self]

private theorem poly_irr : Irreducible poly := by
  refine (irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 ?_
  <;> (try rw [poly_natDegree]); (try omega)
  · refine Multiset.eq_zero_iff_forall_not_mem.2 (fun a ↦ ?_)
    by_contra!
    simp only [mem_roots', ne_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at this
    exact (rat_sq_sub_ne_zero sqf one a) this.2

private theorem poly_min : minpoly ℚ (√-d) = poly := by
  refine (minpoly.eq_of_irreducible_of_monic (poly_irr sqf one) ?_ poly_Monic).symm
  simp only [one_div, map_intCast, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow,
    sub_self]

private theorem base_dim : dim base = 2 :=
  have : Module.finrank ℚ ℚ⟮√-d⟯ = 2 :=
    poly_natDegree ▸ poly_min sqf one ▸ IntermediateField.adjoin.finrank integral
  (this ▸ finrank base).symm

private theorem base_equiv_one : adj (base_dim sqf one) = δ := by
  have : (finChange.equi (base_dim sqf one) 1) =
    ⟨1, by rw [(base_dim sqf one)]; omega⟩ := rfl
  rw [adj, this, basis_eq_pow base ⟨1, by rw [(base_dim sqf one)]; omega⟩]
  simp only [adjoin.powerBasis_gen, pow_one]

private theorem linear_comb (α : ℚ⟮√-d⟯) : ∃ r s : ℚ, α = r + s * δ := by
  have := quadratic.repr (base_dim sqf one) α
  rwa [base_equiv_one sqf one] at this

private theorem int_linear_comb (α : ℚ⟮√-d⟯) :
    ∃ a b : ℤ, ∃ c : ℕ, α = (a + b * δ) / (c : ℚ) ∧ c ≠ 0 := by
  obtain ⟨r, s, hrs⟩ := linear_comb sqf one α
  rw [← Rat.num_div_den r, ← Rat.num_div_den s] at hrs
  have : α = (r.num * s.den + s.num * r.den * δ) / (r.den * s.den : ℚ) := by
    rw [hrs]
    field_simp
    exact mul_right_comm _ δ _
  refine ⟨r.num * s.den, s.num * r.den, r.den * s.den, ⟨?_, Nat.mul_ne_zero r.den_nz s.den_nz⟩⟩
  · convert this <;> norm_cast

private theorem repr (α : ℚ⟮√-d⟯) : ∃ a b : ℤ, ∃ c : ℕ,
    α = (a + b * δ) / (c : ℚ) ∧
    c ≠ 0 ∧
    ∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n := by
  obtain ⟨a, b, c, habc, hc_zero⟩ := int_linear_comb sqf one α
  set e := (a.gcd b : ℤ).gcd c with def_e
  obtain ⟨a', ha⟩ : (e : ℤ) ∣ a := by rw [def_e, Int.gcd_assoc]; exact Int.gcd_dvd_left
  obtain ⟨b', hb⟩ : (e : ℤ) ∣ b := by
    rw [def_e, Int.gcd_comm, ← Int.gcd_assoc]; exact Int.gcd_dvd_right
  obtain ⟨c', hc⟩ : (e : ℤ) ∣ c := by rw [def_e]; exact Int.gcd_dvd_right
  have c_pow : 0 < c' := by
    by_contra!
    have : e * c' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.ofNat_zero_le e) this
    rw [← hc] at this; omega
  obtain ⟨c'', hc''⟩ : ∃ c'' : ℕ, c'' = c' := CanLift.prf c' <| Int.le_of_lt c_pow
  have e_ne_zero : e ≠ 0 := fun foo ↦ by
    simp only [foo, CharP.cast_eq_zero, zero_mul, Nat.cast_eq_zero] at hc
    exact hc_zero hc
  refine ⟨a', b', c'', ⟨?_, ?_⟩⟩
  · have : (a' + b' * δ) / (c'' : ℚ) = e * (a' + b' * δ) / (e * (c'' : ℚ)) := by
      ring_nf
      rw [mul_assoc _ (e : ℚ⟮√-d⟯) _, mul_assoc _ (e : ℚ⟮√-d⟯) _,
        mul_inv_cancel₀ <| Nat.cast_ne_zero.mpr e_ne_zero, mul_one, mul_one]
    have foo : @Nat.cast ℚ Rat.instNatCast c'' = @Int.cast ℚ Rat.instIntCast c' :=
      Rat.ext hc'' rfl
    rw [this, mul_add, ← mul_assoc, foo]
    norm_cast
    rwa [← ha, ← hb, ← hc]
  · constructor
    · convert_to (c'' : ℤ) ≠ 0
      · exact Int.ofNat_eq_zero.symm
      · rw [hc'']; exact (Int.ne_of_lt c_pow).symm
    · intro n hn
      have : n ∣ (a.gcd b) := Int.dvd_gcd (ha.symm ▸ dvd_mul_of_dvd_right hn.1 e)
        <| hb.symm ▸ dvd_mul_of_dvd_right hn.2.1 e
      have bar := Int.gcd_eq_gcd_ab (a.gcd b) c
      rw [← def_e] at bar
      set l₁ := ((a.gcd b) : ℤ).gcdA c; set l₂ := ((a.gcd b) : ℤ).gcdB c
      rw [Int.gcd_eq_gcd_ab a b] at bar
      set l₃ := a.gcdA b; set l₄ := a.gcdB b
      rw [ha, hb, hc, add_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
        ← mul_add (e : ℤ) _, mul_assoc, ← mul_add (e : ℤ) _] at bar
      nth_rw 1 [← mul_one (e : ℤ)] at bar
      rw [Int.mul_eq_mul_left_iff (Int.ofNat_ne_zero.2 e_ne_zero)] at bar
      have := Int.dvd_add
        (Int.dvd_add (Dvd.dvd.mul_right hn.1 (l₃ * l₁)) (Dvd.dvd.mul_right hn.2.1 (l₄ * l₁)))
        (Dvd.dvd.mul_right hn.2.2 l₂)
      rw [hc'', ← bar] at this
      exact isUnit_of_dvd_one this

theorem minpoly_div (x : ℚ⟮√-d⟯) : ∃ a b : ℤ, ∃ c : ℕ,
    minpoly ℚ x ∣ minpo(a, b, c) ∧
    c ≠ 0 ∧
    (∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n) ∧
    x = (a + b * δ) / (c : ℚ) := by
  obtain ⟨a, b, c, ⟨hx, hc, hn⟩⟩ := repr sqf one x
  refine ⟨a, b, c, ⟨minpoly.dvd_iff.2 ?_, hc, hn, hx⟩⟩
  simp only [hx, Rat.cast_natCast, map_add, map_sub, map_pow, aeval_X, map_mul, aeval_C, map_div₀,
    eq_ratCast, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast, map_natCast, Rat.cast_sub,
    Rat.cast_pow]
  ring_nf; rw [sqd_sq]; ring

private theorem minpoly_of_not_mem {x : ℚ⟮√-d⟯} : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range →
  ∃ (r : Σ (_ : ℤ) (_ : ℤ), ℕ),
    minpoly ℚ x = minpo(r.1, r.2.1, r.2.2) ∧
    r.2.2 ≠ 0 ∧
    (∀ n : ℤ, n ∣ r.1 ∧ n ∣ r.2.1 ∧ n ∣ r.2.2 → IsUnit n) ∧
    x = (r.1 + r.2.1 * δ) / (r.2.2 : ℚ) := by
  obtain ⟨a, b, c, ⟨hmin, hc, ⟨hn, hx⟩⟩⟩ := minpoly_div sqf one x
  intro h
  refine ⟨⟨a, ⟨b, c⟩⟩, ⟨?_, hc, hn, hx⟩⟩
  rw [← minpoly.two_le_natDegree_iff (IsIntegral.of_finite ℚ x)] at h
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite ℚ x)) ?_ hmin ?_).symm
  · monicity!
  · compute_degree!

noncomputable def calc_min {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range) :
    Σ (_ : ℤ) (_ : ℤ), ℕ :=
  Classical.choose <| minpoly_of_not_mem sqf one hx

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

section aux

theorem minpoly_of_int (x : ℚ⟮√-d⟯) : x ∈ (integralClosure ℤ ℚ⟮√-d⟯) ↔
    minpoly ℚ x = Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ x) := by
  constructor
  · exact minpoly.isIntegrallyClosed_eq_field_fractions ℚ (ℚ⟮√-d⟯)
  · intro hx
    refine minpoly.ne_zero_iff.1 (fun hzero ↦ ?_)
    rw [hzero, algebraMap_int_eq, Polynomial.map_zero] at hx
    exact False.elim <| (minpoly.ne_zero_of_finite ℚ x) hx

private theorem aux_copri₀ {a b : ℤ} {c : ℕ}
  (hn : ∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n) :
    (c.gcd a.natAbs).Coprime b.natAbs := by
  by_contra not_copri
  simp only [ne_eq] at not_copri
  set w := (c.gcd a.natAbs).gcd b.natAbs with def_w
  have dvd₁ : w ∣ a.natAbs := by
    rw [def_w, Nat.gcd_comm, ← Nat.gcd_assoc]
    exact Nat.gcd_dvd_right (b.natAbs.gcd c) a.natAbs
  have dvd₂ : w ∣ b.natAbs := by
    rw [def_w]
    exact Nat.gcd_dvd_right (c.gcd a.natAbs) b.natAbs
  have dvd₃ : w ∣ c := by
    rw [def_w, Nat.gcd_assoc]
    exact Nat.gcd_dvd_left c (a.natAbs.gcd b.natAbs)
  replace hn := hn w ⟨Int.ofNat_dvd_left.2 dvd₁, Int.ofNat_dvd_left.2 dvd₂,
    Int.ofNat_dvd.2 dvd₃⟩
  rw [Int.ofNat_isUnit, Nat.isUnit_iff] at hn
  exact not_copri hn

private theorem aux_dvd (n : ℤ) {a : ℤ} {c : ℕ} (hc : c ≠ 0) :
    n = (a : ℚ) / (c : ℚ) → (c : ℤ) ∣ a := fun h ↦ by
  refine ⟨n, ?_⟩
  qify
  rw [h]
  exact (mul_div_cancel_of_imp' fun foo ↦
    False.elim (hc <| Rat.natCast_eq_zero.mp foo)).symm

include sqf in
private theorem aux_copri₁ {a b : ℤ} {c : ℕ}
  (hn : ∀ n : ℤ, n ∣ a ∧ n ∣ b ∧ n ∣ c → IsUnit n)
  (hdiv : (c ^ 2 : ℤ) ∣ (a ^ 2 - b ^ 2 * d)) :
    c.Coprime a.natAbs := by
  by_contra!
  simp only [ne_eq] at this
  obtain ⟨k', hk'⟩ := hdiv
  apply_fun (- (- a ^ 2 + · )) at hk'
  simp only [Pi.neg_apply, neg_add_rev, neg_sub, neg_neg, sub_add_cancel] at hk'
  have hk'' : ((c.gcd a.natAbs) ^ 2 : ℤ) ∣ b ^ 2 * d := by
    rw [hk']
    refine (Int.dvd_add_right ?_).2 ?_
    · refine Int.dvd_neg.2 <| Dvd.dvd.mul_right ?_ k'
      exact (Int.pow_dvd_pow_iff (Nat.zero_ne_add_one 1).symm).2
        <| Int.ofNat_dvd.2 <| Nat.gcd_dvd_left c a.natAbs
    · exact (Int.pow_dvd_pow_iff (Nat.zero_ne_add_one 1).symm).2
        <| Int.ofNat_dvd_left.mpr <| Nat.gcd_dvd_right c a.natAbs
  replace hk'' := Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.Coprime.pow 2 2 (aux_copri₀ hn)) <|
      by rwa [← Int.natAbs_pow b 2, ← Int.natAbs_mul, ← Int.ofNat_dvd_left]
  replace sqf := Nat.isUnit_iff.1 <|
    (Int.squarefree_natAbs.2 sqf) (c.gcd a.natAbs) (by rwa [← sq])
  exact this sqf

include sqf in
theorem aux_congruent {a b : ℤ}
  (hdvd : (2 : ℤ) ^ 2 ∣ a ^ 2 - b ^ 2 * d)
  (hn : ∀ (n : ℤ), n ∣ a ∧ n ∣ b ∧ n ∣ (2 : ℤ) → IsUnit n) :
    Odd a ∧ Odd b := by
  have hc : 2 ≠ 0 := (Nat.zero_ne_add_one 1).symm
  have odd_a : Odd a :=
    Int.natAbs_odd.1 <| Nat.Coprime.odd_of_left (aux_copri₁ sqf hn hdvd)
  have odd_a_sq : Odd (a ^ 2) := (Int.odd_pow' hc).2 odd_a
  have even_ab : Even (a ^ 2 - b ^ 2 * d) :=
    even_iff_two_dvd.mpr <| dvd_trans (dvd_pow_self 2 hc) hdvd
  have odd_b := Odd.sub_even odd_a_sq even_ab
  rw [sub_sub_cancel] at odd_b
  replace odd_b : Odd b := Int.Odd.of_mul_right <| Int.Odd.of_mul_left odd_b
  exact ⟨odd_a, odd_b⟩

include sqf in
theorem congruent {a b : ℤ}
  (hdvd : (2 : ℤ) ^ 2 ∣ a ^ 2 - b ^ 2 * d)
  (hn : ∀ (n : ℤ), n ∣ a ∧ n ∣ b ∧ n ∣ (2 : ℤ) → IsUnit n) :
    d ≡ 1 [ZMOD 4] := by
  obtain ⟨odd_a, odd_b⟩ := aux_congruent sqf hdvd hn
  simp only [Nat.cast_ofNat, Int.reducePow] at hdvd
  replace hzero : a ^ 2 - b ^ 2 * d ≡ 0 [ZMOD 4] :=
    Int.ModEq.symm (Dvd.dvd.zero_modEq_int hdvd)
  have mod_b_sq : b ^ 2 ≡ 1 [ZMOD 4] := Int.sq_mod_four_eq_one_of_odd odd_b
  replace hzero := Int.ModEq.add hzero <| Int.ModEq.mul_right d mod_b_sq
  simp only [sub_add_cancel, one_mul, zero_add] at hzero
  exact hzero.symm.trans <| Int.sq_mod_four_eq_one_of_odd odd_a

theorem minpoly_of_int' {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range) :
    x ∈ (integralClosure ℤ ℚ⟮√-d⟯) →
  (Q.calc_min sqf one hx).2.2 ∣ 2 ∧
  ((Q.calc_min sqf one hx).2.2 : ℤ) ^ 2 ∣
    (Q.calc_min sqf one hx).1 ^ 2 - (Q.calc_min sqf one hx).2.1 ^ 2 * d := by
  intro h
  rw [minpoly_of_int] at h
  obtain ⟨hmin, hc, hn ⟩ := Q.calc_min_prop sqf one hx
  rw [h] at hmin
  have hmin₁ := hmin
  apply_fun (- ·.coeff 1) at hmin₁
  simp only [coeff_map, eq_intCast, coeff_add, coeff_sub, coeff_X_pow, OfNat.one_ne_ofNat,
    ↓reduceIte, coeff_mul_X, coeff_C_zero, zero_sub, coeff_C_succ, add_zero, neg_neg] at hmin₁
  have hmin₀ := hmin
  apply_fun (·.coeff 0) at hmin₀
  simp only [coeff_map, eq_intCast, coeff_add, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat,
    ↓reduceIte, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, sub_self,
    zero_add] at hmin₀
  replace hmin₁ : ((Q.calc_min sqf one hx).2.2 : ℤ) ∣ 2 * (Q.calc_min sqf one hx).1 :=
    aux_dvd (- (minpoly ℤ x).coeff 1) hc
    <| by convert hmin₁; simp only [Int.cast_mul, Int.cast_ofNat]
  replace hmin₀ : ((Q.calc_min sqf one hx).2.2 ^ 2 : ℤ) ∣ ((Q.calc_min sqf one hx).1 ^ 2 -
      (Q.calc_min sqf one hx).2.1 ^ 2 * d) := aux_dvd ((minpoly ℤ x).coeff 0)
    (pow_ne_zero 2 hc) <| by simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
      one_mul, Nat.cast_mul, ← sq]
  exact ⟨Int.ofNat_dvd.1 <| Int.dvd_of_dvd_mul_left_of_gcd_one hmin₁
    (aux_copri₁ sqf hn.1 hmin₀), hmin₀⟩

private theorem adjoin_mem₀ {a : ℤ} {c : ℂ}: (a : ℂ) ∈ Algebra.adjoin ℤ {c} := by
  suffices (a : ℂ) ∈ (⊥ : Subalgebra ℤ ℂ) from
    (bot_le (a := Algebra.adjoin ℤ {c})) this
  exact Subalgebra.intCast_mem ⊥ a

theorem adjoin_mem₁ {x : ℚ⟮√-d⟯} {c : ℂ} (hx : x ∈ (algebraMap ℚ ℚ⟮√-d⟯).range)
    (h : x ∈ (integralClosure ℤ ℚ⟮√-d⟯)) : x.1 ∈ Algebra.adjoin ℤ {c} := by
  rw [minpoly_of_int] at h
  have minpoly_deg := minpoly.natDegree_eq_one_iff.2 hx
  rw [h, Polynomial.natDegree_map_eq_of_injective, minpoly.natDegree_eq_one_iff] at minpoly_deg
  swap; exact RingHom.injective_int (algebraMap ℤ ℚ)
  obtain ⟨x', hx'⟩ := minpoly_deg
  simp only [algebraMap_int_eq, eq_intCast] at hx'
  rw [← hx', SubringClass.coe_intCast]
  show (x' : ℂ) ∈ Subsemiring.closure (Set.range (algebraMap ℤ ℂ) ∪ {c})
  exact Subsemiring.subset_closure (Set.subset_union_left (Set.mem_range_self x'))

theorem adjoin_mem₂ {a : ℚ} {c : ℂ}: (a : ℂ) ∈ ℚ⟮c⟯ := by
  suffices (a : ℂ) ∈ (⊥ : Subalgebra ℚ ℂ) from (bot_le (a := ℚ⟮c⟯)) this
  apply SetLike.mem_of_subset
  · simp only [Algebra.coe_bot]; rfl
  · simp only [Set.mem_range, eq_ratCast, Rat.cast_inj, exists_eq]

theorem adjoin_mem₃ {x : ℚ⟮√-d⟯} (hx : x ∉ (algebraMap ℚ ℚ⟮√-d⟯).range)
    (hone : (Q.calc_min sqf one hx).2.2 = 1) : x.1 ∈ Algebra.adjoin ℤ {√-d} := by
  obtain ⟨hmin, -, -⟩ := Q.calc_min_prop sqf one hx
  apply_fun (Polynomial.map (algebraMap ℚ ℂ) · ) at hmin
  rw [minpoly_break] at hmin
  apply_fun (Polynomial.aeval (x : ℂ) · ) at hmin
  simp only [aeval_map_algebraMap, Subalgebra.aeval_coe, minpoly.aeval, ZeroMemClass.coe_zero,
    Rat.cast_intCast, one_div, hone, Nat.cast_one, Rat.cast_one, div_one, map_add, map_intCast,
    map_mul, map_sub, coe_aeval_eq_eval, eval_mul, eval_sub, eval_X, eval_add, eval_intCast, eval_C,
    zero_eq_mul] at hmin
  rcases hmin with hx₁ | hx₁ <;> rw [sub_eq_zero.1 hx₁]
  · refine add_mem adjoin_mem₀ <| mul_mem adjoin_mem₀ ?_
    simpa only [one_div] using Algebra.self_mem_adjoin_singleton ℤ √-d
  · refine sub_mem adjoin_mem₀ <| mul_mem adjoin_mem₀ ?_
    simpa only [one_div] using Algebra.self_mem_adjoin_singleton ℤ √-d

end aux

namespace Z₁

local notation "polyz" => X ^ 2 - C d

private theorem polyz_natDegree : natDegree polyz = 2 := natDegree_X_pow_sub_C
private theorem polyz_Monic : Monic polyz := by monicity!

theorem integralz : IsIntegral ℤ √-d := by
  refine ⟨polyz, ⟨polyz_Monic, ?_⟩⟩
  · simp only [algebraMap_int_eq, one_div, eq_intCast, eval₂_sub, eval₂_X_pow,
    Complex.cpow_ofNat_inv_pow]
    show d - eval₂ (Int.castRingHom ℂ) ((d : ℂ) ^ (2⁻¹ : ℂ)) (C d) = 0
    rw [Polynomial.eval₂_C, eq_intCast, sub_self]

local notation3 "zbase" => Algebra.adjoin.powerBasis' (@integralz d)

private theorem min_polyz_natDegree_le : (minpoly ℤ √-d).natDegree ≤ 2 := by
  rw [← @polyz_natDegree d]
  refine natDegree_le_of_dvd ?_ (X_pow_sub_C_ne_zero (Nat.zero_lt_two) d)
  · refine minpoly.isIntegrallyClosed_dvd integralz ?_
    simp only [one_div, eq_intCast, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow,
      map_intCast, sub_self]

noncomputable abbrev δ : Algebra.adjoin ℤ {√-d} :=
  ⟨√-d, SetLike.mem_coe.1 <| Algebra.subset_adjoin <| Set.mem_singleton √-d⟩

private theorem sqd_sq : (@δ d) ^ 2 = d := by
  apply SetLike.coe_eq_coe.1
  show (√-d) ^ 2 = d
  simp only [one_div, Complex.cpow_ofNat_inv_pow]

include sqf one

private theorem irr_polyz : Irreducible polyz := by
  refine (Monic.irreducible_iff_irreducible_map_fraction_map
    (@polyz_Monic d) (K := ℚ)).2 ?_
  convert Q.poly_irr sqf one
  simp only [algebraMap_int_eq, eq_intCast, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_intCast, map_intCast]

private theorem min_polyz_natDegree : (minpoly ℤ √-d).natDegree = 2 := by
  refine le_antisymm min_polyz_natDegree_le ?_
  rw [minpoly.two_le_natDegree_iff (@integralz d)]
  rintro ⟨x, hx : (algebraMap ℚ ℂ) x = √-d⟩
  have := Q.sqrt_d_not_mem sqf one
  rw [← hx] at this
  absurd this
  exact RingHom.mem_range_self (algebraMap ℚ ℂ) x

private theorem base_dim : dim zbase = 2 := by
  rw [Algebra.adjoin.powerBasis'_dim, min_polyz_natDegree sqf one]

private theorem base_equiv_one : adj (base_dim sqf one) = δ := by
  have : (finChange.equi (base_dim sqf one) 1) =
    ⟨1, by rw [(base_dim sqf one)]; omega⟩ := rfl
  rw [adj, this, basis_eq_pow zbase ⟨1, by rw [(base_dim sqf one)]; omega⟩]
  simp only [adjoin.powerBasis_gen, pow_one]
  exact Algebra.adjoin.powerBasis'_gen integralz

private theorem int_linear_comb (α : Algebra.adjoin ℤ {√-d}) :
    ∃ r s : ℤ, α = r + s * (@δ d) := by
  have := quadratic.repr (base_dim sqf one) α
  rw [base_equiv_one sqf one] at this
  simp only [algebraMap_int_eq, eq_intCast, SetLike.mk_smul_mk, one_div, zsmul_eq_mul] at this
  convert this
  simp only [MulMemClass.coe_mul, SubringClass.coe_intCast, one_div]

private theorem adjoin_mem₄ (α : Algebra.adjoin ℤ {√-d}) : α.1 ∈ ℚ⟮√-d⟯ := by
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one α
  rw [hrs]
  simp only [one_div, AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul]
  exact add_mem adjoin_mem₂ <| mul_mem adjoin_mem₂ <| mem_adjoin_simple_self ℚ _

private theorem adjoin_of_ring_of_int (x : ℚ⟮√-d⟯) (h : x.1 ∈ Algebra.adjoin ℤ {√-d}) :
    x ∈ (integralClosure ℤ ℚ⟮√-d⟯) := by
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one ⟨x, h⟩
  apply Subtype.val_inj.2 at hrs
  simp only [AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul,
    one_div] at hrs
  have : x = r + s * (AdjoinSimple.gen ℚ √-d) := by
    apply Subtype.val_inj.1
    simp only [AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul,
      AdjoinSimple.coe_gen, one_div]
    exact hrs
  rw [this]
  refine add_mem ?_ ?_
  · rw [mem_integralClosure_iff]
    exact isIntegral_algebraMap
  · refine mul_mem isIntegral_algebraMap ?_
    · rw [mem_integralClosure_iff, ← isIntegral_algebraMap_iff (@algMap_inj d),
        AdjoinSimple.algebraMap_gen ℚ (√-d)]
      exact integralz

instance : Module.Free ℤ (Algebra.adjoin ℤ {√-d}) := ⟨⟨Fin (dim zbase), basis zbase⟩⟩

private theorem traceForm_11 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) 1 1 = 2 := by
  rw [Algebra.traceForm_apply, one_mul,
    ← @algebraMap.coe_one ℤ (Algebra.adjoin ℤ {√-d}) _ _,
    Algebra.trace_algebraMap, PowerBasis.finrank zbase,
    base_dim sqf one, nsmul_eq_mul, Nat.cast_ofNat, mul_one]

private theorem traceForm_1δ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) 1 δ = 0 := by
  rw [Algebra.traceForm_apply, one_mul, Algebra.trace_eq_matrix_trace (basis zbase)
    δ, Matrix.trace, finChange.change (base_dim sqf one)]
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one), mul_one]
  have neq : (finChange.equi (base_dim sqf one)) 0 ≠
    (finChange.equi (base_dim sqf one)) 1 := ne_of_beq_false rfl
  have := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one)) 1)
    ((finChange.equi (base_dim sqf one)) 0)
  rw [ite_cond_eq_false _ _ (eq_false neq.symm)] at this
  rw [← base_equiv_one sqf one, adj, this, zero_add, ← adj, base_equiv_one sqf one,
    ← sq, sqd_sq]
  have cast : @Int.cast (Algebra.adjoin ℤ {√-d}) AddGroupWithOne.toIntCast d =
    ((algebraMap ℤ (Algebra.adjoin ℤ {√-d})) d) * 1 := by
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  replace this := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one)) 0)
    ((finChange.equi (base_dim sqf one)) 1)
  rw [ite_cond_eq_false _ _ (eq_false neq)] at this
  rw [cast, Basis.repr_smul', ← base_equiv_zero (base_dim sqf one), this, mul_zero]

private theorem traceForm_δ1 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) δ 1 = 0 := by
  simpa only [Algebra.traceForm_apply, mul_one, one_mul] using traceForm_1δ sqf one

private theorem traceForm_δδ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {√-d}) δ δ = 2 * d := by
  rw [Algebra.traceForm_apply, ← sq, sqd_sq, Algebra.trace_eq_matrix_trace (basis zbase)
    d, Matrix.trace, finChange.change (base_dim sqf one)]
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one), mul_one]
  have := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one)) 0)
    ((finChange.equi (base_dim sqf one)) 0)
  rw [ite_cond_eq_true _ _ (eq_self ((finChange.equi (base_dim sqf one)) 0))] at this
  have cast : @Int.cast (Algebra.adjoin ℤ {√-d}) AddGroupWithOne.toIntCast d =
    ((algebraMap ℤ (Algebra.adjoin ℤ {√-d})) d) * 1 := by
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  nth_rw 1 [cast]
  rw [Basis.repr_smul', ← base_equiv_zero (base_dim sqf one), this, mul_one]
  replace cast : @Int.cast (Algebra.adjoin ℤ {√-d}) AddGroupWithOne.toIntCast d =
    ((algebraMap ℤ (Algebra.adjoin ℤ {√-d})) d) := by
      rw [algebraMap_int_eq, eq_intCast]
  replace this := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one)) 1)
    ((finChange.equi (base_dim sqf one)) 1)
  rw [ite_cond_eq_true _ _ (eq_self ((finChange.equi (base_dim sqf one)) 1))] at this
  rw [cast, Basis.repr_smul', this, mul_one, Int.two_mul d]

private def traceMat : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 2 * d]

private theorem mat_conv :
  (Matrix.reindexAlgEquiv ℤ ℤ (finChange.equi (base_dim sqf one)).symm)
    (Algebra.traceMatrix ℤ (basis zbase)) = @traceMat d := Matrix.ext fun i j ↦ by
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one)]
    simp only [mul_one, traceMat, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    exact traceForm_11 sqf one
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one), ← adj,
      base_equiv_one sqf one]
    simp only [one_mul, traceMat, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    exact traceForm_1δ sqf one
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one), ← adj,
      base_equiv_one sqf one]
    simp only [mul_one, traceMat, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_fin_const]
    exact traceForm_δ1 sqf one
  · rw [Algebra.traceMatrix, Matrix.of_apply, ← adj, base_equiv_one sqf one]
    simp only [MulMemClass.mk_mul_mk, one_div, traceMat, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    exact traceForm_δδ sqf one

private theorem discr_z : Algebra.discr ℤ (basis zbase) = 4 * d := by
  rw [Algebra.discr_def]
  have := Matrix.det_reindexAlgEquiv ℤ ℤ (finChange.equi (base_dim sqf one)).symm
    (Algebra.traceMatrix ℤ (basis zbase))
  rw [← this, mat_conv sqf one, traceMat, Matrix.det_fin_two_of, mul_zero, sub_zero,
    ← mul_assoc]; rfl

variable (hd : ¬ d ≡ 1 [ZMOD 4])

include hd

theorem ring_of_int (x : ℚ⟮√-d⟯) : x ∈ (integralClosure ℤ ℚ⟮√-d⟯) ↔
  x.1 ∈ Algebra.adjoin ℤ {√-d} := by
  constructor
  · intro h
    by_cases hx : x ∈ (algebraMap ℚ ℚ⟮√-d⟯).range
    · exact adjoin_mem₁ hx h
    · obtain ⟨c_div, hmin₀⟩ := minpoly_of_int' sqf one hx h
      obtain ⟨-, hc, hn⟩ := Q.calc_min_prop sqf one hx
      have c_le := Nat.le_of_dvd Nat.zero_lt_two c_div
      set c := (Q.calc_min sqf one hx).2.2
      match hmatch : c with
      | 0 => exact False.elim (hc rfl)
      | 1 => exact adjoin_mem₃ sqf one hx hmatch
      | 2 => exact False.elim <| hd <| congruent sqf hmin₀ hn.1
  · exact adjoin_of_ring_of_int sqf one x

noncomputable def ring_of_int' : 𝓞 ℚ⟮√-d⟯ ≃ₐ[ℤ] Algebra.adjoin ℤ {√-d} where
  toFun x := ⟨x, (ring_of_int sqf one hd x).1 x.2⟩
  invFun y := ⟨⟨y.1, adjoin_mem₄ sqf one y⟩,
    (ring_of_int sqf one hd ⟨y.1, adjoin_mem₄ sqf one y⟩).2 y.2⟩
  left_inv x := rfl
  right_inv y := by
    simp only [RingOfIntegers.map_mk, Subtype.coe_eta]
  map_mul' x y := by
    simp only [map_mul, MulMemClass.coe_mul, MulMemClass.mk_mul_mk]
  map_add' x y := by
    simp only [map_add, AddMemClass.coe_add, AddMemClass.mk_add_mk]
  commutes' x := by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast, SubringClass.coe_intCast]
    rfl

noncomputable abbrev intbase :=
  PowerBasis.map zbase (ring_of_int' sqf one hd).symm

theorem final : NumberField.discr ℚ⟮√-d⟯ = 4 * d := by
  rw [← NumberField.discr_eq_discr ℚ⟮√-d⟯ (intbase sqf one hd).basis, intbase]
  simp only [map_dim, map_basis]
  have : (basis zbase).map (ring_of_int' sqf one hd).symm.toLinearEquiv =
    (ring_of_int' sqf one hd).symm ∘ (basis zbase) := by
    funext x
    simp only [Algebra.adjoin.powerBasis'_dim, Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Function.comp_apply]
  rw [this, ← Algebra.discr_eq_discr_of_algEquiv (basis zbase) (ring_of_int' sqf one hd).symm]
  exact discr_z sqf one

end Z₁

namespace Z₂

variable (hd : d ≡ 1 [ZMOD 4])

noncomputable def k : ℤ := by
  have := Int.ModEq.sub hd (show 1 ≡ 1 [ZMOD 4] by rfl)
  rw [sub_self, Int.modEq_zero_iff_dvd] at this
  exact Classical.choose this

theorem hk : 4 * (k hd) = d - 1 := by
  have := Int.ModEq.sub hd (show 1 ≡ 1 [ZMOD 4] by rfl)
  rw [sub_self, Int.modEq_zero_iff_dvd] at this
  show 4 * (Classical.choose this) = d - 1
  exact (Classical.choose_spec this).symm

noncomputable abbrev polyz : ℤ[X] := X ^ 2 - C 1 * X - C (k hd)

theorem polyz_natDegree : (polyz hd).natDegree = 2 := by
  unfold polyz; compute_degree!

theorem polyz_Monic : (polyz hd).Monic := by
  unfold polyz; monicity!

local notation "γ" => (1 + √-d) / 2

theorem eval_zero : Polynomial.eval₂ (algebraMap ℤ ℂ) γ (polyz hd) = 0 := by
  unfold polyz
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_one, one_mul, eval₂_sub, eval₂_X_pow,
    eval₂_X]
  conv =>
    enter [1, 2]
    change eval₂ (algebraMap ℤ ℂ) γ (C (k hd))
    rw [Polynomial.eval₂_C, algebraMap_int_eq, eq_intCast]
  ring_nf
  simp only [one_div, Complex.cpow_ofNat_inv_pow]
  have : (-1 / 4 + ((d : ℂ) * 4⁻¹ - (k hd))) * 4 = 0 := by
    rw [add_mul, div_mul, div_self (OfNat.zero_ne_ofNat 4).symm, div_one,
      sub_mul, mul_assoc]
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, mul_one]
    norm_cast
    rw [mul_comm _ 4, hk hd, sub_sub_cancel]; rfl
  exact (mul_eq_zero_iff_right (OfNat.zero_ne_ofNat 4).symm).1 this

private theorem adjoin_mem₄ : (AdjoinSimple.gen ℚ (√-d)).1 ∈ Algebra.adjoin ℤ {γ} := by
  suffices (AdjoinSimple.gen ℚ (√-d)).1 = 2 * γ - 1 from by
    rw [this]
    refine sub_mem (mul_mem adjoin_mem₀ <| Algebra.self_mem_adjoin_singleton ℤ _) ?_
    · convert @adjoin_mem₀ 1 γ
      exact Int.cast_one.symm
  rw [AdjoinSimple.coe_gen, one_div, mul_div_cancel₀ _ (NeZero.ne' 2).symm,
    add_sub_cancel_left]

private theorem adjoin_mem₅ {a b : ℤ} (hodd : Odd a ∧ Odd b) :
    (a + b * (AdjoinSimple.gen ℚ (√-d)).1) / 2 ∈ Algebra.adjoin ℤ {γ} := by
  obtain ⟨⟨k₁, ka⟩, ⟨k₂, kb⟩⟩ := hodd
  rw [ka, kb]
  conv =>
    enter [2]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, AdjoinSimple.coe_gen,
      add_div]
    rw [← mul_div, mul_div_cancel₀ _ (NeZero.ne' 2).symm, add_mul, add_div, one_mul,
      mul_assoc, ← mul_div, mul_div_cancel₀ _ (NeZero.ne' 2).symm, ← add_assoc, add_comm, ← add_assoc, ← add_assoc, add_comm _ (1 / 2), ← add_assoc, ← add_div]
  exact add_mem (add_mem (Algebra.self_mem_adjoin_singleton ℤ _) adjoin_mem₀)
    <| mul_mem adjoin_mem₀ adjoin_mem₄

include hd

theorem integralz : IsIntegral ℤ γ := ⟨polyz hd, ⟨polyz_Monic hd, eval_zero hd⟩⟩

local notation3 "zbase" => Algebra.adjoin.powerBasis' (integralz hd)

private theorem min_polyz_natDegree_le : (minpoly ℤ γ).natDegree ≤ 2 := by
  rw [← polyz_natDegree hd]
  exact natDegree_le_of_dvd
    (minpoly.isIntegrallyClosed_dvd (integralz hd) <| eval_zero hd)
      <| Monic.ne_zero_of_ne Int.zero_ne_one <| polyz_Monic hd

noncomputable abbrev δ : Algebra.adjoin ℤ {γ} :=
  ⟨γ, SetLike.mem_coe.1 <| Algebra.subset_adjoin <| Set.mem_singleton γ⟩

noncomputable abbrev polyq := Polynomial.map (algebraMap ℤ ℚ) (polyz hd)

private theorem polyq_natDegree : (polyq hd).natDegree = 2 := by
  unfold polyq
  simp only [algebraMap_int_eq, Polynomial.map_sub, eq_intCast, Int.cast_one, one_mul,
    Polynomial.map_pow, map_X, Polynomial.map_intCast]
  compute_degree!

private theorem break_sq :
    ((@δ d) ^ 2) = (k hd) * 1 + 1 * (@δ d) := by
  apply Subtype.val_inj.1
  simp only [SubmonoidClass.mk_pow, mul_one, one_mul, AddMemClass.coe_add,
    SubringClass.coe_intCast]
  have : ((1 + (d : ℂ) ^ (1 / 2 : ℂ)) / 2) ^ 2 = ((1 + (d : ℂ) ^ (1 / 2 : ℂ)) ^ 2) / 4 := by
    rw [div_pow]; congr; norm_cast
  rw [this]
  refine mul_right_cancel₀ (b := 4) (OfNat.zero_ne_ofNat 4).symm ?_
  rw [div_mul_cancel₀ _ (OfNat.zero_ne_ofNat 4).symm, add_mul]
  norm_cast
  rw [mul_comm (k hd) _, hk hd, show (4 : ℂ) = (2 : ℂ) * 2 by norm_cast, ← mul_assoc,
    div_mul_cancel₀ _ (NeZero.ne' 2).symm, add_mul, one_mul, sq, add_mul, one_mul, mul_add, mul_one, ← sq]
  simp only [one_div, Complex.cpow_ofNat_inv_pow, Int.cast_sub, Int.cast_one]; group

private theorem break_trip : (@δ d) * (@δ d) * (@δ d) = (k hd) + (1 + (k hd)) * (@δ d) := by
  rw [← sq, break_sq hd, mul_one, one_mul, add_mul, ← sq, break_sq hd]; group

include sqf one

private theorem rat_sq_sub_ne_zero (a : ℚ) : a ^ 2 - a - (k hd) ≠ 0 := by
  by_contra!
  apply_fun (· * 4) at this
  rw [sub_mul, zero_mul] at this
  norm_cast at this
  rw [mul_comm (k hd) 4, hk, sub_eq_zero] at this
  apply_fun (· + 1) at this
  rw [Int.cast_sub, Int.cast_one, sub_add_cancel, sub_mul] at this
  have eq_sq : a ^ 2 * 4 - a * 4 + 1 = (2 * a - 1) ^ 2 := by
    rw [sq, sq, sub_mul, mul_sub, one_mul, mul_one, sub_sub, ← add_sub_assoc,
      sub_sub_eq_add_sub, ← mul_two, mul_comm 2 a, ← mul_assoc, mul_comm (a * 2) a,
      ← mul_assoc, add_sub_right_comm, mul_assoc _ _ 2, mul_assoc _ _ 2]
    norm_cast
  rw [eq_sq, ← sub_eq_zero] at this
  exact (Q.rat_sq_sub_ne_zero sqf one (2 * a - 1)) this

private theorem polyz_irr : Irreducible (polyz hd) := by
  refine Polynomial.Monic.irreducible_of_irreducible_map (algebraMap ℤ ℚ)
    (polyz hd) (polyz_Monic hd) ?_
  refine (irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 ?_
  <;> (try rw [polyq_natDegree hd]); (try omega)
  · refine Multiset.eq_zero_iff_forall_not_mem.2 (fun a ↦ ?_)
    by_contra!
    simp only [algebraMap_int_eq, Polynomial.map_sub, eq_intCast, Int.cast_one, one_mul,
      Polynomial.map_pow, map_X, Polynomial.map_intCast, mem_roots', ne_eq, IsRoot.def, eval_sub,
      eval_pow, eval_X, eval_intCast] at this
    exact (rat_sq_sub_ne_zero sqf one hd a) this.2

private theorem min_polyz_natDegree : (minpoly ℤ γ).natDegree = 2 := by
  refine le_antisymm (min_polyz_natDegree_le hd) ?_
  rw [minpoly.two_le_natDegree_iff (integralz hd)]
  rintro ⟨x, hx : x = γ⟩
  apply_fun (· * 2) at hx
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hx
  apply_fun ((-1 + ·) ^ 2) at hx
  simp only [Pi.pow_apply, one_div, neg_add_cancel_left, Complex.cpow_ofNat_inv_pow] at hx
  rw [← sub_eq_zero] at hx
  replace hx : (-1 + (x : ℚ) * 2) ^ 2 - (d : ℚ) = 0 := by
    norm_cast; norm_cast at hx
  exact Q.rat_sq_sub_ne_zero sqf one (-1 + (x : ℚ) * 2) hx

private theorem base_dim : dim zbase = 2 := by
  rwa [Algebra.adjoin.powerBasis'_dim, min_polyz_natDegree sqf one]

private theorem base_equiv_one : adj (base_dim sqf one hd) = δ := by
  have : (finChange.equi (base_dim sqf one hd) 1) =
    ⟨1, by rw [(base_dim sqf one hd)]; omega⟩ := rfl
  rw [adj, this, basis_eq_pow zbase ⟨1, by rw [(base_dim sqf one hd)]; omega⟩]
  simp only [adjoin.powerBasis_gen, pow_one]
  exact Algebra.adjoin.powerBasis'_gen <| integralz hd

private theorem int_linear_comb (α : Algebra.adjoin ℤ {γ}) :
    ∃ r s : ℤ, α = r + s * (@δ d) := by
  have := quadratic.repr (base_dim sqf one hd) α
  rw [base_equiv_one sqf one] at this
  simp only [algebraMap_int_eq, eq_intCast, SetLike.mk_smul_mk, one_div, zsmul_eq_mul] at this
  convert this
  simp only [MulMemClass.coe_mul, SubringClass.coe_intCast, one_div]
  exact hd

private theorem adjoin_mem₆ (α : Algebra.adjoin ℤ {γ}) : α.1 ∈ ℚ⟮√-d⟯ := by
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one hd α
  rw [hrs]
  simp only [one_div, AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul]
  exact add_mem adjoin_mem₂ <| mul_mem adjoin_mem₂ <|
    div_mem (add_mem (IntermediateField.one_mem _)
      (mem_adjoin_simple_self ℚ _)) adjoin_mem₂

noncomputable abbrev δ' : ℚ⟮√-d⟯ := by
  refine ⟨γ, div_mem ?_ adjoin_mem₂⟩
  · refine add_mem ?_ (mem_adjoin_simple_self ℚ _)
    · convert (@adjoin_mem₂ 1 √-d)
      exact Rat.cast_one.symm

private theorem adjoin_of_ring_of_int (x : ℚ⟮√-d⟯) : x.1 ∈ Algebra.adjoin ℤ {γ} →
    x ∈ (integralClosure ℤ ℚ⟮√-d⟯) := by
  intro h
  obtain ⟨r, s, hrs⟩ := int_linear_comb sqf one hd ⟨x, h⟩
  apply Subtype.val_inj.2 at hrs
  simp only [AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul,
    one_div] at hrs
  have : x = r + s * (@δ' d) := by
    apply Subtype.val_inj.1
    simp only [AddMemClass.coe_add, SubringClass.coe_intCast, MulMemClass.coe_mul,
      AdjoinSimple.coe_gen, one_div]
    exact hrs
  rw [this]
  refine add_mem ?_ ?_
  · rw [mem_integralClosure_iff]
    exact isIntegral_algebraMap
  · refine mul_mem isIntegral_algebraMap ?_
    · rw [mem_integralClosure_iff, ← isIntegral_algebraMap_iff (@algMap_inj d)]
      exact (integralz hd)

instance free_mod : Module.Free ℤ (Algebra.adjoin ℤ {γ}) := ⟨⟨Fin (dim zbase), basis zbase⟩⟩

private theorem traceForm_11 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) 1 1 = 2 := by
  rwa [Algebra.traceForm_apply, one_mul, ← @algebraMap.coe_one ℤ (Algebra.adjoin ℤ {γ}) _ _,
    @Algebra.trace_algebraMap ℤ (Algebra.adjoin ℤ {γ}) _ _ _ _ (free_mod hd) 1,
    PowerBasis.finrank zbase, base_dim sqf one, nsmul_eq_mul, Nat.cast_ofNat, mul_one]

private theorem aux_traceForm_1δ :
    ((basis zbase).repr (k hd)) ((finChange.equi (base_dim sqf one hd)) 1) = 0 := by
  have cast : @Int.cast (Algebra.adjoin ℤ {γ}) AddGroupWithOne.toIntCast (k hd) =
    ((algebraMap ℤ (Algebra.adjoin ℤ {γ})) (k hd)) * 1 := by
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  have neq : (finChange.equi (base_dim sqf one hd)) 0 ≠
    (finChange.equi (base_dim sqf one hd)) 1 := ne_of_beq_false rfl
  replace this := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one hd)) 0)
    ((finChange.equi (base_dim sqf one hd)) 1)
  rw [ite_cond_eq_false _ _ (eq_false neq)] at this
  rw [cast, Basis.repr_smul', ← base_equiv_zero (base_dim sqf one hd), this, mul_zero]

private theorem aux_traceForm_1δ' :
    ((basis zbase).repr (δ * δ)) ((finChange.equi (base_dim sqf one hd)) 1) = 1 := by
  rw [← sq, break_sq hd]
  simp only [mul_one, one_mul, map_add, Fin.isValue, Finsupp.coe_add, Pi.add_apply]
  have neq : (finChange.equi (base_dim sqf one hd)) 0 ≠
    (finChange.equi (base_dim sqf one hd)) 1 := ne_of_beq_false rfl
  replace this := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one hd)) 1)
    ((finChange.equi (base_dim sqf one hd)) 1)
  rw [ite_cond_eq_true _ _ (eq_self ((finChange.equi (base_dim sqf one hd)) 1))] at this
  rw [← base_equiv_one sqf one hd, adj, this, aux_traceForm_1δ sqf one hd, zero_add]

private theorem aux_traceForm_1δ'' :
    ((basis zbase).repr δ) ((finChange.equi (base_dim sqf one hd)) 0) = 0 := by
  have neq : (finChange.equi (base_dim sqf one hd)) 0 ≠
      (finChange.equi (base_dim sqf one hd)) 1 := ne_of_beq_false rfl
  have := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one hd)) 1)
    ((finChange.equi (base_dim sqf one hd)) 0)
  rw [ite_cond_eq_false _ _ (eq_false neq.symm)] at this
  rw [← base_equiv_one sqf one hd, adj, this]

private theorem traceForm_1δ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) 1 δ = 1 := by
  rw [Algebra.traceForm_apply, one_mul, Algebra.trace_eq_matrix_trace (basis zbase)
    δ, Matrix.trace, finChange.change (base_dim sqf one hd)]
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one hd), mul_one]
  rw [aux_traceForm_1δ'' sqf one hd, zero_add, ← adj, base_equiv_one sqf one hd]
  exact aux_traceForm_1δ' sqf one hd

private theorem traceForm_δ1 :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) δ 1 = 1 := by
  simpa only [Algebra.traceForm_apply, mul_one, one_mul] using traceForm_1δ sqf one hd

private theorem aux_traceForm_δδ : ((basis zbase).repr (δ * δ)) ((finChange.equi (base_dim sqf one hd)) 0) = (k hd) := by
  rw [← sq, break_sq hd]
  simp only [mul_one, one_mul, map_add, Fin.isValue, Finsupp.coe_add, Pi.add_apply]
  have cast : @Int.cast (Algebra.adjoin ℤ {γ}) AddGroupWithOne.toIntCast (k hd) =
    ((algebraMap ℤ (Algebra.adjoin ℤ {γ})) (k hd)) * 1 := by
      rw [algebraMap_int_eq, eq_intCast, mul_one]
  replace this := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one hd)) 0)
    ((finChange.equi (base_dim sqf one hd)) 0)
  rw [ite_cond_eq_true _ _ (eq_self ((finChange.equi (base_dim sqf one hd)) 0))] at this
  rw [aux_traceForm_1δ'' sqf one hd, cast, Basis.repr_smul',
    ← base_equiv_zero (base_dim sqf one hd), this, mul_one, add_zero]

private theorem traceForm_δδ :
    Algebra.traceForm ℤ (Algebra.adjoin ℤ {γ}) δ δ = 1 + 2 * (k hd) := by
  rw [Algebra.traceForm_apply, Algebra.trace_eq_matrix_trace (basis zbase)
    _, Matrix.trace, finChange.change (base_dim sqf one hd)]
  simp only [Equiv.toFun_as_coe, Matrix.diag_apply, Fin.sum_univ_two, Fin.isValue]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    base_equiv_zero (base_dim sqf one hd), mul_one, aux_traceForm_δδ sqf one hd,
    ← adj, base_equiv_one sqf one hd, break_trip hd]
  simp only [map_add, Fin.isValue, Finsupp.coe_add, Pi.add_apply]
  rw [aux_traceForm_1δ sqf one hd, zero_add, ← base_equiv_one sqf one hd, adj]
  replace cast : @OfNat.ofNat (Algebra.adjoin ℤ {γ}) 1 One.toOfNat1 + @Int.cast (Algebra.adjoin ℤ {γ}) AddGroupWithOne.toIntCast (k hd) =
    ((algebraMap ℤ (Algebra.adjoin ℤ {γ})) (1 + (k hd))) := by
      rw [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_one]
  have := Basis.repr_self_apply (basis zbase)
    ((finChange.equi (base_dim sqf one hd)) 1)
    ((finChange.equi (base_dim sqf one hd)) 1)
  rw [ite_cond_eq_true _ _ (eq_self ((finChange.equi (base_dim sqf one hd)) 1))] at this
  rw [cast, Basis.repr_smul', this, mul_one, add_comm, add_assoc, Int.two_mul (k hd)]

noncomputable def traceMat : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1 + 2 * (k hd)]

private theorem mat_conv :
  (Matrix.reindexAlgEquiv ℤ ℤ (finChange.equi (base_dim sqf one hd)).symm)
    (Algebra.traceMatrix ℤ (basis zbase)) = traceMat hd := Matrix.ext fun i j ↦ by
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one hd)]
    simp only [mul_one, traceMat, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    exact traceForm_11 sqf one hd
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one hd), ← adj,
      base_equiv_one sqf one hd]
    simp only [one_mul, traceMat, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    exact traceForm_1δ sqf one hd
  · rw [Algebra.traceMatrix, Matrix.of_apply, base_equiv_zero (base_dim sqf one hd), ← adj,
      base_equiv_one sqf one hd]
    simp only [mul_one, traceMat, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_fin_const]
    exact traceForm_δ1 sqf one hd
  · rw [Algebra.traceMatrix, Matrix.of_apply, ← adj, base_equiv_one sqf one hd]
    simp only [MulMemClass.mk_mul_mk, one_div, traceMat, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    exact traceForm_δδ sqf one hd

private theorem discr_z : Algebra.discr ℤ (basis zbase) = d := by
  have := Matrix.det_reindexAlgEquiv ℤ ℤ (finChange.equi (base_dim sqf one hd)).symm
    (Algebra.traceMatrix ℤ (basis zbase))
  rw [Algebra.discr_def, ← this, mat_conv sqf one hd, traceMat, Matrix.det_fin_two_of,
    mul_add, mul_one, mul_one, ← mul_assoc, show (2 : ℤ) * 2 = 4 by rfl, hk hd]; group

theorem ring_of_int (x : ℚ⟮√-d⟯) : x ∈ (integralClosure ℤ ℚ⟮√-d⟯) ↔
  x.1 ∈ Algebra.adjoin ℤ {γ} := by
  constructor
  · intro h
    by_cases hx : x ∈ (algebraMap ℚ ℚ⟮√-d⟯).range
    · exact adjoin_mem₁ hx h
    · obtain ⟨c_div, hdvd⟩ := minpoly_of_int' sqf one hx h
      obtain ⟨hm, hc, ⟨hn₁, hn₂⟩⟩ := Q.calc_min_prop sqf one hx
      have c_le := Nat.le_of_dvd Nat.zero_lt_two c_div
      set c := (Q.calc_min sqf one hx).2.2
      match hmatch : c with
      | 0 => exact False.elim (hc rfl)
      | 1 =>
        simp only [Nat.cast_one, Rat.cast_one, div_one] at hn₂
        rw [hn₂]
        exact add_mem adjoin_mem₀ <| mul_mem adjoin_mem₀ adjoin_mem₄
      | 2 =>
        simp only [Nat.cast_ofNat, Rat.cast_ofNat] at hn₂
        rw [hn₂]
        exact adjoin_mem₅ <| aux_congruent sqf hdvd hn₁
  · exact adjoin_of_ring_of_int sqf one hd x

noncomputable def ring_of_int' : 𝓞 ℚ⟮√-d⟯ ≃ₐ[ℤ] Algebra.adjoin ℤ {γ} where
  toFun x := ⟨x, (ring_of_int sqf one hd x).1 x.2⟩
  invFun y := ⟨⟨y.1, adjoin_mem₆ sqf one hd y⟩,
    (ring_of_int sqf one hd ⟨y.1, adjoin_mem₆ sqf one hd y⟩).2 y.2⟩
  left_inv x := rfl
  right_inv y := by
    simp only [RingOfIntegers.map_mk, Subtype.coe_eta]
  map_mul' x y := by
    simp only [map_mul, MulMemClass.coe_mul, MulMemClass.mk_mul_mk]
  map_add' x y := by
    simp only [map_add, AddMemClass.coe_add, AddMemClass.mk_add_mk]
  commutes' x := by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast, SubringClass.coe_intCast]
    rfl

noncomputable abbrev intbase :=
  PowerBasis.map zbase (ring_of_int' sqf one hd).symm

theorem final : NumberField.discr ℚ⟮√-d⟯ = d := by
  rw [← NumberField.discr_eq_discr ℚ⟮√-d⟯ (intbase sqf one hd).basis, intbase]
  simp only [map_dim, map_basis]
  have : (basis zbase).map (ring_of_int' sqf one hd).symm.toLinearEquiv =
    (ring_of_int' sqf one hd).symm ∘ (basis zbase) := by
    funext x
    simp only [Algebra.adjoin.powerBasis'_dim, Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Function.comp_apply]
  rw [this, ← Algebra.discr_eq_discr_of_algEquiv (basis zbase) (ring_of_int' sqf one hd).symm]
  exact discr_z sqf one hd

end Z₂

end nontrivial

include sqf in
theorem quadratic_discr :
    (  d ≡ 1 [ZMOD 4] → NumberField.discr ℚ⟮√-d⟯ = d) ∧
    (¬ d ≡ 1 [ZMOD 4] → NumberField.discr ℚ⟮√-d⟯ = 4 * d) := by
  by_cases one : d ≠ 1
  · exact ⟨Z₂.final sqf one, Z₁.final sqf one⟩
  · simp only [ne_eq, Decidable.not_not] at one
    constructor
    · intro hcong
      rw [one, ← discr_rat]
      refine discr_eq_discr_of_algEquiv _ ?_
      rw [discr_rat]
      have : ℚ⟮((1 : ℤ) ^ (1 / 2 : ℂ) : ℂ)⟯ = ⊥ := by
        rw [← le_bot_iff, adjoin_le_iff]
        simp only [Int.cast_one, one_div, Complex.one_cpow, Set.singleton_subset_iff,
          SetLike.mem_coe]
        exact IntermediateField.one_mem _
      exact (IntermediateField.equivOfEq this).trans (botEquiv ℚ ℂ)
    · intro hcong
      rw [one] at hcong; tauto
