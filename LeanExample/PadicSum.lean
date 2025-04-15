import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-
Let $0 \neq x \in \mathbb{Q}$. Show that $|x| \prod_{p \text { prime }}|x|_{p}=1$. (First show that $|x|_{p}=1$ for almost all primes $p$. )
-/

variable {x : ℚ} (h : x ≠ 0)

/--$(p : \mathbb{Q})^{\text{padicValRat } p x} = \frac{(p : \mathbb{Q})^{\text{padicValNat } p |x.num|}}{(p : \mathbb{Q})^{\text{padicValNat } p x.den}}$.-/
lemma Rat.pow_padiv {p : ℕ} (hp : p ≠ 0) :
  (p : ℚ) ^ padicValRat p x =
    (p : ℚ) ^ padicValNat p x.num.natAbs / (p : ℚ) ^ padicValNat p x.den := by
  have : ((p : ℚ) ^ padicValRat p x) * (p : ℚ) ^ padicValNat p x.den =
      (p : ℚ) ^ padicValNat p x.num.natAbs := by
    -- Start with the definition of p-adic valuation for rationals: $\text{padicValRat } p x = \text{padicValInt } p x = \text{padicValNat } p |x.num| - \text{padicValNat } p x.den$.
    unfold padicValRat padicValInt
    calc
      -- Substitute the definition into the exponent: $(p : \mathbb{Q})^{(\text{padicValNat } p |x.num| - \text{padicValNat } p x.den)} \cdot (p : \mathbb{Q})^{\text{padicValNat } p x.den}$.
      _ = (p : ℚ) ^ (((padicValNat p x.num.natAbs) : ℤ) - ((padicValNat p x.den) : ℤ) +
      (padicValNat p x.den : ℤ)) := by
        -- Apply the exponent rule $a^{b+c} = a^b \cdot a^c$ in reverse, $a^{u-v} \cdot a^v = a^{(u-v)+v} = a^u$.
        rw [zpow_add', zpow_natCast]
        -- Ensure the base $(p : \mathbb{Q}) \neq 0$ for the power rule, which is true as $p \neq 0$.
        refine Or.intro_left _ (Nat.cast_ne_zero.2 hp)
      -- Simplify the exponent by canceling $-(\text{padicValNat } p x.den) + (\text{padicValNat } p x.den)$.
      _ = _ := by
        -- Apply basic arithmetic to simplify the exponent: $(u-v)+v = u$.
        rw [sub_add_cancel, zpow_natCast]
  -- Divide both sides of the equation by $(p : \mathbb{Q})^{\text{padicValNat } p x.den}$ to isolate $(p : \mathbb{Q})^{\text{padicValRat } p x}$.
  rw [← this, ← mul_div, div_self, mul_one]
  -- Simplify the resulting expression by canceling the common term and using $a/a = 1$ and $1 \cdot b = b$.
  simp only [ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, hp,
    padicValNat.eq_zero_iff, Rat.den_ne_zero, false_or, not_or, Decidable.not_not,
    false_and, not_false_eq_true]

include h in
/--The product of $(p : \mathbb{Q})^{\text{padicValRat } p x}$ for primes $p < m$ yields $|x|$ for sufficiently large $m$. -/
lemma prod_pow_prime_padicValRat : ∀ m, x.den < m ∧ x.num.natAbs < m →
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range m),
      (p : ℚ) ^ padicValRat p x = |x| := by
  intro m ⟨hden, hnum⟩
  -- Use the prime factorization of the denominator: $x.den = \prod_{p< m, p \text{ prime}} p^{\text{padicValNat } p x.den}$.
  have prod1 := Nat.prod_pow_prime_padicValNat x.den x.den_nz m hden
  -- Use the prime factorization of the numerator's absolute value: $|x.num| = \prod_{p< m, p \text{ prime}} p^{\text{padicValNat } p |x.num|}$.
  have prod2 := Nat.prod_pow_prime_padicValNat x.num.natAbs
    (Int.natAbs_ne_zero.2 ((x.num_ne_zero).2 h)) m hnum
  -- Express the ratio of numerator and denominator factorizations as a product of ratios.
  have eq1 : ∏ p ∈ Finset.filter Nat.Prime (Finset.range m),
    (p ^ padicValNat p x.num.natAbs : ℚ) / (p ^ padicValNat p x.den : ℚ) =
      x.num.natAbs / x.den := by
    -- Substitute the prime factorizations into the ratio $x.num.natAbs / x.den$.
    nth_rw 2 [← prod1, ← prod2]
    -- Distribute the division over the product: $\frac{\prod a_i}{\prod b_i} = \prod \frac{a_i}{b_i}$.
    simp only [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_pow]
  -- Relate the product of $(p : \mathbb{Q})^{\text{padicValRat } p x}$ to the ratio $x.num.natAbs / x.den$.
  have eq2 : ∏ p ∈ Finset.filter Nat.Prime (Finset.range m),
      (p : ℚ) ^ padicValRat p x = x.num.natAbs / x.den := by
    -- Replace the product of ratios with the product of powers using the previous lemma.
    rw [← eq1]
    -- Show term-wise equality inside the product using the lemma `Rat.pow_padiv`.
    refine Finset.prod_congr rfl ?_
    simp only [Finset.mem_filter, Finset.mem_range, and_imp]
    -- Apply `Rat.pow_padiv` to each term in the product, using the fact that $p$ is prime hence $p \neq 0$.
    exact fun p hp₁ hp₂ ↦ Rat.pow_padiv (Nat.Prime.ne_zero hp₂)
  -- Use the definition of the absolute value of a rational number: $|x| = \frac{|x.num|}{|x.den|} = \frac{x.num.natAbs}{x.den}$.
  have eq3 : |x| = x.num.natAbs / x.den := by
    rw [Rat.abs_def, (Rat.natCast_div_eq_divInt x.num.natAbs x.den).symm]
  -- Replace $x.num.natAbs / x.den$ with $|x|$ in the equation to obtain the desired approximation.
  rwa [← eq3] at eq2

include h in
/--The product of $|x|_p$ for primes $p < m$ yields $|x|^{-1}$ for sufficiently large $m$. -/
lemma prod_prime_padicNorm : ∀ m, x.den < m ∧ x.num.natAbs < m →
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range m), padicNorm p x = |x|⁻¹ := by
  -- Rewrite the product using the definition of p-adic norm: $|x|_p = p^{-\text{padicValRat } p x} = (p^{\text{padicValRat } p x})^{-1}$.
  simp only [padicNorm, h, ↓reduceIte, zpow_neg, Finset.prod_inv_distrib, inv_inj]
  -- After simplification, the goal is equivalent to the previous lemma `prod_pow_prime_padicValRat h`.
  exact prod_pow_prime_padicValRat h

include h in
/--If $m$ is coprime to both numerator and denominator (implied by $m > \max(|x.num|, x.den)$ and $m \neq 1$), then $|x|_m = 1$.-/
lemma padicNorm_ne_one {m : ℕ} (hm : m ≠ 1) : x.den < m ∧ x.num.natAbs < m →
    padicNorm m x = 1 := by
  intro hp'
  simp only [padicNorm, h, ↓reduceIte, zpow_neg, inv_eq_one, padicValRat]
  -- $|x|_m = 1 \iff |(m : \mathbb{Q})^{-\text{padicValRat } m x}| = 1 \iff (m : \mathbb{Q})^{-\text{padicValRat } m x} = \pm 1$. Since norm is non-negative, it means $(m : \mathbb{Q})^{-\text{padicValRat } m x} = 1$.
  -- This is equivalent to $-\text{padicValRat } m x = 0 \iff \text{padicValRat } m x = 0 \iff \text{padicValNat } m |x.num| - \text{padicValNat } m x.den = 0$.
  rw [zpow_eq_one_iff_right₀ m.cast_nonneg' (Nat.cast_ne_one.2 hm), sub_eq_zero]
  -- We need to show $\text{padicValNat } m |x.num| = \text{padicValNat } m x.den$.
  congr
  -- If $m > |x.num|$, then $m \nmid x.num$, hence $\text{padicValNat } m |x.num| = 0$.
  have ndvd1 : ¬↑m ∣ x.num := by
    convert_to ¬↑m ∣ x.num.natAbs
    exact Int.ofNat_dvd_left
    exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.2 (Rat.num_ne_zero.2 h)) hp'.2
  -- If $m > x.den$, then $m \nmid x.den$, hence $\text{padicValNat } m x.den = 0$.
  have ndvd2 : ¬m ∣ x.den := Nat.not_dvd_of_pos_of_lt x.den_pos hp'.1
  -- If $m \nmid x.num$ and $m \nmid x.den$, then both valuations are 0.
  rw [padicValInt.eq_zero_of_not_dvd ndvd1, padicValNat.eq_zero_of_not_dvd ndvd2]

/--Define a finset containing all prime numbers less than $m$.-/
def Primes.below (m : ℕ) : Finset Nat.Primes :=
  -- This definition constructs a finset of `Nat.Primes` from `Nat.primesBelow m` (primes below m as natural numbers).
  let inj_fun : { x // x ∈ m.primesBelow } ↪ Nat.Primes := {
    toFun := fun x ↦ ⟨x.val, Nat.prime_of_mem_primesBelow x.property⟩
    inj' := fun _ _ h12 ↦ let_fun this := Subtype.val_inj.mpr h12; Subtype.eq this
  }
  (Nat.primesBelow m).attach.map inj_fun

/--If a prime $p$ is not in $\text{Primes.below } m$, it means $p \ge m$.-/
lemma Primes.below_not_mem_le {m : ℕ} {p : Nat.Primes} : p ∉ (Primes.below m) → m ≤ p := by
  contrapose!
  -- Prove the contrapositive: $p < m \implies p \in \text{Primes.below } m$.
  refine fun hpm ↦ Finset.mem_map.2
    ⟨⟨p.val, Nat.mem_primesBelow.2 ⟨hpm, p.property⟩⟩, ?_⟩
  simp only [Finset.mem_attach, Function.Embedding.coeFn_mk, Subtype.coe_eta, and_self]
  -- This follows directly from the definition of `Primes.below` and `Nat.primesBelow`.

/--If a prime $p$ is in $\text{Primes.below } m$, it means $p < m$.-/
lemma Primes.below_mem_lt {m : ℕ} {p : Nat.Primes} : p ∈ (Primes.below m) → p < m := by
  intro hpa
  obtain ⟨q, ⟨hq1, hq2⟩⟩ := Finset.mem_map.1 hpa
  suffices q < m from lt_of_eq_of_lt (congrArg Subtype.val hq2.symm) this
  exact (Nat.mem_primesBelow.1 q.2).1
  -- This also follows directly from the definition of `Primes.below` and `Nat.primesBelow`.

/--Equivalence: $p \in \text{Primes.below } m$ if and only if $p < m$.-/
lemma Primes.below_prime_mem_iff {m : ℕ} {p : Nat.Primes} :
    p ∈ (Primes.below m) ↔ p < m := by
  -- Prove both directions of the equivalence.
  constructor
  · exact Primes.below_mem_lt -- $p \in \text{Primes.below } m \implies p < m$.
  · contrapose!; exact Primes.below_not_mem_le -- $p < m \implies p \in \text{Primes.below } m$ (by contrapositive).

include h

/--If $p \ge m$ and $m > \max(|x.den|, |x.num.natAbs|)$, then $|x|_p = 1$.-/
lemma Primes.below_not_mem_padicNorm {m : ℕ} {p : Nat.Primes}
    (hm : x.den < m ∧ x.num.natAbs < m) : p ∉ (Primes.below m) → padicNorm p x = 1 := by
  intro hp
  replace hp : m ≤ p := Primes.below_not_mem_le hp
  exact padicNorm_ne_one h p.property.ne_one ⟨(LE.le.trans hm.1 hp), LE.le.trans hm.2 hp⟩
  -- Combine `Primes.below_not_mem_le` and `padicNorm_ne_one` to show $|x|_p = 1$ for primes outside `Primes.below m`.

/--The product of $|x|_p$ throughout $\text{Primes.below } m$ is $|x|^{-1}$-/
lemma prod_primesBelow_padic {m : ℕ} (hm : x.den < m ∧ x.num.natAbs < m) :
    ∏ p ∈ (Primes.below m), padicNorm p x = |x|⁻¹ := by
  -- Rewrite the product over primes in $\text{Primes.below } m$ in terms of $|x|^{-1}$.
  rw [← prod_prime_padicNorm h m hm]
  -- We need to show that the product over `Primes.below m` is the same as the product over `Finset.filter Nat.Prime (Finset.range m)`.
  refine Finset.prod_bij ?_ ?_ ?_ ?_ ?_ (α := ℚ)
  -- Construct a bijection between `Primes.below m` and `Finset.filter Nat.Prime (Finset.range m)`.
  · exact fun p _ ↦ p.val -- Function: `Nat.Primes` -> `ℕ`, map prime structure to natural number value.
  · exact fun p hp ↦
      Finset.mem_filter.2 ⟨Finset.mem_range.2 <| Primes.below_mem_lt hp, p.property⟩
      -- Show that if $p \in \text{Primes.below } m$, then $p.val \in \text{Finset.filter Nat.Prime (Finset.range m)}$.
      -- $p \in \text{Primes.below } m \implies p < m \implies p.val < m \implies p.val \in \text{Finset.range } m$. Also $p.val$ is prime by definition of `Nat.Primes`.
  · exact fun a₁ _ a₂ _ h12 ↦ (Nat.Primes.coe_nat_inj a₁ a₂).mp h12
    -- Injectivity of the map: if $p_1.val = p_2.val$, then $p_1 = p_2$ for $p_1, p_2 \in \text{Primes.below } m$.
  · intro b hb
    have := Finset.mem_filter.1 hb
    exact ⟨⟨b, this.2⟩, ⟨Primes.below_prime_mem_iff.2 (Finset.mem_range.1 this.1), rfl⟩⟩
    -- Surjectivity: for each $b \in \text{Finset.filter Nat.Prime (Finset.range m)}$, there exists $p \in \text{Primes.below } m$ such that $p.val = b$.
    -- If $b \in \text{Finset.filter Nat.Prime (Finset.range m)}$, then $b$ is prime and $b < m$. So $b \in \text{Nat.primesBelow } m$. We can construct $p = \langle b, \text{prime proof}\rangle \in \text{Primes.below } m$.
  · exact fun _ _ ↦ rfl -- Map preserves the value: $\text{padicNorm } p x = \text{padicNorm } (p.val) x$.

/--The infinite product $\prod_{p} |x|_p$ converges.-/
lemma multipliable_padicNorm : Multipliable fun (p : Nat.Primes) ↦ padicNorm p x := by
  simp only [Multipliable, HasProd, nhds, Set.mem_setOf_eq, Filter.tendsto_iInf,
    Filter.tendsto_principal, Filter.eventually_atTop, ge_iff_le, Finset.le_eq_subset, and_imp]
  -- Choose $m$ large enough such that $m > \max(|x.den|, |x.num.natAbs|)$.
  obtain ⟨m , ⟨hden, hnum⟩⟩ := exists_ge_of_linear x.den.succ x.num.natAbs.succ
  refine ⟨|x|⁻¹, fun i i_one i_open ↦ ?_⟩
  refine ⟨(Primes.below m), fun b hab ↦ ?_⟩
  suffices ∏ p ∈ b, padicNorm p x = |x|⁻¹ from this.symm ▸ i_one
  -- Split the product over a finite set $b$ into product over $\text{Primes.below } m$ and the remaining primes.
  have : b = (Primes.below m) ∪ (b \ (Primes.below m)) :=
    (Finset.union_sdiff_of_subset hab).symm
  rw [this, Finset.prod_union, prod_primesBelow_padic h ⟨hden, hnum⟩]
  -- For primes $p \in b \setminus \text{Primes.below } m$, we have $p \ge m$, so $|x|_p = 1$.
  suffices ∏ p ∈ b \ (Primes.below m), padicNorm p x = 1 from by
    rw [this, mul_one]
  refine Finset.prod_eq_one fun p hp ↦ ?_
  exact Primes.below_not_mem_padicNorm h ⟨hden, hnum⟩ (Finset.mem_sdiff.1 hp).2
  exact Finset.disjoint_sdiff
  -- The product over primes $p \ge m$ is 1 because $|x|_p = 1$ for such primes.

/--The set of primes $p$ where $|x|_p \neq 1$ is finite.-/
lemma finsupport_padicNorm :
    (Function.mulSupport fun (p : Nat.Primes) ↦ padicNorm p x).Finite := by
  -- Choose $m$ large enough such that $m > \max(|x.den|, |x.num.natAbs|)$.
  obtain ⟨m , hm⟩ := exists_ge_of_linear x.den.succ x.num.natAbs.succ
  -- The set of primes with $|x|_p \neq 1$ is a subset of $\text{Primes.below } m$, which is finite.
  refine Set.Finite.subset (Primes.below m).finite_toSet
    <| Function.mulSupport_subset_iff.2 fun p ↦ ?_
  contrapose!
  exact Primes.below_not_mem_padicNorm h hm

/--Prove the product formula: $\prod_{p \text{ prime }}|x|_{p} = |x|^{-1}$.-/
lemma tprod_prime_padicNorm : ∏' p : Nat.Primes, padicNorm p x = |x|⁻¹ := by
  -- Choose $m$ large enough such that $m > \max(|x.den|, |x.num.natAbs|)$.
  obtain ⟨m , hm⟩ := exists_ge_of_linear x.den.succ x.num.natAbs.succ
  simp only [tprod_def, multipliable_padicNorm h, ↓reduceDIte, finsupport_padicNorm h,
    ↓reduceIte, ← prod_primesBelow_padic h hm]
  -- Reduce the infinite product to a finite product over the finset `Primes.below m` because $|x|_p = 1$ outside this finset.
  refine finprod_eq_finset_prod_of_mulSupport_subset
    (fun (p : Nat.Primes) ↦ padicNorm p x) ?_
  simp only [Function.mulSupport_subset_iff, ne_eq, Finset.mem_coe]
  intro p hp
  by_contra hpa
  exact hp <| Primes.below_not_mem_padicNorm h hm hpa
  -- For $p \notin \text{Primes.below } m$, $|x|_p = 1$, so these terms do not affect the product.
