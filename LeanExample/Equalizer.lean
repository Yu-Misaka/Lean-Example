import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Tactic.Group

-- Show that every monomorphism of Grps is the equalizer of two homomorphisms.

variable {H : Type*} [Group H] {K : Subgroup H}

local notation "X" => H ⧸ K ⊕ Unit -- Define $X$ as the disjoint union of the quotient group $H/K$ and a unit type.

open Classical

/--
Define a function `toFun₀` on $X = H/K \sqcup \{\star\}$ which swaps the identity coset $\llbracket 1 \rrbracket$ with $\star$.
Specifically,
$$
\text{toFun}_0(x) = \begin{cases}
      \star & \text{if } x = \llbracket 1 \rrbracket \\
      x & \text{if } x \in H/K, x \neq \llbracket 1 \rrbracket \\
      \llbracket 1 \rrbracket & \text{if } x = \star
    \end{cases}
$$
-/
noncomputable def toFun₀ : X → X
  | .inl x =>
    if x = ⟦1⟧ then -- If $x$ is the identity coset $\llbracket 1 \rrbracket$ in $H/K$,
      .inr () -- map it to the element in the unit type.
    else
      .inl x -- Otherwise, keep it as is in $H/K$.
  | .inr () => .inl ⟦1⟧ -- Map the element in the unit type to the identity coset $\llbracket 1 \rrbracket$ in $H/K$.

/--
`inv₀` shows that $\text{toFun}_0$ is an involution, i.e., $\text{toFun}_0 \circ \text{toFun}_0 = \text{id}_X$.
-/
lemma inv₀ (x : X) : toFun₀ (toFun₀ x) = x := by
  match x with -- Perform case analysis on $x \in X$.
    | .inl x' =>
      by_cases h : x' = ⟦1⟧ <;> simp only [toFun₀, h, ↓reduceIte] -- Case 1: $x = \text{inl } x'$ where $x' \in H/K$. Subcase 1.1: $x' = \llbracket 1 \rrbracket$. Subcase 1.2: $x' \neq \llbracket 1 \rrbracket$. Simplify using the definition of `toFun₀` and case assumption $h$.
    | .inr () => simp only [toFun₀, ↓reduceIte] -- Case 2: $x = \text{inr } ()$. Simplify using the definition of `toFun₀`.

/--
Define $\rho$ as the permutation of $X$ induced by $\text{toFun}_0$.
Since $\text{toFun}_0$ is an involution, $\rho$ is its own inverse, i.e., $\rho = \rho^{-1}$.
In terms of function, $\rho = \text{toFun}_0$.
-/
noncomputable def ρ : Equiv.Perm X := ⟨toFun₀, toFun₀, inv₀, inv₀⟩

/--
Define a function $\text{toFun}_1(h) : X \to X$ for each $h \in H$.
It acts on $H/K$ by left multiplication by $h$ and fixes the element in the unit type.
Specifically,
$$
\text{toFun}_1(h)(x) = \begin{cases}
      \llbracket h \cdot x.out \rrbracket & \text{if } x \in H/K \\
      \star & \text{if } x = \star
    \end{cases}
$$
where $x.out$ is a representative of the coset $x$.
-/
noncomputable def toFun₁ (h : H) : X → X
  | .inl x => .inl ⟦h * x.out⟧ -- For $x \in H/K$, map it to $h \cdot x$ in $H/K$ by left multiplication.
  | .inr () => .inr () -- For the element in the unit type, keep it unchanged.

/--
Define a function $\text{inv}_1(h) : X \to X$ for each $h \in H$.
It acts on $H/K$ by left multiplication by $h^{-1}$ and fixes the element in the unit type.
This is intended to be the inverse of $\text{toFun}_1(h)$.
Specifically,
$$
\text{inv}_1(h)(x) = \begin{cases}
      \llbracket h^{-1} \cdot x.out \rrbracket & \text{if } x \in H/K \\
      \star & \text{if } x = \star
    \end{cases}
$$
where $x.out$ is a representative of the coset $x$.
-/
noncomputable def inv₁ (h : H) : X → X
  | .inl x => .inl ⟦h⁻¹ * x.out⟧ -- For $x \in H/K$, map it to $h^{-1} \cdot x$ in $H/K$ by left multiplication by $h^{-1}$.
  | .inr () => .inr () -- For the element in the unit type, keep it unchanged.


/--
Define `pre_f₁ (h)` as a permutation of $X$ using $\text{toFun}_1(h)$ and $\text{inv}_1(h)$ as forward and inverse functions respectively.
The lemmas `left_inv` and `right_inv` verify that they are indeed inverses of each other, thus `pre_f₁ (h)` is a permutation.
-/
noncomputable def pre_f₁ (h : H) : Equiv.Perm X := {
  toFun S := toFun₁ h S -- Define the forward function as $\text{toFun}_1(h)$.
  invFun S := inv₁ h S -- Define the inverse function as $\text{inv}_1(h)$.
  left_inv x := by -- Prove that $\text{inv}_1(h) \circ \text{toFun}_1(h) = \text{id}_X$.
    simp only [inv₁, toFun₁] -- Simplify using the definitions of $\text{toFun}_1$ and $\text{inv}_1$.
    match x with -- Case analysis on $x \in X$.
      | .inr () => simp only -- Case 1: $x = \text{inr } ()$. Trivial case.
      | .inl x => -- Case 2: $x = \text{inl } x'$ where $x' \in H/K$.
        simp only [Sum.inl.injEq] -- Simplify the equality for `Sum.inl`.
        have h₁ := @QuotientGroup.eq H _ K (h * x.out) -- Use `QuotientGroup.eq` to relate $\llbracket h \cdot x.out \rrbracket$ and its representative.
          (@Quotient.out H (QuotientGroup.leftRel K) ⟦h * x.out⟧)
            |>.1 ((QuotientGroup.out_eq' ⟦h * x.out⟧).symm) -- Use `QuotientGroup.out_eq'` to rewrite $\llbracket h \cdot x.out \rrbracket$ in terms of `Quotient.out`.
        obtain ⟨k, hk⟩ : ∃ k : K, k = (h * x.out)⁻¹ * -- Use `CanLift.prf` to show the existence of $k \in K$ such that $k = (h \cdot x.out)^{-1} \cdot \text{out}(\llbracket h \cdot x.out \rrbracket)$.
          (@Quotient.out H (QuotientGroup.leftRel K) ⟦h * x.out⟧) :=
          CanLift.prf ((h * x.out)⁻¹ * ⟦h * x.out⟧.out) h₁ -- Apply `CanLift.prf` with the appropriate term.
        nth_rw 2 [show x = ⟦x.out⟧ by exact (QuotientGroup.out_eq' x).symm] -- Rewrite $x$ as $\llbracket x.out \rrbracket$ using `QuotientGroup.out_eq'`.
        refine QuotientGroup.eq.mpr ?_ -- Use `QuotientGroup.eq.mpr` to prove equality in the quotient group.
        apply_fun ((h * x.out) * ·) at hk -- Multiply both sides of $hk$ by $h \cdot x.out$ from the left.
        group at hk; rw [← hk] -- Simplify using `group` and rewrite using $hk$.
        group; exact Subgroup.zpow_mem K k.2 (-1) -- Simplify and use the fact that $k \in K$ implies $k^{-1} \in K$.
  right_inv x := by -- Prove that $\text{toFun}_1(h) \circ \text{inv}_1(h) = \text{id}_X$.
    simp only [toFun₁, inv₁] -- Simplify using the definitions of $\text{toFun}_1$ and $\text{inv}_1$.
    match x with -- Case analysis on $x \in X$.
      | .inr () => simp only -- Case 1: $x = \text{inr } ()$. Trivial case.
      | .inl x => -- Case 2: $x = \text{inl } x'$ where $x' \in H/K$.
        simp only [Sum.inl.injEq] -- Simplify the equality for `Sum.inl`.
        have h₁ := @QuotientGroup.eq H _ K (h⁻¹ * x.out) -- Use `QuotientGroup.eq` to relate $\llbracket h^{-1} \cdot x.out \rrbracket$ and its representative.
          (@Quotient.out H (QuotientGroup.leftRel K) ⟦h⁻¹ * x.out⟧)
            |>.1 ((QuotientGroup.out_eq' ⟦h⁻¹ * x.out⟧).symm) -- Use `QuotientGroup.out_eq'` to rewrite $\llbracket h^{-1} \cdot x.out \rrbracket$ in terms of `Quotient.out`.
        obtain ⟨k, hk⟩ : ∃ k : K, k = (h⁻¹ * x.out)⁻¹ * -- Use `CanLift.prf` to show the existence of $k \in K$ such that $k = (h^{-1} \cdot x.out)^{-1} \cdot \text{out}(\llbracket h^{-1} \cdot x.out \rrbracket)$.
          (@Quotient.out H (QuotientGroup.leftRel K) ⟦h⁻¹ * x.out⟧) :=
          CanLift.prf ((h⁻¹ * x.out)⁻¹ * ⟦h⁻¹ * x.out⟧.out) h₁ -- Apply `CanLift.prf` with the appropriate term.
        nth_rw 2 [show x = ⟦x.out⟧ by exact (QuotientGroup.out_eq' x).symm] -- Rewrite $x$ as $\llbracket x.out \rrbracket$ using `QuotientGroup.out_eq'`.
        refine QuotientGroup.eq.mpr ?_ -- Use `QuotientGroup.eq.mpr` to prove equality in the quotient group.
        apply_fun ((h⁻¹ * x.out) * ·) at hk -- Multiply both sides of $hk$ by $h^{-1} \cdot x.out$ from the left.
        group at hk; rw [show h⁻¹ = h ^ (-1 : ℤ) by exact (zpow_neg_one h).symm, ← hk] -- Simplify using `group`, rewrite $h^{-1}$ as $h^{(-1: \mathbb{Z})}$, and rewrite using $hk$.
        group; exact Subgroup.zpow_mem K k.2 (-1) -- Simplify and use the fact that $k \in K$ implies $k^{-1} \in K$.
}

/--
Show that `pre_f₁` maps the identity element of $H$ to the identity permutation of $X$.
This is the first condition for `pre_f₁` to be a group homomorphism.
-/
lemma pre_f₁_one : pre_f₁ (1 : H) (K := K) = 1 := by
  simp only [pre_f₁, toFun₁, one_mul, Quotient.out_eq, inv₁, inv_one] -- Simplify using the definitions and properties of identity element.
  ext x -- Prove equality of permutations by showing they have the same action on every $x \in X$.
  simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq] -- Simplify to compare function application.
  match x with -- Case analysis on $x \in X$.
    | .inr () => simp only -- Case 1: $x = \text{inr } ()$. Trivial case.
    | .inl x => simp only -- Case 2: $x = \text{inl } x'$ where $x' \in H/K$. Trivial case.

/--
Show that `pre_f₁` preserves multiplication, i.e., `pre_f₁ (x * y) = pre_f₁ x * pre_f₁ y`.
Combined with `pre_f₁_one`, this shows that `pre_f₁` is a group homomorphism.
-/
lemma pre_f₁_mul (x y : H) : pre_f₁ (x * y) (K := K) = pre_f₁ x * pre_f₁ y := by
  simp only [pre_f₁, toFun₁, inv₁, mul_inv_rev] -- Simplify using the definitions and properties of inverse of product.
  ext z -- Prove equality of permutations by showing they have the same action on every $z \in X$.
  simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply] -- Simplify to compare function application.
  match z with -- Case analysis on $z \in X$.
    | .inr () => simp only -- Case 1: $z = \text{inr } ()$. Trivial case.
    | .inl z => -- Case 2: $z = \text{inl } z'$ where $z' \in H/K$.
      simp only [Sum.inl.injEq] -- Simplify the equality for `Sum.inl`.
      refine QuotientGroup.eq.2 ?_ -- Use `QuotientGroup.eq.2` to prove equality in the quotient group.
      group -- Simplify using `group` tactic.
      rw [show z.out ^ (-1 : ℤ) * y ^ (-1 : ℤ) = (y * z.out)⁻¹ by group] -- Rewrite using group properties.
      refine QuotientGroup.eq.1 ?_ -- Use `QuotientGroup.eq.1` to prove equality in the quotient group.
      exact (QuotientGroup.out_eq' ⟦y * z.out⟧).symm -- Use `QuotientGroup.out_eq'` to rewrite in terms of `Quotient.out`.


/--
Define $f_1 : H \to \text{Perm}(X)$ as the group homomorphism induced by `pre_f₁`.
This is the first homomorphism we construct.
-/
noncomputable def f₁ : H →* Equiv.Perm X := {
  toFun := pre_f₁ -- Define the underlying function as `pre_f₁`.
  map_one' := pre_f₁_one -- Use `pre_f₁_one` to prove the identity map condition.
  map_mul' := pre_f₁_mul -- Use `pre_f₁_mul` to prove the multiplication preserving condition.
}

/--
Define `pre_f₂ (h)` by conjugating `pre_f₁ (h)` with $\rho$, i.e., $\text{pre_f}_2(h) = \rho \circ \text{pre_f}_1(h) \circ \rho^{-1}$.
Since $\rho = \rho^{-1}$, we have $\text{pre_f}_2(h) = \rho \circ \text{pre_f}_1(h) \circ \rho$.
-/
noncomputable def pre_f₂ (h : H) : Equiv.Perm X := (ρ.trans (pre_f₁ h)).trans ρ⁻¹

/--
Define $f_2 : H \to \text{Perm}(X)$ as the group homomorphism induced by `pre_f₂`.
This is the second homomorphism we construct, obtained by conjugating $f_1$ by $\rho$.
-/
noncomputable def f₂ : H →* Equiv.Perm X := {
  toFun := pre_f₂ -- Define the underlying function as `pre_f₂`.
  map_one' := by -- Prove the identity map condition.
    simp only [pre_f₂, pre_f₁_one, Equiv.Perm.trans_one, Equiv.Perm.self_trans_inv] -- Simplify using the properties of identity and conjugation.
  map_mul' x y := by -- Prove the multiplication preserving condition.
    simp only [pre_f₂, pre_f₁_mul] -- Simplify using the definition of `pre_f₂` and the homomorphism property of `pre_f₁`.
    ext z -- Prove equality of permutations by showing they have the same action on every $z \in X$.
    simp only [Equiv.trans_apply, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.coe_trans,
      Equiv.Perm.apply_inv_self] -- Simplify to compare function application and using properties of composition and inverse.
}

/--
If $x \in K$, then $\llbracket x \cdot \text{out}(\llbracket 1 \rrbracket) \rrbracket = \llbracket 1 \rrbracket$ in $H/K$.
This lemma shows one direction of the condition for $x \in K$ in terms of quotient group.
-/
lemma foo (x : H) (hx : x ∈ K) : @Quotient.mk H (QuotientGroup.leftRel K)
    (x * (@Quotient.mk H (QuotientGroup.leftRel K) 1).out) = ⟦1⟧ := by
  refine QuotientGroup.eq.2 ?_ -- Use `QuotientGroup.eq.2` to prove equality in the quotient group.
  simp only [mul_inv_rev, mul_one] -- Simplify using properties of inverse and identity.
  refine mul_mem ?_ ?_ -- Use `mul_mem` to show membership in $K$.
  · have := @QuotientGroup.eq H _ K -- Use `QuotientGroup.eq` to relate $\llbracket 1 \rrbracket$ and its representative.
      (@Quotient.out H (QuotientGroup.leftRel K) ⟦1⟧) 1 |>.1
      (QuotientGroup.out_eq' ⟦1⟧) -- Use `QuotientGroup.out_eq'` to rewrite $\llbracket 1 \rrbracket$ in terms of `Quotient.out`.
    rwa [mul_one] at this -- Rewrite using multiplication by identity.
  · exact inv_mem hx -- Use the assumption $hx : x \in K$ and the property that subgroup is closed under inverse.

/--
If $\llbracket x \cdot \text{out}(\llbracket 1 \rrbracket) \rrbracket = \llbracket 1 \rrbracket$ in $H/K$, then $x \in K$.
This lemma shows the other direction of the condition for $x \in K$ in terms of quotient group.
Combined with `foo`, it gives a characterization of $x \in K$.
-/
lemma foo' (x : H) (hx : @Quotient.mk H (QuotientGroup.leftRel K)
    (x * (@Quotient.mk H (QuotientGroup.leftRel K) 1).out) = ⟦1⟧) : x ∈ K := by
  have base := QuotientGroup.eq.1 hx -- Use `QuotientGroup.eq.1` to extract the condition for equality in quotient group.
  have := @QuotientGroup.eq H _ K -- Use `QuotientGroup.eq` to relate $\llbracket 1 \rrbracket$ and its representative.
    (@Quotient.out H (QuotientGroup.leftRel K) ⟦1⟧) 1 |>.1
    (QuotientGroup.out_eq' ⟦1⟧) -- Use `QuotientGroup.out_eq'` to rewrite $\llbracket 1 \rrbracket$ in terms of `Quotient.out`.
  rw [mul_one] at this base -- Rewrite using multiplication by identity.
  apply inv_mem at base -- Apply `inv_mem` to use the closure under inverse in subgroup.
  rw [inv_inv] at base -- Simplify using inverse of inverse.
  have := mul_mem base this -- Use `mul_mem` to show membership in $K$.
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this -- Simplify using associativity, inverse cancellation, and identity.

/--
Show that the subgroup $K$ is the equalizer of the two homomorphisms $f_1$ and $f_2$.
That is, $K = \{h \in H \mid f_1(h) = f_2(h)\}$.
This completes the proof that every subgroup is an equalizer of two homomorphisms into a permutation group.
-/
lemma eq_of_f₁_f₂ : K.carrier = {h : H | f₁ h (K := K) = f₂ h} := by
  ext x -- Prove set equality by showing mutual inclusion.
  simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
    Set.mem_setOf_eq] -- Simplify set membership notations.
  constructor -- Prove both directions of inclusion.
  · intro hx -- Assume $x \in K$.
    simp only [f₁, MonoidHom.coe_mk, OneHom.coe_mk, pre_f₁, toFun₁, f₂, pre_f₂] -- Simplify using definitions of $f_1, f_2, \text{pre_f}_1, \text{pre_f}_2, \text{toFun}_1$.
    ext z -- Show that $f_1(x)$ and $f_2(x)$ are the same permutation by checking their action on every $z \in X$.
    simp only [Equiv.coe_fn_mk, Equiv.trans_apply] -- Simplify function application notations.
    match z with -- Case analysis on $z \in X$.
      | .inr () => -- Case 1: $z = \text{inr } ()$.
        simp only [ρ, Equiv.coe_fn_mk, toFun₀] -- Simplify using definition of $\rho$ and $\text{toFun}_0$.
        show @Sum.inr (H ⧸ K) Unit () = toFun₀ (Sum.inl (@Quotient.mk H (QuotientGroup.leftRel K) (x * ⟦1⟧.out))) -- Goal becomes showing equality after applying definitions.
        simp only [toFun₀, foo x hx, ↓reduceIte] -- Simplify using definition of $\text{toFun}_0$ and lemma `foo` with $x \in K$.
      | .inl z => -- Case 2: $z = \text{inl } z'$ where $z' \in H/K$.
        simp only [ρ, Equiv.coe_fn_mk, toFun₀] -- Simplify using definition of $\rho$ and $\text{toFun}_0$.
        show Sum.inl ⟦x * Quotient.out z⟧ = toFun₀ ( -- Goal becomes showing equality after applying definitions.
            match if z = ⟦1⟧ then Sum.inr () else Sum.inl z with
              | Sum.inl x_1 => Sum.inl ⟦x * Quotient.out x_1⟧
              | Sum.inr PUnit.unit => Sum.inr ())
        simp only [toFun₀] -- Simplify using definition of $\text{toFun}_0$.
        by_cases hone : z = ⟦1⟧ -- Subcase 2.1: $z = \llbracket 1 \rrbracket$.
        · simp only [hone, foo x hx, ↓reduceIte] -- Simplify using case assumption, lemma `foo` with $x \in K$, and definition of $\text{toFun}_0$.
        · simp only [hone, ↓reduceIte] -- Subcase 2.2: $z \neq \llbracket 1 \rrbracket$. Simplify using case assumption and definition of $\text{toFun}_0$.
          have : ¬ @Quotient.mk H (QuotientGroup.leftRel K) (x * z.out) = ⟦1⟧ := by -- Need to show $\llbracket x \cdot z.out \rrbracket \neq \llbracket 1 \rrbracket$ when $z \neq \llbracket 1 \rrbracket$ and $x \in K$ and $z \neq \llbracket 1 \rrbracket$.
            by_contra hnot -- Proof by contradiction. Assume $\llbracket x \cdot z.out \rrbracket = \llbracket 1 \rrbracket$.
            apply QuotientGroup.eq.1 at hnot -- Use `QuotientGroup.eq.1` to extract condition for equality in quotient group.
            rw [mul_one] at hnot -- Simplify using multiplication by identity.
            apply inv_mem at hnot -- Use closure under inverse in subgroup.
            rw [inv_inv, mul_mem_cancel_left hx] at hnot -- Simplify using inverse of inverse and cancelation with $x \in K$.
            absurd hone -- Contradiction with the assumption $z \neq \llbracket 1 \rrbracket$.
            rw [← QuotientGroup.out_eq' z] -- Rewrite $z$ as $\llbracket z.out \rrbracket$.
            refine QuotientGroup.eq.2 ?_ -- Use `QuotientGroup.eq.2` to prove equality in quotient group.
            rw [mul_one] -- Simplify using multiplication by identity.
            exact inv_mem hnot -- Use closure under inverse in subgroup.
          simp only [this, ↓reduceIte] -- Simplify using the proven inequality and definition of $\text{toFun}_0$.
  · intro h -- Assume $f_1(x) = f_2(x)$.
    simp only [f₁, MonoidHom.coe_mk, OneHom.coe_mk, pre_f₁, toFun₁, f₂, pre_f₂] at h -- Simplify using definitions of $f_1, f_2, \text{pre_f}_1, \text{pre_f}_2, \text{toFun}_1$.
    replace h := (Equiv.ext_iff.1 h) (Sum.inr ()) -- Apply extensionality of equivalences and consider action on $\text{inr } ()$.
    simp only [Equiv.coe_fn_mk, ρ, Equiv.trans_apply, toFun₀] at h -- Simplify using definitions of $\rho$ and $\text{toFun}_0$.
    replace h : Sum.inr () = toFun₀ (Sum.inl (@Quotient.mk H (QuotientGroup.leftRel K) (x * (@Quotient.out H (QuotientGroup.leftRel K) ⟦1⟧)))) := h -- Rewrite the goal.
    simp only [toFun₀] at h -- Simplify using definition of $\text{toFun}_0$.
    by_cases hone : (@Quotient.mk H (QuotientGroup.leftRel K) (x * (@Quotient.mk H (QuotientGroup.leftRel K) 1).out)) = (@Quotient.mk H (QuotientGroup.leftRel K) 1) -- Case analysis on whether $\llbracket x \cdot \text{out}(\llbracket 1 \rrbracket) \rrbracket = \llbracket 1 \rrbracket$.
    · exact foo' x hone -- If $\llbracket x \cdot \text{out}(\llbracket 1 \rrbracket) \rrbracket = \llbracket 1 \rrbracket$, use lemma `foo'` to conclude $x \in K$.
    · simp only [hone, ↓reduceIte, reduceCtorEq] at h -- If $\llbracket x \cdot \text{out}(\llbracket 1 \rrbracket) \rrbracket \neq \llbracket 1 \rrbracket$, simplify using case assumption and definition of $\text{toFun}_0$.
