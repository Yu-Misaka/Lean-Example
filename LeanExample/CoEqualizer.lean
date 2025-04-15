import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Order.CompletePartialOrder

-- Show that every epimorphism of Grps is the coequalizer of two homomorphisms.

open CategoryTheory Limits

universe u

namespace backend

variable {G H : Type u} [Group G] [Group H]
  (q : G →* H) (hsur : Function.Surjective q)
-- Given two groups $G$ and $H$, and a surjective group homomorphism $q : G \to H$.
-- Surjectivity `hsur` is crucial as it implies that $q$ is an epimorphism in Grp.

/--
Define the subgroup $I$ of $G \times G$ as the kernel pair of $q$.
The kernel pair of $q$ consists of all pairs $(g_1, g_2) \in G \times G$ such that $q(g_1) = q(g_2)$.
This subgroup will serve as the domain of the parallel pair of homomorphisms whose coequalizer we will construct.
-/
def I : Subgroup (G × G) := {
  carrier := {g : G × G | q g.1 = q g.2} -- The carrier of $I$ is the set of pairs $(g_1, g_2)$ in $G \times G$ satisfying $q(g_1) = q(g_2)$.
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, map_mul, Prod.snd_mul] at ha hb ⊢ -- Unfold the definitions and apply homomorphism property for multiplication.
    rw [ha, hb] -- Use the conditions $q(a.1) = q(a.2)$ and $q(b.1) = q(b.2)$ from hypotheses `ha` and `hb`.
    -- If $q(a_1) = q(a_2)$ and $q(b_1) = q(b_2)$, then $q(a_1b_1) = q(a_1)q(b_1) = q(a_2)q(b_2) = q(a_2b_2)$.
  one_mem' := by
    simp only [Set.mem_setOf_eq, Prod.fst_one, map_one, Prod.snd_one] -- Unfold definitions and use homomorphism property for identity.
    -- $q(1_G) = 1_H = q(1_G)$, so $(1_G, 1_G) \in I$.
  inv_mem' {a} ha := by
    simpa only [Set.mem_setOf_eq, Prod.fst_inv, map_inv, Prod.snd_inv, inv_inj] -- Unfold definitions and use homomorphism property for inverse and injectivity of inverse.
    -- If $q(a_1) = q(a_2)$, then $q(a_1^{-1}) = q(a_1)^{-1} = q(a_2)^{-1} = q(a_2^{-1})$.
}

/--
Define the first projection homomorphism $\pi_1 : I \to G$.
This homomorphism projects a pair $(g_1, g_2) \in I$ to its first component $g_1$.
-/
def π₁ : (I q) →* G :=
  (MonoidHom.fst G G).comp (Subgroup.subtype (I q))
  -- $\pi_1$ is the composition of the first projection from $G \times G$ to $G$ and the inclusion of $I$ into $G \times G$.

/--
Define the second projection homomorphism $\pi_2 : I \to G$.
This homomorphism projects a pair $(g_1, g_2) \in I$ to its second component $g_2$.
-/
def π₂ : (I q) →* G :=
  (MonoidHom.snd G G).comp (Subgroup.subtype (I q))
  -- $\pi_2$ is the composition of the second projection from $G \times G$ to $G$ and the inclusion of $I$ into $G \times G$.

local notation "G'" => Grp.of G
local notation "H'" => Grp.of H
local notation "q'" => Grp.ofHom q
local notation "I'" => Grp.of (I q)
local notation "π₁'" => Grp.ofHom (π₁ q)
local notation "π₂'" => Grp.ofHom (π₂ q)
-- Introduce local notations for objects and morphisms in the category `Grp` for conciseness.
-- `Grp.of` lifts a type with group structure to an object in `Grp`.
-- `Grp.ofHom` lifts a group homomorphism to a morphism in `Grp`.

/--
Prove the coequalizer condition: $\pi_1' \circ q' = \pi_2' \circ q'$.
This shows that $q'$ coequalizes the parallel pair $(\pi_1', \pi_2')$.
In terms of elements, this means for any $(g_1, g_2) \in I$, $q(\pi_1(g_1, g_2)) = q(g_1)$ and $q(\pi_2(g_1, g_2)) = q(g_2)$, and by definition of $I$, $q(g_1) = q(g_2)$.
-/
lemma comp : π₁' ≫ q' = π₂' ≫ q' := by
  ext x -- Use extensionality for group homomorphisms, i.e., check equality pointwise.
  exact x.2 -- For any $x \in I$, by definition of $I$, $q(x.1) = q(x.2)$, which is exactly what we need to show.

/--
Define the regular epimorphism structure for $q'$.
To show that $q'$ is a regular epimorphism, we need to show that it is the coequalizer of its kernel pair $(\pi_1', \pi_2')$.
We use `RegularEpi.mk` which requires us to provide the parallel pair $(\pi_1', \pi_2')$, the coequalizer condition, and prove the universal property of the coequalizer.
-/
noncomputable def regular_epi : RegularEpi q' := {
  W := I' -- Set the object $W$ to be $I'$, the kernel pair of $q'$.
  left := π₁' -- Set the left morphism to be $\pi_1'$, the first projection.
  right := π₂' -- Set the right morphism to be $\pi_2'$, the second projection.
  w := comp q -- Set the coequalizer condition to be the lemma `comp q`, which proves $\pi_1' \circ q' = \pi_2' \circ q'$.
  isColimit := by
    refine Cofork.IsColimit.ofExistsUnique ?_ -- To prove that $q'$ is the coequalizer, we use `Cofork.IsColimit.ofExistsUnique`. This tactic requires us to show the existence and uniqueness of the mediating morphism.
    intro s -- Consider any morphism $s.\pi : H' \to Z'$ in `Grp` that coequalizes $(\pi_1', \pi_2')$, i.e., $\pi_1' \circ s.\pi = \pi_2' \circ s.\pi$.
    simp only [Cofork.ofπ_pt, parallelPair_obj_one, Functor.const_obj_obj, Cofork.π_ofπ] -- Simplify the goal using definitions of cofork and parallel pair.
    have cofork := Cofork.condition s -- Extract the coequalizer condition $\pi_1' \circ s.\pi = \pi_2' \circ s.\pi$ from the cofork `s`.
    replace cofork : ∀ i : I', (π₁' ≫ s.π) i = (π₂' ≫ s.π) i := fun i ↦
      congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom cofork)) i -- Rewrite the categorical equality `cofork` into a pointwise equality for elements of $I'$.
    simp only [I, π₁, Grp.ofHom_comp, π₂, Functor.const_obj_obj, Category.assoc, Grp.hom_comp,
      Grp.hom_ofHom, MonoidHom.coe_comp, MonoidHom.coe_fst,
      Function.comp_apply, MonoidHom.coe_snd, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq,
      Prod.forall] at cofork -- Simplify the pointwise coequalizer condition by unfolding definitions of $\pi_1'$, $\pi_2'$, and compositions.
      -- The condition `cofork` now becomes $\forall (g_1, g_2) \in I$, $s.\pi(q(g_1)) = s.\pi(q(g_2))$. Since $(g_1, g_2) \in I$ means $q(g_1) = q(g_2)$, this condition is trivially true and doesn't seem right.
      -- Let's re-examine `Cofork.condition s`. It is `left ≫ s.π = right ≫ s.π`, which is $\pi_1' \circ s.\pi = \pi_2' \circ s.\pi$.
      -- So the condition is actually $\forall (g_1, g_2) \in I$, $s.\pi(\pi_1'(g_1, g_2)) = s.\pi(\pi_2'(g_1, g_2))$, which means $s.\pi(g_1) = s.\pi(g_2)$ whenever $q(g_1) = q(g_2)$.
    obtain ⟨finv, hinv⟩ := Function.surjective_iff_hasRightInverse.1 hsur -- Since $q$ is surjective, there exists a right inverse `finv` for $q$.
    have hker : q.ker ≤ (Grp.Hom.hom s.π).ker := by
      intro x hx -- Assume $x \in \ker(q)$, i.e., $q(x) = 1$.
      simp only [MonoidHom.mem_ker, parallelPair_obj_one, Functor.const_obj_obj] at hx ⊢ -- Simplify the goal and hypothesis.
      have foo := (cofork x 1) (by rwa [map_one]) -- Apply the coequalizer condition `cofork` to the pair $(x, 1)$. Since $q(x) = 1 = q(1)$, $(x, 1) \in I$.
      simp only [Subgroup.coe_subtype, map_one] at foo -- Simplify the result.
      exact foo -- From $s.\pi(x) = s.\pi(1) = 1$, we have $x \in \ker(s.\pi)$. Thus $\ker(q) \subseteq \ker(s.\pi)$.
    set equiv := MonoidHom.liftOfRightInverse q finv hinv (G₃ := s.pt) with equiv_def -- Define the mediating morphism `equiv` using `MonoidHom.liftOfRightInverse`.
    -- `MonoidHom.liftOfRightInverse q finv hinv G₃ hker` lifts a homomorphism from $G$ to $G_3$ to a homomorphism from $H$ to $G_3$ if the kernel of $q$ is contained in the kernel of the given homomorphism and $q$ has a right inverse. Here $G_3 = s.pt = Z'$, and the homomorphism from $G$ to $Z'$ is $s.\pi$.
    use Grp.ofHom (equiv ⟨(Grp.Hom.hom s.π), hker⟩) -- Lift the homomorphism $s.\pi$ to a homomorphism from $H$ to $Z'$ using `liftOfRightInverse`.
    constructor
    · simp only [parallelPair_obj_one, Functor.const_obj_obj] -- Simplify the goal.
      ext x -- Use extensionality to check equality of homomorphisms.
      simp only [Grp.hom_comp, Grp.hom_ofHom, MonoidHom.coe_comp, Function.comp_apply] -- Simplify compositions.
      have := MonoidHom.liftOfRightInverse_comp_apply q finv hinv ⟨(Grp.Hom.hom s.π), hker⟩ x -- Apply the property of `liftOfRightInverse`: `(liftOfRightInverse q finv hinv f).comp q = f`.
      rwa [← equiv_def] at this -- Rewrite using the definition of `equiv`.
      -- This shows that $q' \circ (\text{Grp.ofHom } equiv) = s.\pi$.
    · intro y hy -- Assume another morphism $y : H' \to Z'$ such that $q' \circ y = s.\pi$.
      have comp_eq : (Grp.Hom.hom y).comp q = Grp.Hom.hom s.π := by
        refine MonoidHom.ext_iff.mpr ?_ -- Use extensionality for monoid homomorphisms.
        exact fun x ↦ (DFunLike.congr (congrArg Grp.Hom.hom (hy.symm)) rfl).symm -- Rewrite the categorical equality $q' \circ y = s.\pi$ to pointwise equality.
        -- `hy` is $q' \circ y = s.\pi$, so `Grp.Hom.hom hy` is `Grp.Hom.hom (q' ≫ y) = Grp.Hom.hom s.\pi`.
        -- `Grp.Hom.hom (q' ≫ y) = (Grp.Hom.hom y).comp (Grp.Hom.hom q') = (Grp.Hom.hom y).comp q`.
        -- So we have `(Grp.Hom.hom y).comp q = Grp.Hom.hom s.\pi`.
      have := MonoidHom.eq_liftOfRightInverse q finv hinv (Grp.Hom.hom s.π) hker (Grp.Hom.hom y) comp_eq -- Apply the uniqueness property of `liftOfRightInverse`: if $f'.comp q = f$, then $f' = \text{liftOfRightInverse } q \text{ finv } \text{ hinv } f$.
      rw [← equiv_def] at this -- Rewrite using the definition of `equiv`.
      exact Grp.hom_ext_iff.mpr this -- Use extensionality for group homomorphisms to conclude $y = \text{Grp.ofHom } equiv$.
      -- This shows the uniqueness of the mediating morphism.
}

end backend

/-- Grp is a category in which every epimorphism is regular.-/
instance : IsRegularEpiCategory Grp := {
  regularEpiOfEpi {X Y} f hsur := by
    -- by using directly the previous lemma
    have := backend.regular_epi (Grp.Hom.hom f) ((Grp.epi_iff_surjective f).mp hsur)
    simp only [Grp.ofHom_hom] at this
    exact Nonempty.intro this
}
