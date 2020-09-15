/-
-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.finite_products
import category_theory.limits.preserves.shapes

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

TODO: provide the dual result.
-/

open category_theory
open opposite

namespace category_theory.limits

universes v u u₂
variables {C : Type u} [category.{v} C]

variables {J : Type v} [small_category J]

-- We hide the "implementation details" inside a namespace
namespace has_limit_of_has_products_of_has_equalizers

variables {F : J ⥤ C}
          {c₁ : fan F.obj}
          {c₂ : fan (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2)}
          (s t : c₁.X ⟶ c₂.X)
          (hs : ∀ (f : Σ p : J × J, p.1 ⟶ p.2), s ≫ c₂.π.app f = c₁.π.app f.1.1 ≫ F.map f.2)
          (ht : ∀ (f : Σ p : J × J, p.1 ⟶ p.2), t ≫ c₂.π.app f = c₁.π.app f.1.2)
          (i : fork s t)

include hs ht
@[simps]
def build_limit : cone F :=
{ X := i.X,
  π := { app := λ j, i.ι ≫ c₁.π.app _,
         naturality' := λ j₁ j₂ f, by { dsimp, simp [← hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] } } }

variable {i}
def built_is_limit (t₁ : is_limit c₁) (t₂ : is_limit c₂) (hi : is_limit i) :
  is_limit (build_limit s t hs ht i) :=
{ lift := λ q,
  begin
    refine hi.lift (fork.of_ι _ _),
    refine t₁.lift (limits.fan.mk (λ j, _)),
    apply q.π.app j,
    apply t₂.hom_ext,
    simp [hs, ht],
  end,
  uniq' := λ q m w, hi.hom_ext (i.equalizer_ext (t₁.hom_ext (by simpa using w))) }

end has_limit_of_has_products_of_has_equalizers

open has_limit_of_has_products_of_has_equalizers

/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
lemma has_limit_of_equalizer_and_product (F : J ⥤ C)
  [has_limit (discrete.functor F.obj)]
  [has_limit (discrete.functor (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2))]
  [has_equalizers C] : has_limit F :=
has_limit.mk
{ cone := _,
  is_limit :=
    built_is_limit
      (pi.lift (λ f, limit.π _ _ ≫ F.map f.2))
      (pi.lift (λ f, limit.π _ f.1.2))
      (by simp)
      (by simp)
      (limit.is_limit _)
      (limit.is_limit _)
      (limit.is_limit _) }

/--
Any category with products and equalizers has all limits.

See https://stacks.math.columbia.edu/tag/002N.
-/
lemma limits_from_equalizers_and_products
  [has_products C] [has_equalizers C] : has_limits C :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI has_limit_of_equalizer_and_product F } }

/--
Any category with finite products and equalizers has all finite limits.

See https://stacks.math.columbia.edu/tag/002O.
(We do not prove equivalence with the third condition.)
-/
lemma finite_limits_from_equalizers_and_finite_products
  [has_finite_products C] [has_equalizers C] : has_finite_limits C :=
λ J _ _, { has_limit := λ F, by exactI has_limit_of_equalizer_and_product F }

variables {D : Type u₂} [category.{v} D]
variables [has_limits_of_shape (discrete J) C]
          [has_limits_of_shape (discrete (Σ p : J × J, p.1 ⟶ p.2)) C]
          [has_equalizers C]
variables (G : C ⥤ D)
          [preserves_limits_of_shape walking_parallel_pair G]
          [preserves_limits_of_shape (discrete J) G]
          [preserves_limits_of_shape (discrete (Σ p : J × J, p.1 ⟶ p.2)) G]

-- noncomputable def preserves_limit_of_preserves_equalizers_and_product :
--   preserves_limits_of_shape J G :=
-- { preserves_limit := λ K,
--   preserves_limit_of_preserves_limit_cone
--   (built_is_limit
--     (pi.lift (λ f, limit.π _ _ ≫ K.map f.2))
--     (pi.lift (λ f, limit.π _ f.1.2))
--     (by simp)
--     (by simp)
--     (limit.is_limit _) (limit.is_limit _) (limit.is_limit _))
--   begin
--     -- apply built_is_limit _ _ _ _ _ _ _,
--     apply is_limit.of_iso_limit (built_is_limit _ _ _ _ _ _ _) _,
--     -- { exact fan.mk (λ j, G.map (pi.π _ j)) },
--     -- { exact fan.mk (λ j, G.map (pi.π _ _)) },

--     -- sorry,
--     -- -- { exact is_limit.lift (preserves_limit.preserves (limit.is_limit (discrete.functor K.obj))) { X := G.obj (pi_obj K.obj), π := { app := λ j, G.map (limit.π (discrete.functor K.obj) j) } } },
--     -- sorry,
--     -- -- { refine
--     -- --     is_limit.lift
--     -- --       (preserves_limit.preserves (limit.is_limit (discrete.functor K.obj)))
--     -- --       { X := G.obj _, π := { app := λ j, G.map (limit.π _ _) } } },
--     -- rintro ⟨⟨j₁, j₂⟩, f⟩,
--     -- dsimp,
--     -- sorry,
--     -- rintro ⟨⟨j₁, j₂⟩, f⟩,
--     -- dsimp,

--   end

-- }

end category_theory.limits
