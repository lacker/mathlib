/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of abelian groups, indexed by a discrete type.
-/
import algebra.direct_sum_monoid

open_locale big_operators

universes u v w u₁

namespace direct_sum

variables {ι : Type v} [decidable_eq ι]
variables {β : ι → Type w} [Π i, add_comm_group (β i)]

instance : add_comm_group (direct_sum ι β) :=
dfinsupp.add_comm_group

instance mk.is_add_group_hom (s : finset ι) : is_add_group_hom (mk β s) :=
{ map_add := λ _ _, dfinsupp.mk_add }

@[simp] lemma mk_neg (s : finset ι) (x) : mk β s (-x) = -mk β s x :=
is_add_group_hom.map_neg _ x

@[simp] lemma mk_sub (s : finset ι) (x y) : mk β s (x - y) = mk β s x - mk β s y :=
is_add_group_hom.map_sub _ x y

instance of.is_add_group_hom (i : ι) : is_add_group_hom (of β i) :=
{ map_add := λ _ _, dfinsupp.single_add }

@[simp] lemma of_neg (i : ι) (x) : of β i (-x) = -of β i x :=
is_add_group_hom.map_neg _ x

@[simp] lemma of_sub (i : ι) (x y) : of β i (x - y) = of β i x - of β i y :=
is_add_group_hom.map_sub _ x y

variables {γ : Type u₁} [add_comm_group γ]
variables (φ : Π i, β i → γ) [Π i, is_add_group_hom (φ i)]

variables (φ)
def to_group (f : direct_sum ι β) : γ := @to_add_monoid _ _ _ _ _ _ φ (λ i, by apply_instance) f
variables {φ}

instance to_group.is_add_group_hom : is_add_group_hom (to_group φ) :=
{ .. to_add_monoid.is_add_monoid_hom}

variables (φ)
@[simp] lemma to_group_zero : to_group φ 0 = 0 :=
by apply to_add_monoid_zero

@[simp] lemma to_group_add (x y) : to_group φ (x + y) = to_group φ x + to_group φ y :=
by apply to_add_monoid_add

@[simp] lemma to_group_neg (x) : to_group φ (-x) = -to_group φ x :=
is_add_group_hom.map_neg _ x

@[simp] lemma to_group_sub (x y) : to_group φ (x - y) = to_group φ x - to_group φ y :=
is_add_group_hom.map_sub _ x y

@[simp] lemma to_group_of (i) (x : β i) : to_group φ (of β i x) = φ i x :=
by apply to_add_monoid_of

variables (ψ : direct_sum ι β → γ) [is_add_group_hom ψ]

theorem to_group.unique (f : direct_sum ι β) :
  ψ f = @to_group _ _ _ _ _ _ (λ i, ψ ∘ of β i) (λ i, is_add_group_hom.comp (of β i) ψ) f :=
by apply to_add_monoid.unique

-- TODO: generalize to to_add_monoid too
variables (β)
def set_to_set (S T : set ι) (H : S ⊆ T) :
  direct_sum S (β ∘ subtype.val) → direct_sum T (β ∘ subtype.val) :=
to_group $ λ i, of (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩
variables {β}

-- TODO: generalize to to_add_monoid too
instance (S T : set ι) (H : S ⊆ T) : is_add_group_hom (set_to_set β S T H) :=
to_group.is_add_group_hom

end direct_sum
