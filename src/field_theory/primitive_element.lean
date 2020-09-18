/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.adjoin
import field_theory.separable

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `primitive_element`: a finite separable extension has a primitive element.

-/

noncomputable theory
open_locale classical

/- Proof of the primitive element theorem. -/

open finite_dimensional

namespace field

section

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

/-! ### Primitive element theorem for finite fields -/

/-- Primitive element theorem assuming E is finite. -/
lemma primitive_element_fin_aux [fintype E] : ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  obtain ⟨α, hα⟩ := is_cyclic.exists_generator (units E),
  use α,
  ext,
  rw iff_true_right algebra.mem_top,
  by_cases hx : x = 0,
  { rw hx,
    exact F⟮α.val⟯.zero_mem, },
  { obtain ⟨n, hn⟩ := set.mem_range.mp (hα (units.mk0 x hx)),
    rw (show x = α^n, by { norm_cast, simp * }),
    exact @is_subfield.pow_mem E _ α.val n F⟮α.val⟯ _ (field.mem_adjoin_simple_self F α.val), },
end

/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem primitive_element_fin [fintype F] [hfd : finite_dimensional F E] :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  haveI : fintype E := finite_dimensional.finite_of_findim_over_finite F E,
  exact primitive_element_fin_aux F,
end

end

section

variables {F : Type*} [field F] {E : Type*} [field E] (ϕ : F →+* E)

/-! ### Primitive element theorem for infinite fields -/

lemma primitive_element_two_inf_exists_c (α β : E) (f g : polynomial F) [F_inf : infinite F] :
  ∃ c : F, ∀ (α' ∈ (f.map ϕ).roots) (β' ∈ (g.map ϕ).roots), -(α' - α)/(β' - β) ≠ ϕ c :=
begin
  let sf := (f.map ϕ).roots,
  let sg := (g.map ϕ).roots,
  let s := (sf.bind (λ α', sg.map (λ β', -(α' - α) / (β' - β)))).to_finset,
  let s' := s.preimage ϕ (λ x hx y hy h, ϕ.injective h),
  obtain ⟨c, hc⟩ := infinite.exists_not_mem_finset s',
  simp_rw [finset.mem_preimage, multiset.mem_to_finset, multiset.mem_bind, multiset.mem_map] at hc,
  push_neg at hc,
  exact ⟨c, hc⟩,
end

lemma polynomial.linear_of_splits_single_root {β : F} {h : polynomial F}
  (h_splits : polynomial.splits ϕ h) (h_roots : (h.map ϕ).roots = {ϕ β}) :
  h = (polynomial.C (polynomial.leading_coeff h)) * (polynomial.X - polynomial.C β) :=
begin
  apply polynomial.map_injective _ ϕ.injective,
  rw [polynomial.eq_prod_roots_of_splits h_splits,h_roots,multiset.map_singleton,
      multiset.singleton_eq_singleton,multiset.prod_singleton,polynomial.map_mul,
      polynomial.map_sub,polynomial.map_X,polynomial.map_C,polynomial.map_C],
end

lemma polynomial.linear_of_splits_separable_root {β : F} {h : polynomial F} (h_ne_zero : h ≠ 0)
  (h_sep : h.separable) (h_root : h.eval β = 0) (h_splits : polynomial.splits ϕ h)
  (h_roots : ∀ x ∈ (h.map ϕ).roots, x = ϕ β) :
  h = (polynomial.C (polynomial.leading_coeff h)) * (polynomial.X - polynomial.C β) :=
begin
  apply polynomial.linear_of_splits_single_root ϕ h_splits,
  apply finset.mk.inj,
  { change _ = {ϕ β},
    rw finset.eq_singleton_iff_unique_mem,
    split,
    { apply finset.mem_mk.mpr,
      rw polynomial.mem_roots (show h.map ϕ ≠ 0, by exact polynomial.map_ne_zero h_ne_zero),
      rw [polynomial.is_root.def,←polynomial.eval₂_eq_eval_map,polynomial.eval₂_hom,h_root],
      exact ring_hom.map_zero ϕ },
    { exact h_roots } },
  { exact polynomial.nodup_roots (polynomial.separable.map h_sep) },
end

end

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma primitive_element_two_inf (α β : E) (F_sep : is_separable F E)   (F_inf : infinite F) :
  ∃ γ : E, (F⟮α, β⟯ : set E) ⊆ (F⟮γ⟯ : set E) :=
begin
  rcases F_sep α with ⟨hα, hf⟩,
  rcases F_sep β with ⟨hβ, hg⟩,
  let f := minimal_polynomial hα,
  let g := minimal_polynomial hβ,
  let ιFE := algebra_map F E,
  let g' := g.map ιFE,
  let E' := polynomial.splitting_field g',
  let ιEE' := algebra_map E E',
  let ιFE' := ιEE'.comp(ιFE),
  have key := primitive_element_two_inf_exists_c ιFE' (ιEE' α) (ιEE' β) f g,
  cases key with c hc,
  let γ := α+(ιFE c)*β,
  let f' := (f.map ιFE).comp(polynomial.C γ-(polynomial.C (ιFE c))*(polynomial.X)),
  let h := euclidean_domain.gcd f' g',
  have h_sep : h.separable := polynomial.separable_gcd_right f' g' (polynomial.separable.map hg),
  have h_ne_zero : h ≠ 0,
  { intro h_eq_zero,
    rw euclidean_domain.gcd_eq_zero_iff at h_eq_zero,
    apply polynomial.map_monic_ne_zero (minimal_polynomial.monic hβ) h_eq_zero.2, },
  have h_root : h.eval β = 0,
  { apply polynomial.gcd_eval_zero,
    { rw [polynomial.eval_comp,polynomial.eval_sub,polynomial.eval_mul,polynomial.eval_C,
          polynomial.eval_C,polynomial.eval_X,add_sub_cancel,
          polynomial.eval_map,←polynomial.aeval_def, minimal_polynomial.aeval] },
    { rw [polynomial.eval_map,←polynomial.aeval_def, minimal_polynomial.aeval] } },
  have h_splits : polynomial.splits (algebra_map E E') h :=
    polynomial.splits_of_splits_gcd_right (algebra_map E E')
    (polynomial.map_ne_zero (minimal_polynomial.ne_zero hβ)) (polynomial.splitting_field.splits g'),
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = algebra_map E E' β,
  { intros x hx,
    rw polynomial.mem_roots_of_map h_ne_zero at hx,
    specialize hc ((ιEE' γ) - (ιFE' c) * x) (begin
      rw [polynomial.mem_roots_of_map (minimal_polynomial.ne_zero hα),←polynomial.eval₂_map],
      have f_root : f'.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_left f' g' x hx,
      rw [polynomial.eval₂_comp,polynomial.eval₂_sub,polynomial.eval₂_mul,polynomial.eval₂_C,
          polynomial.eval₂_C,polynomial.eval₂_X] at f_root,
      exact f_root,
    end),
    specialize hc x (begin
      rw [polynomial.mem_roots_of_map (minimal_polynomial.ne_zero hβ),←polynomial.eval₂_map],
      exact polynomial.gcd_root_right f' g' x hx,
    end),
    by_contradiction a,
    apply hc,
    symmetry,
    apply (eq_div_iff (sub_ne_zero.mpr a)).mpr,
    simp only [ring_hom.map_add,ring_hom.map_mul,ring_hom.comp_apply],
    ring, },
  have composition : (algebra_map F⟮γ⟯ E).comp(algebra_map F F⟮γ⟯) = algebra_map F E := by ext;refl,
  have fswap : f' = ((f.map(algebra_map F F⟮γ⟯)).comp
    (polynomial.C (field.adjoin_simple.gen F γ)-(polynomial.C ↑c)*(polynomial.X))).map _,
  { rw [polynomial.map_comp,polynomial.map_map,composition,polynomial.map_sub,polynomial.map_mul,
        polynomial.map_C,polynomial.map_C,polynomial.map_X],
    refl },
  have gswap : g' = (g.map(algebra_map F F⟮γ⟯)).map(algebra_map F⟮γ⟯ E),
  { rw [polynomial.map_map,composition] },
  let p := euclidean_domain.gcd (_ : polynomial F⟮γ⟯) (_ : polynomial F⟮γ⟯),
  have hswap : h = p.map(algebra_map F⟮γ⟯ E),
  { dsimp only [h,p],
    rw[fswap,gswap],
    convert polynomial.gcd_map (algebra_map F⟮γ⟯ E) },
  rw polynomial.linear_of_splits_separable_root ιEE' h_ne_zero h_sep h_root h_splits h_roots at hswap,
  have leading_coeff_ne_zero : h.leading_coeff ≠ 0,
  { intro eq_zero,
    rw [polynomial.leading_coeff_eq_zero,euclidean_domain.gcd_eq_zero_iff] at eq_zero,
    apply polynomial.map_monic_ne_zero (minimal_polynomial.monic hβ) eq_zero.2, },
  have finale : β = algebra_map F⟮γ⟯ E (-p.coeff 0 / p.coeff 1),
  { rw [ring_hom.map_div,ring_hom.map_neg,←polynomial.coeff_map,←polynomial.coeff_map,←hswap,
        polynomial.coeff_C_mul,polynomial.coeff_C_mul,polynomial.coeff_sub,polynomial.coeff_sub,
        polynomial.coeff_X_zero,polynomial.coeff_X_one,polynomial.coeff_C_zero,polynomial.coeff_C,
        zero_sub,mul_neg_eq_neg_mul_symm,neg_neg],
    simp only [one_ne_zero],
    rw [if_false,sub_zero,mul_one,mul_comm,div_eq_mul_inv,mul_assoc,
        mul_inv_cancel leading_coeff_ne_zero,mul_one] },
  have β_in_Fγ : β ∈ F⟮γ⟯,
  { rw finale,
    exact subtype.mem (-p.coeff 0 / p.coeff 1) },
  have γ_in_Fγ : γ ∈ F⟮γ⟯ := field.mem_adjoin_simple_self F γ,
  have c_in_Fγ : ιFE c ∈ F⟮γ⟯ := field.adjoin.algebra_map_mem F {γ} c,
  have cβ_in_Fγ : (ιFE c)*β ∈ (F⟮γ⟯ : set E) := is_submonoid.mul_mem c_in_Fγ β_in_Fγ,
  have α_in_Fγ : α ∈ (F⟮γ⟯ : set E),
  { rw (show α = γ - (ιFE c)*β, by exact (add_sub_cancel α ((ιFE c)*β)).symm),
    exact is_add_subgroup.sub_mem F⟮γ⟯ γ ((ιFE c)*β) γ_in_Fγ cβ_in_Fγ, },
  have αβ_in_Fγ : {α,β} ⊆ (F⟮γ⟯ : set E) := λ x hx, by cases hx; cases hx; cases hx; assumption,
  have Fαβ_sub_Fγ : (F⟮α, β⟯ : set E) ⊆ (F⟮γ⟯ : set E) :=
    (field.adjoin_subset_iff F {α,β}).mp αβ_in_Fγ,
  exact ⟨γ, Fαβ_sub_Fγ⟩,
end

universe u

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf {F E : Type u} [field F] [field E] [algebra F E]
  (F_sep : is_separable F E) (F_findim: finite_dimensional F E) (F_inf : infinite F)
  (n : ℕ) (hn : findim F E = n) :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  tactic.unfreeze_local_instances,
  revert F,
  apply nat.strong_induction_on n,
  clear n,
  intros n ih F hF hFE F_sep F_findim F_inf hn,
  by_cases key : ∃ α : E, findim F⟮α⟯ E < n,
  { cases key with α Fα_le_n,
    have Fα_findim : finite_dimensional F⟮α⟯ E := finite_dimensional.findim_of_tower_findim F F⟮α⟯ E,
    have Fα_inf : infinite F⟮α⟯ := infinite.of_injective _ (algebra_map F F⟮α⟯).injective,
    have Fα_sep : is_separable F⟮α⟯ E := is_separable_top F F⟮α⟯ E F_sep,
    obtain ⟨β, hβ⟩ := ih _ Fα_le_n Fα_sep Fα_findim Fα_inf rfl,
    obtain ⟨γ, hγ⟩ := primitive_element_two_inf α β F_sep F_inf,
    use γ,
    ext1,
    rw iff_true_right algebra.mem_top,
    apply hγ,
    rw [←field.adjoin_simple_adjoin_simple, hβ],
    exact algebra.mem_top, },
  { push_neg at key,
    use 0,
    ext1,
    rw iff_true_right algebra.mem_top,
    specialize key x,
    rw ←hn at key,
    haveI : finite_dimensional F⟮x⟯ E := findim_of_tower_findim F F⟮x⟯ E,
    rw ←findim_mul_findim F F⟮x⟯ E at key,
    have h : findim F F⟮x⟯ = 1 := by nlinarith only
      [key, show 0 < findim F F⟮x⟯, from findim_pos, show 0 < findim F⟮x⟯ E, from findim_pos],
    replace h := field.adjoin.findim_one F x h,
    rw [algebra.mem_bot,set.mem_range] at h,
    cases h with y hy,
    rw ← hy,
    exact F⟮0⟯.algebra_map_mem y, },
end

/- Actual primitive element theorem. -/

/-- Primitive element theorem in same universe. -/
theorem primitive_element_aux (F E : Type u) [field F] [field E] [algebra F E]
  (F_sep : is_separable F E)  (F_findim : finite_dimensional F E) :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  by_cases F_finite : nonempty (fintype F),
  exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h F_findim),
  exact primitive_element_inf F_sep F_findim (not_nonempty_fintype.mp F_finite) (findim F E) rfl,
end

/-- Primitive element theorem in different universes. -/
theorem primitive_element (F_sep : is_separable F E)  (F_findim : finite_dimensional F E) :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  have F'_sep : is_separable F⟮(0 : E)⟯ E := is_separable_top F F⟮(0 : E)⟯ E F_sep,
  have F'_findim : finite_dimensional F⟮(0 : E)⟯ E :=
    finite_dimensional.findim_of_tower_findim F F⟮(0 : E)⟯ E,
  obtain ⟨α, hα⟩ := primitive_element_aux F⟮(0 : E)⟯ E F'_sep F'_findim,
  use α,
  ext1,
  rw iff_true_right algebra.mem_top,
  rw subalgebra.ext_iff at hα,
  specialize hα x,
  rw iff_true_right algebra.mem_top at hα,
  change x ∈ (↑_ : set E) at hα,
  rw [field.adjoin_simple_comm,field.adjoin_zero] at hα,
  change x ∈ (⊥ : subalgebra F⟮α⟯ E) at hα,
  rw [algebra.mem_bot,set.mem_range] at hα,
  cases hα with y hy,
  rw ←hy,
  cases y,
  assumption,
end

end field
