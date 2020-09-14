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
local attribute [instance, priority 100] classical.prop_decidable

/- Proof of the primitive element theorem. -/

open finite_dimensional

namespace field

section

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

/- Primitive element theorem for finite fields. -/

-- Replaces earlier messy proof, courtesy of Aaron Anderson & Markus Himmel on zulip
/-- A finite dimensional vector space over a finite field is finite. -/
def finite_of_findim_over_finite [fintype F] [hE : finite_dimensional F E] : fintype E :=
module.fintype_of_fintype (classical.some_spec (finite_dimensional.exists_is_basis_finset F E) : _)

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
    rw (show x = α^n, by norm_cast; simp *),
    exact @is_subfield.pow_mem E _ α.val n F⟮α.val⟯ _ (field.mem_adjoin_simple_self F α.val), },
end

/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem primitive_element_fin [fintype F] [hfd : finite_dimensional F E] :
    ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  haveI : fintype E := finite_of_findim_over_finite F,
  exact primitive_element_fin_aux F,
end

end

/- Primitive element theorem for infinite fields. -/

section
variables {F : Type*} [field F] {E : Type*} [field E] (ϕ : F →+* E)

lemma primitive_element_two_aux (α β : E) (f g : polynomial F) [F_inf : infinite F] :
    ∃ c : F, ∀ (α' ∈ (f.map ϕ).roots) (β' ∈ (g.map ϕ).roots), β' ≠ β → ϕ c ≠ -(α' - α)/(β' - β) :=
begin
  let sf := (f.map ϕ).roots,
  let sg := (g.map ϕ).roots,
  let s := {c : E | ∃ (α' ∈ sf) (β' ∈ sg), β' ≠ β ∧ c = -(α' - α)/(β' - β)},
  let r : E → E → E := λ α' β', -(α' - α)/(β' - β),
  have hr : ∀ c ∈ s, ∃ α' β', ((α' ∈ sf) ∧ (β' ∈ sg)) ∧ r α' β' = c :=
  begin
    intros c hc,
    rw set.mem_set_of_eq at hc,
    tauto,
  end,
  have s_fin : s.finite :=
  begin
    refine (set.finite.image (λ z : E × E, r z.1 z.2) (set.finite_mem_finset (sf.product sg))).subset _,
    simpa only [set.subset_def, set.mem_image, prod.exists, finset.mem_product] using hr,
  end,
  have s'_fin : (ϕ⁻¹' s).finite := s_fin.preimage ((ring_hom.injective ϕ).inj_on (⇑ϕ⁻¹' s)),
  obtain ⟨c, hc⟩ := infinite.exists_not_mem_finset s'_fin.to_finset,
  rw [set.finite.mem_to_finset, set.mem_preimage, set.mem_set_of_eq] at hc,
  push_neg at hc,
  exact ⟨c, hc⟩,
end

lemma primitive_element_two_inf_key_aux {β : F} {h : polynomial F} (h_ne_zero : h ≠ 0) (h_sep : h.separable)
(h_root : h.eval β = 0) (h_splits : polynomial.splits ϕ h) (h_roots : ∀ x ∈ (h.map ϕ).roots, x = ϕ β) :
h = (polynomial.C (polynomial.leading_coeff h)) * (polynomial.X - polynomial.C β) :=
begin
  have map_injective := polynomial.map_injective ϕ ϕ.injective,
  apply map_injective,
  rw polynomial.splits_iff_exists_multiset at h_splits,
  cases h_splits with s hs,
  have h' := @multiset.eq_repeat_of_mem (polynomial E) (polynomial.X - polynomial.C (ϕ β)) (multiset.map (λ (a : E), polynomial.X - polynomial.C a) s)
  begin
    intros x hx,
    rw multiset.mem_map at hx,
    cases hx with a ha,
    rw h_roots a at ha,
    exact ha.2.symm,
    rw polynomial.mem_roots (show polynomial.map ϕ h ≠ 0, by exact polynomial.map_ne_zero h_ne_zero),dsimp[polynomial.is_root],
    cases multiset.exists_cons_of_mem ha.1 with y hy,
    simp[hs,hy],
  end,
  rw [h',multiset.prod_repeat,multiset.card_map] at hs,
  have hf : ¬is_unit (polynomial.X - polynomial.C (ϕ β)) :=
  begin
    rw [polynomial.is_unit_iff_degree_eq_zero,polynomial.degree_X_sub_C],
    exact dec_trivial,
  end,
  have hn : s.card ≠ 0 :=
  begin
    intro hs_card,
    rw [hs_card,pow_zero,mul_one,←polynomial.map_C] at hs,
    replace hs := map_injective hs,
    rw [hs,polynomial.eval_C,polynomial.leading_coeff_eq_zero] at h_root,
    exact h_ne_zero h_root,
  end,
  have h_map_separable : (h.map ϕ).separable := polynomial.separable.map h_sep,
  rw hs at h_map_separable,
  rw [(polynomial.separable.of_pow hf hn (polynomial.separable.of_mul_right h_map_separable)).2,pow_one] at hs,
  simp [hs],
end

end

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma primitive_element_two_inf_key (α β : E) [F_sep : is_separable F E]
  (F_inf : infinite F) : ∃ c : F, β ∈ F⟮α + (algebra_map F E) c * β⟯ :=
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
  have key := primitive_element_two_aux ιFE' (ιEE' α) (ιEE' β) f g,
  cases key with c hc,
  use c,
  let γ := α+(ιFE c)*β,
  change β ∈ F⟮γ⟯,
  let f' := (f.map ιFE).comp(polynomial.C γ-(polynomial.C (ιFE c)) * (polynomial.X)),
  let h := euclidean_domain.gcd f' g',
  have h_sep : h.separable :=
  begin
    cases euclidean_domain.gcd_dvd_right f' g' with p mul,
    dsimp[←h] at mul,
    apply polynomial.separable.of_mul_left,
    rw ←mul,
    exact polynomial.separable.map hg,
  end,
  have h_ne_zero : h ≠ 0 :=
  begin
    intro h_eq_zero,
    rw euclidean_domain.gcd_eq_zero_iff at h_eq_zero,
    apply polynomial.map_monic_ne_zero (minimal_polynomial.monic hβ) h_eq_zero.2,
  end,
  have h_root : h.eval β = 0 :=
  begin
    apply polynomial.gcd_eval_zero,
    rw [polynomial.eval_comp,polynomial.eval_sub,polynomial.eval_mul,polynomial.eval_C,polynomial.eval_C,polynomial.eval_X,add_sub_cancel],
    rw [polynomial.eval_map,←polynomial.aeval_def,minimal_polynomial.aeval],
    rw [polynomial.eval_map,←polynomial.aeval_def,minimal_polynomial.aeval],
  end,
  have h_splits : polynomial.splits (algebra_map E E') h :=
    polynomial.splits_of_splits_of_dvd (algebra_map E E') (polynomial.map_ne_zero (minimal_polynomial.ne_zero hβ)) (polynomial.splitting_field.splits g') (euclidean_domain.gcd_dvd_right f' g'),
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = algebra_map E E' β :=
  begin
    intros x hx,
    rw polynomial.mem_roots (show h.map ιEE' ≠ 0, by exact polynomial.map_ne_zero h_ne_zero) at hx,
    dsimp[polynomial.is_root] at hx,
    rw polynomial.eval_map at hx,
    specialize hc _
    begin
      rw polynomial.mem_roots (show f.map ιFE' ≠ 0, by exact polynomial.map_ne_zero (minimal_polynomial.ne_zero hα)),
      dsimp[polynomial.is_root],
      rw polynomial.eval_map,
      have f_root : f'.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_left f' g' x hx,
      simp only [polynomial.eval₂_map,polynomial.eval₂_comp,polynomial.eval₂_sub,polynomial.eval₂_mul,polynomial.eval₂_C,polynomial.eval₂_X] at f_root,
      exact f_root,
    end,
    specialize hc x
    begin
      rw polynomial.mem_roots (show g.map ιFE' ≠ 0, by exact polynomial.map_ne_zero (minimal_polynomial.ne_zero hβ)),
      dsimp[polynomial.is_root],
      rw polynomial.eval_map,
      have g_root : g'.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_right f' g' x hx,
      simp only [polynomial.eval₂_map] at g_root,
      exact g_root,
    end,
    by_contradiction,
    apply hc a,
    dsimp[ιEE'],
    rw[neg_sub,ring_hom.map_add,←sub_add,←sub_sub,sub_self,zero_sub,neg_add_eq_sub,ring_hom.map_mul,←mul_sub],
    symmetry,
    apply mul_div_cancel,
    rw sub_ne_zero,
    exact a,
  end,
  let p := euclidean_domain.gcd ((f.map(algebra_map F F⟮γ⟯)).comp(polynomial.C (field.adjoin_simple.gen F γ)-(polynomial.C ↑c) * (polynomial.X))) (g.map(algebra_map F F⟮γ⟯)),
  have key : p.map(algebra_map F⟮γ⟯ E) = (polynomial.C (h.leading_coeff)) * (polynomial.X - polynomial.C β) :=
  begin
    rw ←primitive_element_two_inf_key_aux ιEE' h_ne_zero h_sep h_root h_splits h_roots,
    rw ←(show euclidean_domain.gcd _ _ = (euclidean_domain.gcd ((f.map(algebra_map F F⟮γ⟯)).comp(polynomial.C (field.adjoin_simple.gen F γ)-(polynomial.C ↑c) * (polynomial.X))) (g.map(algebra_map F F⟮γ⟯))).map(algebra_map F⟮γ⟯ E), by convert polynomial.gcd_map (algebra_map F⟮γ⟯ E)),
    have composition : (algebra_map F⟮γ⟯ E).comp(algebra_map F F⟮γ⟯) = algebra_map F E := by ext;refl,
    simp[polynomial.map_comp,polynomial.map_map,composition],
    dsimp[h,f',g',γ],
    simp,
    refl,
  end,
  have leading_coeff_ne_zero : h.leading_coeff ≠ 0 :=
  begin
    intro eq_zero,
    rw [polynomial.leading_coeff_eq_zero,euclidean_domain.gcd_eq_zero_iff] at eq_zero,
    apply polynomial.map_monic_ne_zero (minimal_polynomial.monic hβ) eq_zero.2,
  end,
  have finale : β = algebra_map F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) :=
  begin
    simp[ring_hom.map_div,←polynomial.coeff_map,key,polynomial.coeff_C],
    apply eq_div_of_mul_eq leading_coeff_ne_zero,
    exact mul_comm _ _,
  end,
  rw finale,
  exact subtype.mem (-p.coeff 0 / p.coeff 1),
end

/-- Primitive element theorem for adjoining two elements to an infinite field. -/
lemma primitive_element_two_inf (α β : E) (F_sep : is_separable F E)
    (F_inf : infinite F) :  ∃ γ : E, (F⟮α, β⟯ : set E) ⊆ (F⟮γ⟯ : set E) :=
begin
  obtain ⟨c, β_in_Fγ⟩ := primitive_element_two_inf_key α β F_inf,
  let c' := algebra_map F E c,
  let γ := α + c'*β,
  have γ_in_Fγ : γ ∈ F⟮γ⟯ := by simp only [field.mem_adjoin_simple_self],
  have c_in_Fγ : c' ∈ F⟮γ⟯ := by simp only [field.adjoin.algebra_map_mem],
  have cβ_in_Fγ : c'*β ∈ (F⟮γ⟯ : set E) := by simp [is_submonoid.mul_mem, *],
  have α_in_Fγ : α ∈ (F⟮γ⟯ : set E) := by rw (show α = γ - c'*β, by simp *);
    exact is_add_subgroup.sub_mem F⟮γ⟯ γ (c'*β) γ_in_Fγ cβ_in_Fγ,
  have αβ_in_Fγ : {α,β} ⊆ (F⟮γ⟯ : set E) := λ x hx, by cases hx; cases hx; cases hx; assumption,
  have Fαβ_sub_Fγ : (F⟮α, β⟯ : set E) ⊆ (F⟮γ⟯ : set E) := (field.adjoin_subset_iff F {α,β}).mp αβ_in_Fγ,
  exact ⟨γ, Fαβ_sub_Fγ⟩,
end

universe u

lemma nlinarith_lemma (a b : ℕ) (h : a * b ≤ b) (ha : 0 < a) (hb : 0 < b) : a = 1 := by nlinarith

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf (F E : Type u) [field F] [field E] [algebra F E] (F_sep : is_separable F E) (F_findim: finite_dimensional F E)
  (F_inf : infinite F) (n : ℕ) (hn : findim F E = n) : ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  tactic.unfreeze_local_instances,
  revert F,
  apply n.strong_induction_on,
  clear n,
  intros n ih F hF hFE F_sep F_findim F_inf hn,
  by_cases key : ∃ α : E, findim F⟮α⟯ E < n,
  { cases key with α Fα_le_n,
    have Fα_findim : finite_dimensional F⟮α⟯ E := finite_dimensional.findim_of_tower_findim F F⟮α⟯ E,
    have Fα_inf : infinite F⟮α⟯ := infinite.of_injective _ (algebra_map F F⟮α⟯).injective,
    have Fα_sep : is_separable F⟮α⟯ E := is_separable_top F F⟮α⟯ E F_sep,
    obtain ⟨β, hβ⟩ := ih (findim F⟮α⟯ E) Fα_le_n F⟮α⟯ Fα_sep Fα_findim Fα_inf rfl,
    obtain ⟨γ, hγ⟩ := primitive_element_two_inf α β F_sep F_inf,
    use γ,
    ext1,
    rw iff_true_right algebra.mem_top,
    apply hγ,
    rw [←field.adjoin_simple_adjoin_simple,hβ],
    exact algebra.mem_top, },
  { push_neg at key,
    use 0,
    ext1,
    rw iff_true_right algebra.mem_top,
    specialize key x,
    rw ←hn at key,
    haveI : finite_dimensional F⟮x⟯ E := findim_of_tower_findim F F⟮x⟯ E,
    rw ←findim_mul_findim F F⟮x⟯ E at key,
    have h : findim F F⟮x⟯ = 1 := nlinarith_lemma (findim F F⟮x⟯) (findim F⟮x⟯ E) key findim_pos findim_pos,
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
  (∃ α : E, F⟮α⟯ = ⊤) :=
begin
  by_cases F_finite : nonempty (fintype F),
  exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h F_findim),
  exact primitive_element_inf F E F_sep F_findim (not_nonempty_fintype.mp F_finite) (findim F E) rfl,
end

/-- Primitive element theorem in different universes. -/
theorem primitive_element (F_sep : is_separable F E)  (F_findim : finite_dimensional F E) :
  (∃ α : E, F⟮α⟯ = ⊤) :=
begin
  have F'_sep : is_separable F⟮(0 : E)⟯ E := is_separable_top F F⟮(0 : E)⟯ E F_sep,
  have F'_findim : finite_dimensional F⟮(0 : E)⟯ E := finite_dimensional.findim_of_tower_findim F F⟮(0 : E)⟯ E,
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
