-- this should all be moved

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import data.zmod.basic
import data.fintype.card
import data.finset.lattice
import data.set.disjointed
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this file should move to other files


-- namespace alg_hom
-- open mv_polynomial

-- note: this has moved to the mv_polynomial namespace, is that reasonable?
-- it also doesn't seem to be used

-- lemma comp_aeval {σ : Type*}
--   {R : Type*} {A : Type*} {B : Type*}
--    [comm_semiring R] [comm_semiring A] [algebra R A] [comm_semiring B] [algebra R B]
--   (f : σ → A) (φ : A →ₐ[R] B) :
--   φ.comp (aeval f) = (aeval (λ i, φ (f i))) :=
-- begin
--   apply mv_polynomial.alg_hom_ext,
--   intros i,
--   rw [comp_apply, aeval_X, aeval_X],
-- end

-- end alg_hom

namespace finset

open_locale classical

@[simp]
lemma fold_union_empty_singleton {α : Type*} (s : finset α) :
  finset.fold (∪) ∅ singleton s = s :=
begin
  apply finset.induction_on s,
  { simp only [fold_empty], },
  { intros a s has ih, rw [fold_insert has, ih, insert_eq], }
end

@[simp]
lemma fold_sup_bot_singleton {α : Type*} (s : finset α) :
  finset.fold (⊔) ⊥ singleton s = s :=
fold_union_empty_singleton s

end finset

namespace mv_polynomial
open finsupp

variables (σ R A : Type*) [comm_semiring R] [comm_semiring A]

@[simp] lemma aeval_zero [algebra R A] (p : mv_polynomial σ R) :
  aeval (0 : σ → A) p = algebra_map _ _ (p.coeff 0) :=
begin
  apply mv_polynomial.induction_on p,
  { simp only [aeval_C, forall_const, if_true, coeff_C, eq_self_iff_true] },
  { intros, simp only [*, alg_hom.map_add, ring_hom.map_add, coeff_add] },
  { intros,
    simp only [coeff_mul_X', pi.zero_apply, ring_hom.map_zero, eq_self_iff_true,
      mem_support_iff, not_true, aeval_X, if_false, ne.def, mul_zero, alg_hom.map_mul, zero_apply] }
end

@[simp] lemma aeval_zero' [algebra R A] (p : mv_polynomial σ R) :
  aeval (λ _, 0 : σ → A) p = algebra_map _ _ (p.coeff 0) :=
aeval_zero σ R A p

open_locale big_operators

lemma C_dvd_iff_dvd_coeff {σ : Type*} {R : Type*} [comm_ring R]
  (r : R) (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ ∀ i, r ∣ (φ.coeff i) :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : (σ →₀ ℕ) → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : mv_polynomial σ R := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    apply mv_polynomial.ext, intro i,
    simp only [coeff_C_mul, coeff_sum, coeff_monomial],
    rw [finset.sum_eq_single i, if_pos rfl],
    { dsimp [c'], split_ifs with hi hi,
      { rw hc },
      { rw finsupp.not_mem_support_iff at hi, rwa [mul_zero] } },
    { intros j hj hji, convert if_neg hji },
    { intro hi, rw [if_pos rfl], exact if_neg hi } }
end

-- Johan: why the hack does ring_hom.ker not exist!!!
-- Rob: it does now, why do you ask here?

lemma C_dvd_iff_map_hom_eq_zero {σ : Type*} {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]
  (q : R →+* S) (hq : function.surjective q) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
  (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ map q φ = 0 :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intro h, apply mv_polynomial.ext, intro i,
    simp only [coeff_map, *, ring_hom.coe_of, coeff_zero], },
  { rw mv_polynomial.ext_iff,
    simp only [coeff_map, *, ring_hom.coe_of, coeff_zero, imp_self] }
end

lemma C_dvd_iff_zmod {σ : Type*} (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map (int.cast_ring_hom (zmod n)) φ = 0 :=
begin
  apply C_dvd_iff_map_hom_eq_zero,
  { exact zmod.int_cast_surjective },
  { exact char_p.int_cast_eq_zero_iff (zmod n) n, }
end

end mv_polynomial

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R S : Type*} [comm_semiring R] [comm_semiring S]
variables (f : R →+* S)
variables (p q : mv_polynomial σ R)

open function
open_locale classical big_operators

section constant_coeff

noncomputable
def constant_coeff : mv_polynomial σ R →+* R :=
{ to_fun := coeff 0,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := coeff_zero _,
  map_add' := coeff_add _ }

-- I think neither direction should be simp.
-- But I one of them must be simp, then: ←
lemma constant_coeff_eq : (constant_coeff : mv_polynomial σ R → R) = coeff 0 := rfl

@[simp]
lemma constant_coeff_C (r : R) :
  constant_coeff (C r : mv_polynomial σ R) = r :=
sorry

@[simp]
lemma constant_coeff_X (i : σ) :
  constant_coeff (X i : mv_polynomial σ R) = 0 :=
sorry

lemma constant_coeff_monomial (d : σ →₀ ℕ) (r : R) :
  constant_coeff (monomial d r) = if d = 0 then r else 0 :=
by rw [constant_coeff_eq, coeff_monomial]

end constant_coeff

section monomial

lemma eval₂_hom_monomial (f : R →+* S) (g : σ → S) (d : σ →₀ ℕ) (r : R) :
  eval₂_hom f g (monomial d r) = f r * d.prod (λ i k, g i ^ k) :=
by simp only [monomial_eq, ring_hom.map_mul, eval₂_hom_C, finsupp.prod,
  ring_hom.map_prod, ring_hom.map_pow, eval₂_hom_X']

lemma aeval_monomial [algebra R S] (g : σ → S) (d : σ →₀ ℕ) (r : R) :
  aeval g (monomial d r) = algebra_map _ _ r * d.prod (λ i k, g i ^ k) :=
eval₂_hom_monomial _ _ _ _

end monomial

section vars

lemma vars_add_subset :
  (p + q).vars ⊆ p.vars ∪ q.vars :=
begin
  sorry
end

lemma vars_add_of_disjoint (h : disjoint p.vars q.vars) :
  (p + q).vars = p.vars ∪ q.vars :=
begin
  sorry
end

section sum
variables {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R)

lemma vars_sum_subset :
  (∑ i in s, φ i).vars ⊆ finset.bind s (λ i, (φ i).vars) :=
begin
  sorry
end

lemma vars_sum_of_disjoint (h : pairwise $ disjoint on (λ i, (φ i).vars)) :
  (∑ i in s, φ i).vars = finset.bind s (λ i, (φ i).vars) :=
begin
  sorry
end

end sum

lemma vars_map : (map f p).vars ⊆ p.vars :=
sorry

lemma vars_map_of_injective (hf : injective f) :
  (map f p).vars = p.vars :=
sorry

lemma vars_monomial_single (i : σ) (e : ℕ) (r : R) (he : e ≠ 0) (hr : r ≠ 0) :
  (monomial (finsupp.single i e) r).vars = {i} :=
by rw [vars_monomial hr, finsupp.support_single_ne_zero he]

lemma eval₂_hom_eq_constant_coeff_of_vars (f : R →+* S) (g : σ → S)
  (p : mv_polynomial σ R) (hp : ∀ i ∈ p.vars, g i = 0) :
  eval₂_hom f g p = f (constant_coeff p) :=
begin
  -- I don't like this proof
  -- revert hp,
  -- generalize hps : p.vars = s,
  -- revert hps,
  -- apply mv_polynomial.induction_on' p,
  -- { intros d r hs hg,
  --   by_cases hr : r = 0,
  --   { simp only [hr, monomial_zero, ring_hom.map_zero] },
  --   { rw vars_monomial hr at hs,
  --     rw [eval₂_hom_monomial, constant_coeff_monomial, finsupp.prod, hs],
  --     split_ifs with h,
  --     { -- TODO: `finsupp.prod_zero_index` is not in the default simp set
  --       simp only [h, mul_one, finset.prod_const_one, finsupp.zero_apply, pow_zero], },
  --     { subst hs,
  --       rw [← finsupp.support_eq_empty, ← ne.def, ← finset.nonempty_iff_ne_empty] at h,
  --       obtain ⟨i, hi⟩ := h,
  --       rw [finset.prod_eq_zero hi, mul_zero, f.map_zero],
  --       simp_rw [finsupp.mem_support_iff] at hi hg,
  --       rw [hg i hi, zero_pow' _ hi], } } },
  -- { intros φ ψ hφ hψ hs, sorry  }
end

lemma aeval_eq_constant_coeff_of_vars [algebra R S] (g : σ → S)
  (p : mv_polynomial σ R) (hp : ∀ i ∈ p.vars, g i = 0) :
  aeval g p = algebra_map _ _ (constant_coeff p) :=
eval₂_hom_eq_constant_coeff_of_vars _ g p hp

end vars

end mv_polynomial


namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [comm_semiring R]

/-- This is an example of a map of “algebraic varieties for dummies” over `R`.
(Not meant in a degrading way. Just that we don'y have any actual varieties in Lean yet.) -/
noncomputable def comap (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) :
  (τ → R) → (σ → R) :=
λ x i, aeval x (f (X i))

@[simp] lemma comap_apply (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) (x : τ → R) (i : σ) :
  comap f x i = aeval x (f (X i)) := rfl

@[simp] lemma comap_id_apply (x : σ → R) : comap (alg_hom.id R (mv_polynomial σ R)) x = x :=
by { funext i, simp only [comap, alg_hom.id_apply, id.def, aeval_X], }

variables (σ R)

lemma comap_id : comap (alg_hom.id R (mv_polynomial σ R)) = id :=
by { funext x, exact comap_id_apply x }

variables {σ R}

lemma comap_comp_apply (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R)
  (g : mv_polynomial τ R →ₐ[R] mv_polynomial υ R) (x : υ → R) :
  comap (g.comp f) x = (comap f) (comap g x) :=
begin
  funext i,
  transitivity (aeval x (aeval (λ i, g (X i)) (f (X i)))),
  { apply eval₂_hom_congr rfl rfl,
    rw alg_hom.comp_apply,
    suffices : g = aeval (λ i, g (X i)), { rw ← this, },
    apply mv_polynomial.alg_hom_ext g,
    intro, rw [aeval_X], },
  { simp only [comap, aeval_eq_eval₂_hom, map_eval₂_hom, alg_hom.comp_apply],
    refine eval₂_hom_congr _ rfl rfl,
    ext r, apply aeval_C },
end

lemma comap_comp (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R)
  (g : mv_polynomial τ R →ₐ[R] mv_polynomial υ R) (x : υ → R) :
  comap (g.comp f) = (comap f) ∘ (comap g) :=
by { funext x, exact comap_comp_apply _ _ _ }

lemma comap_eq_id_of_eq_id (f : mv_polynomial σ R →ₐ[R] mv_polynomial σ R)
  (hf : ∀ φ, f φ = φ) (x : σ → R) :
  comap f x = x :=
by { convert comap_id_apply x, ext1 φ, rw [hf, alg_hom.id_apply] }

noncomputable def comap_equiv (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  (τ → R) ≃ (σ → R) :=
{ to_fun    := comap f,
  inv_fun   := comap f.symm,
  left_inv  := by { intro x, rw [← comap_comp_apply], apply comap_eq_id_of_eq_id, intro,
    simp only [alg_hom.id_apply, alg_equiv.comp_symm], },
  right_inv := by { intro x, rw [← comap_comp_apply], apply comap_eq_id_of_eq_id, intro,
  simp only [alg_hom.id_apply, alg_equiv.symm_comp] }, }

@[simp] lemma comap_equiv_coe (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  (comap_equiv f : (τ → R) → (σ → R)) = comap f := rfl

@[simp] lemma comap_equiv_symm_coe (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  ((comap_equiv f).symm : (σ → R) → (τ → R)) = comap f.symm := rfl

lemma equiv_of_family_aux (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (h : ∀ i, aeval g (f i) = X i) (φ : mv_polynomial σ R) :
  (aeval g) (aeval f φ) = φ :=
begin
  rw ← alg_hom.comp_apply,
  suffices : (aeval g).comp (aeval f) = alg_hom.id _ _,
  { rw [this, alg_hom.id_apply], },
  refine mv_polynomial.alg_hom_ext _ (alg_hom.id _ _) _,
  intro i,
  rw [alg_hom.comp_apply, alg_hom.id_apply, aeval_X, h],
end

noncomputable def equiv_of_family (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R :=
{ to_fun    := aeval f,
  inv_fun   := aeval g,
  left_inv  := equiv_of_family_aux f g hfg,
  right_inv := equiv_of_family_aux g f hgf,
  .. aeval f}

@[simp] lemma equiv_of_family_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  (equiv_of_family f g hfg hgf : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) = aeval f := rfl

@[simp] lemma equiv_of_family_symm_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  ((equiv_of_family f g hfg hgf).symm : mv_polynomial τ R →ₐ[R] mv_polynomial σ R) = aeval g := rfl

@[simp] lemma equiv_of_family_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)
  (φ : mv_polynomial σ R) :
  equiv_of_family f g hfg hgf φ = aeval f φ := rfl

@[simp] lemma equiv_of_family_symm_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)
  (φ : mv_polynomial τ R) :
  (equiv_of_family f g hfg hgf).symm φ = aeval g φ := rfl

-- I think this stuff should move back to the witt_vector file
namespace witt_structure_machine
variable {idx : Type*}
variables (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
variables (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)

noncomputable def structure_polynomial (Φ : mv_polynomial idx R) (t : τ) :
  mv_polynomial (idx × τ) R :=
aeval (λ s : σ, (aeval (λ i, (rename (λ t', (i,t')) (f s)))) Φ) (g t)

include hfg

theorem structure_polynomial_prop (Φ : mv_polynomial idx R) (s : σ) :
  aeval (structure_polynomial f g Φ) (f s) = aeval (λ b, (rename (λ i, (b,i)) (f s))) Φ :=
calc aeval (structure_polynomial f g Φ) (f s) =
      aeval (λ s', aeval (λ b, (rename (prod.mk b)) (f s')) Φ) (aeval g (f s)) :
      by { conv_rhs { rw [aeval_eq_eval₂_hom, map_aeval] },
           apply eval₂_hom_congr _ rfl rfl,
           ext1 r, symmetry, apply eval₂_hom_C, }
... = aeval (λ i, (rename (λ t', (i,t')) (f s))) Φ : by rw [hfg, aeval_X]

include hgf

theorem exists_unique (Φ : mv_polynomial idx R) :
  ∃! (φ : τ → mv_polynomial (idx × τ) R),
    ∀ (s : σ), aeval φ (f s) = aeval (λ i, (rename (λ t', (i,t')) (f s))) Φ :=
begin
  refine ⟨structure_polynomial f g Φ, structure_polynomial_prop _ _ hfg _, _⟩,
  { intros φ H,
    funext t,
    calc φ t = aeval φ (aeval (f) (g t))    : by rw [hgf, aeval_X]
         ... = structure_polynomial f g Φ t : _,
    rw [aeval_eq_eval₂_hom, map_aeval],
    apply eval₂_hom_congr _ _ rfl,
    { ext1 r, exact eval₂_C _ _ r, },
    { funext k, exact H k } }
end

end witt_structure_machine

end mv_polynomial

-- ### end FOR_MATHLIB