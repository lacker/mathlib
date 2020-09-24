/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.giry_monad

/-!
# The product measure space

TODO:

σ-finite measures (is locally finite enough?):
- A measure space (X, B, µ) is σ-finite if X can be expressed as the countable union of sets of
  finite measure

Define product measure
Define finite (and countably infinite) product measure
Fubini's theorem

-/
noncomputable theory
open_locale classical big_operators

namespace function
/-- Evaluation a function to an argument. Useful if you want to talk about the partially applied
  `function.apply i : (Π i, α i) → α i`. -/
@[reducible] def eval {ι} {α : ι → Type*} (i : ι) (f : Π i, α i) : α i := f i

@[simp] lemma eval_apply {ι} {α : ι → Type*} (i : ι) (f : Π i, α i) : eval i f = f i := rfl

example {ι : Type*} {α : ι → Type*} (i : ι) (g : (Π i, α i) → α i) (s : set (Π i, α i)) :
  eval i '' s = g '' s :=
begin
  success_if_fail { simp only [eval_apply] },
  simp, -- why does this simplify?
  sorry
end


end function

open function measure_theory.outer_measure

namespace set
section
variables {ι : Type*} {α : ι → Type*} {s : set ι} {t : Π i, set (α i)}
@[simp] lemma mem_pi {f : Π i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=
by refl

@[simp] lemma mem_pi_univ {f : Π i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i :=
by simp

lemma pi_eq_empty {i : ι} (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
by { ext f, simp only [mem_empty_eq, classical.not_forall, iff_false, mem_pi, classical.not_imp],
     exact ⟨i, hs, by simp [ht]⟩ }

lemma pi_univ_eq_empty {i : ι} (ht : t i = ∅) : pi univ t = ∅ :=
pi_eq_empty (mem_univ i) ht

lemma pi_nonempty_iff : (s.pi t).nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i :=
by simp [classical.skolem, set.nonempty]

lemma pi_univ_nonempty_iff : (pi univ t).nonempty ↔ ∀ i, (t i).nonempty :=
by simp [classical.skolem, set.nonempty]

lemma pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, (α i → false) ∨ (i ∈ s ∧ t i = ∅) :=
begin
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff], push_neg, apply exists_congr, intro i,
  split,
  { intro h, by_cases hα : nonempty (α i),
    { cases hα with x, refine or.inr ⟨(h x).1, by simp [eq_empty_iff_forall_not_mem, h]⟩ },
    { exact or.inl (λ x, hα ⟨x⟩) }},
  { rintro (h|h) x, exfalso, exact h x, simp [h] }
end

lemma pi_univ_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ :=
by simp [← not_nonempty_iff_eq_empty, pi_univ_nonempty_iff]

lemma eval_image_pi {i : ι} (hs : i ∈ s) (ht : (s.pi t).nonempty) : eval i '' s.pi t = t i :=
begin
  ext x, rcases ht with ⟨f, hf⟩, split,
  { rintro ⟨g, hg, rfl⟩, exact hg i hs },
  { intro hg, refine ⟨function.update f i x, _, by simp⟩,
    intros j hj, by_cases hji : j = i,
    { subst hji, simp [hg] },
    { simp at hf, simp [hji, hf, hj] }},
end

@[simp] lemma eval_image_pi_univ {i : ι} (ht : (pi univ t).nonempty) :
  (λ f : Π i, α i, f i) '' pi univ t = t i :=
eval_image_pi (mem_univ i) ht

lemma update_preimage_pi {i : ι} {f : Π i, α i} (hi : i ∈ s)
  (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : (update f i) ⁻¹' s.pi t = t i :=
begin
  ext x, split,
  { intro h, convert h i hi, simp },
  { intros hx j hj, by_cases h : j = i,
    { cases h, simpa },
    { rw [update_noteq h], exact hf j hj h }}
end

lemma update_preimage_pi_univ {i : ι} {f : Π i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
  (update f i) ⁻¹' pi univ t = t i :=
update_preimage_pi (mem_univ i) (λ j _, hf j)

lemma subset_pi_eval_image (s : set ι) (u : set (Π i, α i)) : u ⊆ pi s (λ i, eval i '' u) :=
λ f hf i hi, ⟨f, hf, rfl⟩

end

section
variables {α β : Type*}
-- rename this and set.push_pull'. Ping Patrick Massot
lemma image_inter_preimage {f : α → β} {s : set α} {t : set β} : f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
set.push_pull f s t

lemma image_compl_preimage {f : α → β} {s : set α} {t : set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

end
end set
open set

namespace canonically_ordered_semiring
variables {α : Type*} [canonically_ordered_comm_semiring α]

lemma mul_le_mul_left' {b c : α} (h : b ≤ c) (a : α) : a * b ≤ a * c :=
mul_le_mul (le_refl a) h

lemma mul_le_mul_right' {b c : α} (h : b ≤ c) (a : α) : b * a ≤ c * a :=
mul_le_mul h (le_refl a)

end canonically_ordered_semiring

section monoid_with_zero

@[simp] lemma zero_pow_eq_zero {α} [monoid_with_zero α] [nontrivial α] {n : ℕ} :
  (0 : α) ^ n = 0 ↔ 0 < n :=
begin
  split; intro h,
  { rw [nat.pos_iff_ne_zero], rintro rfl, simpa using h },
  { exact zero_pow' n h.ne.symm }
end


end monoid_with_zero

namespace finset
@[to_additive]
lemma prod_split {α β} [decidable_eq α] [comm_monoid β] (s t : finset α) (f : α → β) :
  (∏ x in s, f x) = (∏ x in s ∩ t, f x) * (∏ x in s \ t, f x) :=
by { convert s.prod_piecewise t f f, simp [finset.piecewise] }

@[to_additive]
lemma prod_split_single {α β} [decidable_eq α] [comm_monoid β] {s : finset α} {i : α} (h : i ∈ s)
  (f : α → β) : (∏ x in s, f x) = f i * (∏ x in s \ {i}, f x) :=
by { convert s.prod_split {i} f, simp [h] }

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
lemma prod_add_prod_eq {α β} [comm_semiring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j)
  (h3 : ∀ j ∈ s, j ≠ i → h j = f j) : ∏ i in s, g i + ∏ i in s, h i = ∏ i in s, f i :=
by { simp_rw [prod_split_single hi, ← h1, right_distrib], congr' 2; apply prod_congr rfl; simpa }

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` is the
  sum of the products of `g` and `h`. -/
lemma prod_univ_add_prod_univ_eq {α β} [fintype α] [comm_semiring β] (i : α) {f g h : α → β}
  (h1 : g i + h i = f i) (h2 : ∀ j ≠ i, g j = f j) (h3 : ∀ j ≠ i, h j = f j) :
  ∏ i, g i + ∏ i, h i = ∏ i, f i :=
prod_add_prod_eq (mem_univ i) h1 (λ j _, h2 j) (λ j _, h3 j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_add_prod_le {α β} [linear_ordered_comm_ring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_split_single hi],
  refine le_trans _ (mul_le_mul_of_nonneg_right h2i _),
  { rw [right_distrib],
    apply add_le_add; apply mul_le_mul_of_nonneg_left; try { apply prod_le_prod };
    simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption },
  { apply prod_nonneg, simp only [and_imp, mem_sdiff, mem_singleton],
    intros j h1j h2j, refine le_trans (hg j h1j) (hgf j h1j h2j) }
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_univ_add_prod_univ_le {α β} [fintype α] [linear_ordered_comm_ring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, 0 ≤ h i) :
  ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j) (λ j _, hg j) (λ j _, hh j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`.
-/
lemma prod_add_prod_le' {α β} [canonically_ordered_comm_semiring β] {s : finset α} {i : α}
  {f g h : α → β} (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_split_single hi],
  refine le_trans _ (canonically_ordered_semiring.mul_le_mul_right' h2i _),
  rw [right_distrib],
  apply add_le_add; apply canonically_ordered_semiring.mul_le_mul_left'; apply prod_le_prod';
  simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`. -/
lemma prod_univ_add_prod_univ_le' {α β} [fintype α] [canonically_ordered_comm_semiring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) : ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le' (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j)

end finset

section complete_lattice

variables {ι : Sort*} {α : Type*} {x : α} [complete_lattice α]
lemma supr_const_le : (⨆ (h : ι), x) ≤ x :=
supr_le (λ _, le_rfl)

lemma le_infi_const : x ≤ (⨅ (h : ι), x) :=
le_infi (λ _, le_rfl)

end complete_lattice

namespace measure_theory

namespace outer_measure
section bounded_by

variables {α : Type*} (m : set α → ennreal)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def bounded_by : outer_measure α :=
outer_measure.of_function (λ s, ⨆ (h : s.nonempty), m s) (by simp [empty_not_nonempty])

variables {m}
theorem bounded_by_le (s : set α) : bounded_by m s ≤ m s :=
(of_function_le _).trans supr_const_le

local attribute [irreducible] outer_measure.of_function
theorem bounded_by_eq_of_function (m_empty : m ∅ = 0) (s : set α) :
  bounded_by m s = outer_measure.of_function m m_empty s :=
begin
  have : (λ s : set α, ⨆ (h : s.nonempty), m s) = m,
  { ext1 t, cases t.eq_empty_or_nonempty with h h; simp [h, empty_not_nonempty, m_empty] },
  simp [bounded_by, this]
end

theorem bounded_by_eq (s : set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ (s : ℕ → set α), m (⋃i, s i) ≤ (∑'i, m (s i))) : bounded_by m s = m s :=
by rw [bounded_by_eq_of_function m_empty, of_function_eq s m_mono m_subadd]

theorem le_bounded_by {μ : outer_measure α} : μ ≤ bounded_by m ↔ ∀ s, μ s ≤ m s :=
begin
  rw [bounded_by, le_of_function, forall_congr], intro s,
  cases s.eq_empty_or_nonempty with h h; simp [h, empty_not_nonempty]
end

theorem le_bounded_by' {μ : outer_measure α} :
  μ ≤ bounded_by m ↔ ∀ s : set α, s.nonempty → μ s ≤ m s :=
by { rw [le_bounded_by, forall_congr], intro s, cases s.eq_empty_or_nonempty with h h; simp [h] }

lemma bounded_by_caratheodory {m : set α → ennreal} {s : set α}
  (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) : (bounded_by m).caratheodory.is_measurable s :=
begin
  apply of_function_caratheodory, intro t,
  cases t.eq_empty_or_nonempty with h h,
  { simp [h, empty_not_nonempty] },
  { convert le_trans _ (hs t), simp [h], exact add_le_add supr_const_le supr_const_le }
end

/- TODO: also replace `Inf_eq_of_function_Inf_gen`. -/
end bounded_by
end outer_measure
open outer_measure

section measurable_pi
variables {α : Type*} {β : α → Type*} [Πa, measurable_space (β a)]

lemma is_measurable.pi [encodable α] {t : Π i, set (β i)} (hs : ∀ i, is_measurable (t i)) :
  is_measurable (pi univ t) :=
by { convert is_measurable.Inter (λ i, measurable_pi_apply _ (hs i) : _), simp [pi_def] }

lemma measurable_update (f : Π (a : α), β a) {i : α} : measurable (update f i) :=
begin
  apply measurable_pi_lambda,
  intro j, by_cases hj : j = i,
  { cases hj, convert measurable_id, ext, simp },
  simp_rw [update_noteq hj], apply measurable_const,
end

lemma is_measurable_pi_of_nonempty [encodable α] {t : Π i, set (β i)} (h : (pi univ t).nonempty) :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) :=
begin
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i, _, is_measurable.pi⟩,
  convert measurable_update f hst, rw [update_preimage_pi_univ], exact λ j _, hf j (mem_univ j)
end

lemma is_measurable_pi [encodable α] {t : Π i, set (β i)} :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) ∨ ∃ i, t i = ∅ :=
begin
  cases (pi univ t).eq_empty_or_nonempty with h h,
  { have := pi_univ_eq_empty_iff.mp h, simp [h, pi_univ_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, pi_univ_nonempty_iff.mp h, is_measurable_pi_of_nonempty h] }
end

end measurable_pi

section measure_pi

variables {ι : Type*} [fintype ι] {α : ι → Type*} {m : Π i, outer_measure (α i)}

/-- An upper bound for the measure in a product space.
  It is defined to be the product of the measures of all its projections.
  For boxes it should be equal to the correct measure. -/
def pi_premeasure (m : Π i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
∏ i, m i (eval i '' s)

@[simp] lemma pi_premeasure_def {s : set (Π i, α i)} :
  pi_premeasure m s = ∏ i, m i (eval i '' s) := rfl

lemma pi_premeasure_pi {s : Π i, set (α i)} (hs : (pi univ s).nonempty) :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
by simp [hs]

lemma pi_premeasure_pi' [nonempty ι] {s : Π i, set (α i)} :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
begin
  cases (pi univ s).eq_empty_or_nonempty with h h,
  { rcases pi_univ_eq_empty_iff.mp h with ⟨i, hi⟩,
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩,
    simpa [h, finset.card_univ, zero_pow (fintype.card_pos_iff.mpr _inst_2),
      @eq_comm _ (0 : ennreal), finset.prod_eq_zero_iff] },
  { simp [h] }
end

lemma pi_premeasure_pi_mono {s t : set (Π i, α i)} (h : s ⊆ t) :
  pi_premeasure m s ≤ pi_premeasure m t :=
finset.prod_le_prod' (λ i _, (m i).mono' (image_subset _ h))

lemma pi_premeasure_pi_eval [nonempty ι] {s : set (Π i, α i)} :
  pi_premeasure m (pi univ (λ i, eval i '' s)) = pi_premeasure m s :=
by simp [pi_premeasure_pi']

namespace outer_measure
/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi (m : Π i, outer_measure (α i)) : outer_measure (Π i, α i) :=
bounded_by (pi_premeasure m)

lemma pi_pi_le (s : Π i, set (α i)) :
  outer_measure.pi m (pi univ s) ≤ ∏ i, m i (s i) :=
by { cases (pi univ s).eq_empty_or_nonempty with h h, simp [h],
     exact (bounded_by_le _).trans_eq (pi_premeasure_pi h) }


lemma le_pi {m : Π i, outer_measure (α i)} {n : outer_measure (Π i, α i)} :
  n ≤ outer_measure.pi m ↔ ∀ (s : Π i, set (α i)), (pi univ s).nonempty →
    n (pi univ s) ≤ ∏ i, m i (s i) :=
begin
  rw [outer_measure.pi, le_bounded_by'], split,
  { intros h s hs, refine (h _ hs).trans_eq (pi_premeasure_pi hs)  },
  { intros h s hs, refine le_trans (n.mono $ subset_pi_eval_image univ s) (h _ _),
    simp [pi_univ_nonempty_iff, hs] }
end

lemma pi_pi_false [encodable ι] (s : Π i, set (α i))
  (h2s : (pi univ s).nonempty) : outer_measure.pi m (pi univ s) = ∏ i, m i (s i) :=
begin
  simp_rw [← pi_premeasure_pi h2s],
  refine le_antisymm (bounded_by_le _) _,
  refine le_binfi _, dsimp only, intros t ht,
  sorry
  -- refine le_trans _ (ennreal.tsum_le_tsum $ λ i, _),
end
end outer_measure

namespace measure

variables [Π i, measurable_space (α i)] (μ : Π i, measure (α i))

protected lemma caratheodory {α} [measurable_space α] (μ : measure α) {s t : set α}
  (hs : is_measurable s) : μ (t ∩ s) + μ (t \ s) = μ t :=
(le_to_outer_measure_caratheodory μ s hs t).symm

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _, intros i s hs,
  simp [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
  apply bounded_by_caratheodory, intro t,
  simp_rw [pi_premeasure_def],
  refine finset.prod_univ_add_prod_univ_le' i _ _ _,
  { simp [image_inter_preimage, image_compl_preimage, (μ i).caratheodory hs, le_refl] },
  { intros j hj, apply mono', apply image_subset, apply inter_subset_left },
  { intros j hj, apply mono', apply image_subset, apply diff_subset }
end

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be the maximal product measure, i.e.
  the maximal measure `n` with the property that `ν (pi univ s) = ∏ i, μ i (s i)`,
  where `pi univ s` is the product of the sets `{ s i | i : ι }`. -/
protected def pi : measure (Π i, α i) :=
to_measure (outer_measure.pi (λ i, (μ i).to_outer_measure)) (pi_caratheodory μ)

lemma pi_pi [encodable ι] (s : Π i, set (α i)) (h1s : ∀ i, is_measurable (s i))
  (h2s : (pi univ s).nonempty) : measure.pi μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  rw [measure.pi, to_measure_apply _ _ (is_measurable.pi h1s)],
  simp_rw [← to_outer_measure_apply, ← pi_premeasure_pi h2s],
  refine le_antisymm (bounded_by_le _) _,
  refine le_binfi _, dsimp only, intros t ht,
  sorry
end

end measure

end measure_pi


/-! ### Prod -/
namespace measure

variables {α β : Type*} [measurable_space α] [measurable_space β] (μ : measure α) (ν : measure β)

protected def prod : measure (α × β) :=
bind μ $ λ x : α, map (prod.mk x) ν

variables {μ ν}

lemma measurable.map {ι} [measurable_space ι] {f : ι → α → β} (hf : ∀ i, measurable (f i)) :
  measurable (λx, map (f x) μ) :=
begin
  sorry
end

@[simp] lemma prod_apply {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ x, ν (prod.mk x ⁻¹' s) ∂μ :=
begin
  rw [measure.prod, bind_apply hs],
  congr, ext x : 1, rw [map_apply _ hs],
  apply measurable_const.prod_mk measurable_id,
  refine measurable.map (λ _, measurable_const.prod_mk measurable_id)
end

lemma prod_apply_symm {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
begin
  /- prove for rectangles on which both `μ` and `ν` are finite -/
  /- assume μ and ν σ-finite -/
  /- show that it is closed under countable disjoint unions -/
  /- show that this is sufficient -/
  sorry
end

lemma prod_eq_symm : μ.prod ν = bind ν (λ y : β, map (λ x, (x, y)) μ) :=
begin
  simp [measure.prod, bind],
  sorry
end

end measure

end measure_theory

-- #lint
