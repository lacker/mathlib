/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import control.basic data.sum data.list.defs tactic.basic
import tactic.type_based_naming

/--
After elaboration, Lean does not have non-dependent function types with
unnamed arguments. This means that for the declaration

```lean
inductive test : Type :=
| intro : unit → test
```

the type of `test.intro` becomes

```lean
test.intro : ∀ (a : unit), test
```lean

after elaboration, where `a` is an auto-generated name.

This means that we can't know for sure whether a constructor argument was named
by the user. Hence the following hack: If an argument is non-dependent *and* its
name is `a` or `a_n` for some `n ∈ ℕ`, then we assume that this name was
auto-generated rather than chosen by the user.
-/
library_note "unnamed constructor arguments"


universes u v w


namespace list

open native

variables {α : Type u} {β : Type v}

/-- Auxiliary definition for `foldl_with_index`. -/
def foldl_with_index_aux (f : ℕ → α → β → α) : ℕ → α → list β → α
| _ a [] := a
| i a (b :: l) := foldl_with_index_aux (i + 1) (f i a b) l

/--
Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index.
-/
def foldl_with_index (f : ℕ → α → β → α) (a : α) (l : list β) : α :=
foldl_with_index_aux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldr_with_index_aux (f : ℕ → α → β → β) : ℕ → β → list α → β
| _ b [] := b
| i b (a :: l) := f i a (foldr_with_index_aux (i + 1) b l)

/--
Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index.
-/
def foldr_with_index (f : ℕ → α → β → β) (b : β) (l : list α) : β :=
foldr_with_index_aux f 0 b l

section mfold_with_index

variables {m : Type v → Type w} [monad m]

/-- Monadic variant of `foldl_with_index`. -/
def mfoldl_with_index (f : ℕ → β → α → m β) (b : β) (as : list α) : m β :=
as.foldl_with_index (λ i ma b, do a ← ma, f i a b) (pure b)

/-- Monadic variant of `foldr_with_index`. -/
def mfoldr_with_index (f : ℕ → α → β → m β) (b : β) (as : list α) : m β :=
as.foldr_with_index (λ i a mb, do b ← mb, f i a b) (pure b)

end mfold_with_index

section mmap_with_index

variables {m : Type v → Type w} [applicative m]

def mmap_with_index_aux (f : ℕ → α → m β) : ℕ → list α → m (list β)
| _ [] := pure []
| i (a :: as) := list.cons <$> f i a <*> mmap_with_index_aux (i + 1) as

def mmap_with_index (f : ℕ → α → m β) (as : list α) : m (list β) :=
mmap_with_index_aux f 0 as

end mmap_with_index

section mmap_with_index'

variables {m : Type → Type v} [applicative m]

def mmap_with_index'_aux (f : ℕ → α → m unit) : ℕ → list α → m unit
| _ [] := pure punit.star
| i (a :: as) := f i a *> mmap_with_index'_aux (i + 1) as

def mmap_with_index' (f : ℕ → α → m unit) (as : list α) : m unit :=
mmap_with_index'_aux f 0 as

end mmap_with_index'

/-- The list of indices of a list. `index_list l = [0, ..., length l - 1]`. -/
def index_list : list α → list ℕ := map_with_index (λ i _, i)

/-- `indexed_list [x₀, ..., xₙ] = [(0, x₀), ..., (n, xₙ)]` -/
def indexed (xs : list α) : list (ℕ × α) :=
xs.foldr_with_index (λ i a l, (i, a) :: l) []

def to_rbmap : list α → rbmap ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) (mk_rbmap ℕ α)

meta def to_rb_map {α : Type} : list α → rb_map ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) mk_rb_map

def all_some : list (option α) → option (list α)
| [] := some []
| (some x :: xs) := (λ xs, x :: xs) <$> all_some xs
| (none :: xs) := none

def m_any {m} [monad m] {α} (p : α → m bool) : list α → m bool
| [] := pure ff
| (x :: xs) := do
  px ← p x,
  if px then pure tt else m_any xs

def m_all {m} [monad m] {α} (p : α → m bool) : list α → m bool
| [] := pure tt
| (x :: xs) := do
  px ← p x,
  if px then m_all xs else pure ff

def mbor {m} [monad m] (xs : list (m bool)) : m bool := xs.m_any id

def mband {m} [monad m] (xs : list (m bool)) : m bool := xs.m_all id

end list


namespace native

@[reducible] meta def rb_multimap (α β : Type) : Type :=
rb_map α (rb_set β)

meta def mk_rb_multimap (α β : Type) [ltα : has_lt α] [ltβ : has_lt β]
  [decidable_rel ((<) : α → α → Prop)]
  : rb_multimap α β :=
mk_rb_map


namespace rb_multimap

variables {α β : Type}

section

variables [has_lt α] [has_lt β] [decidable_rel ((<) : α → α → Prop)]

meta def find (m : rb_multimap α β) (a : α)
  : option (rb_set β) :=
rb_map.find m a

variables [decidable_rel ((<) : β → β → Prop)]

meta def insert (m : rb_multimap α β) (a : α) (b : β) : rb_multimap α β :=
let bs := m.find a in
rb_map.insert m a
  (match bs with
   | none := rb_map.set_of_list [b]
   | (some bs) := bs.insert b
   end)

meta def contains (m : rb_multimap α β) (a : α) (b : β) : bool :=
match m.find a with
| none := false
| (some bs) := bs.contains b
end

end

meta def to_list (m : rb_multimap α β) : list (α × rb_set β) :=
rb_map.to_list m

meta def to_multilist (m : rb_multimap α β) : list (α × list β) :=
(rb_map.to_list m).map (λ ⟨a, bs⟩, ⟨a, bs.to_list⟩)

end rb_multimap


namespace rb_set

variables {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)]

meta def merge (xs ys : rb_set α) : rb_set α :=
rb_set.fold ys xs (λ a xs, xs.insert a)

end rb_set
end native

open native


namespace binder_info

def is_implicit : binder_info → bool
| implicit := tt
| _ := ff

end binder_info


namespace expr

meta def local_pp_name_option : expr → option name
| (local_const _ n _ _) := some n
| _ := none

meta def local_unique_name_option : expr → option name
| (local_const n _ _ _) := some n
| _ := none

meta def local_names_option : expr → option (name × name)
| (local_const n₁ n₂ _ _) := some (n₁, n₂)
| _ := none

meta def is_local (e : expr) : bool := e.local_unique_name_option.is_some

meta def free_vars (binder_depth : ℕ) (e : expr) : rbtree ℕ :=
e.fold (mk_rbtree ℕ) $ λ e depth vars,
  match e with
  | var n := if n ≥ binder_depth + depth then vars.insert n else vars
  | _ := vars
  end

/-- Given a closed type of the form `∀ (x : T) ... (z : U), V`, this function
returns a tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.

Note that the type of each argument and the return type all live in a different
contexts. For example, for the input `∀ (x : α) (y : β x) (z : γ x y), δ`,
`decompose_pi` returns `β #0` as the type of `y` and `γ #1 #0` as the type of
`z` -- the two `#0`s do not denote the same thing.
-/
meta def decompose_pi
  : expr → list (name × binder_info × expr × bool) × ℕ × expr
| (pi name binfo T rest) :=
  let (args, n_args, ret) := decompose_pi rest in
  -- NOTE: the following makes this function quadratic in the size of the input
  -- expression.
  let dep := rest.has_var_idx 0 in
  ((name, binfo, T, dep) :: args, n_args + 1, ret)
| e := ([], 0, e)

/-- Given a closed type of the form `∀ (x : T) ... (z : U), V`, this function
returns a tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.

The input expression is normalised lazily. This means that the returned
expressions are not necessarily in normal form.

Note that the type of each argument and the return type all live in a different
contexts. For example, for the input `∀ (x : α) (y : β x) (z : γ x y), δ`,
`decompose_pi_normalizing` returns `β #0` as the type of `y` and `γ #1 #0`
as the type of `z` -- the two `#0`s do not denote the same thing.
-/
meta def decompose_pi_normalizing
  : expr → tactic (list (name × binder_info × expr × bool) × expr) := λ e, do
  e ← tactic.whnf e,
  match e with
  | (pi n binfo T rest) := do
      (args, ret) ← decompose_pi_normalizing rest,
      -- NOTE: the following makes this function quadratic in the size of the input
      -- expression.
      let dep := rest.has_var_idx 0,
      pure ((n , binfo, T, dep) :: args, ret)
  | _ := pure ([] , e)
  end

/-- Auxiliary function for `decompose_app`. -/
meta def decompose_app_aux : expr → expr × list expr
| (app t u) :=
  let (f , args) := decompose_app_aux t in
  (f , u :: args)
| e := (e , [])

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.
-/
meta def decompose_app (e : expr) : expr × list expr :=
let (f , args) := decompose_app_aux e in
(f , args.reverse)

/-- Auxiliary function for `decompose_app_normalizing`. -/
meta def decompose_app_normalizing_aux (md : tactic.transparency)
  : expr → tactic (expr × list expr) := λ e, do
  e ← tactic.whnf e md,
  match e with
  | (app t u) := do
      (f , args) ← decompose_app_normalizing_aux t,
      pure (f , u :: args)
  | _ := pure (e , [])
  end

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.

`e` is normalised lazily. This means that the returned expressions are not
necessarily in normal form.
-/
meta def decompose_app_normalizing (e : expr) (md := semireducible)
  : tactic (expr × list expr) := do
  (f , args) ← decompose_app_normalizing_aux md e,
  pure (f , args.reverse)

/-- Returns the set of variables occurring in `e`. -/
meta def vars (e : expr) : rb_set ℕ :=
e.fold mk_rb_set $ λ e _ occs,
  match e with
  | var n := occs.insert n
  | _ := occs
  end

meta def local_constants (e : expr) : expr_set :=
e.fold mk_expr_set $ λ e _ occs,
  if e.is_local_constant
    then occs.insert e
    else occs

/-- Given an application `e = f x ... z`, this function returns a map
associating each de Bruijn index that occurs in `e` with the application
argument(s) that it occurs in. For instance, if `e = f (#2 + 1) #3 #3` then the
returned map is

    3 -> 1, 2
    2 -> 0

Arguments are counted from zero (as shown above).
-/
meta def application_variable_occurrences (e : expr) : rb_multimap ℕ ℕ :=
let (_, args) := decompose_app e in
let occs := args.map vars in
occs.foldl_with_index
  (λ i occ_map occs, occs.fold occ_map (λ var occ_map, occ_map.insert var i))
  (mk_rb_multimap ℕ ℕ)

meta def eta_expand_leading_implicit_arguments (e : expr) (t : expr) : expr :=
let ⟨args, _⟩ := decompose_pi t in
let implicit_args := args.take_while (λ x, x.2.1.is_implicit) in
let implicit_arg_types := implicit_args.map (λ ⟨name, _, type, _⟩, (name, type)) in
let applications :=
  implicit_arg_types.foldr_with_index (λ i _ res, app res (var i)) e in
implicit_arg_types.foldr (λ ⟨name, type⟩ res, lam name binder_info.implicit type res) applications

-- TODO debug
example (x : Π {n m : ℕ} (k : unit), ℕ) : unit :=
begin
  let h : ℕ := @x 0 1 (),
  (do x ← tactic.get_local `x,
      t ← tactic.infer_type x,
      let ⟨args, _⟩ := decompose_pi t,
      let implicit_args := args.take_while (λ x, x.2.1.is_implicit),
      tactic.trace $ implicit_args.map (λ ⟨n, _, t, _⟩, (n, t)),
      tactic.trace $ (eta_expand_leading_implicit_arguments x t)
  ),
  exact ()
end

end expr


namespace sum

def get_left {α β} : α ⊕ β → option α
| (inl a) := some a
| _ := none

def get_right {α β} : α ⊕ β → option β
| (inr b) := some b
| _ := none

def is_left {α β} (s : α ⊕ β) : bool :=
s.get_left.is_some

def is_right {α β} (s : α ⊕ β) : bool :=
s.get_right.is_some

end sum


namespace parser

def char : parser char :=
sat (λ _, true)

def digit : parser nat := do
  c ← char,
  let c' := c.to_nat - '0'.to_nat,
  if 0 ≤ c' ∧ c' ≤ 9
    then pure c'
    else parser.fail $ "expected a digit, got: " ++ c.to_string

def nat : parser nat := do
  digits ← many1 digit,
  pure $ prod.fst $
    digits.foldr
      (λ digit ⟨sum, magnitude⟩, ⟨sum + digit * magnitude, magnitude * 10⟩)
      ⟨0, 1⟩

end parser


namespace name

open parser

meta def basename : name → name
| anonymous := anonymous
| (mk_string s _) := mk_string s anonymous
| (mk_numeral n _) := mk_numeral n anonymous

/-- See [note unnamed constructor arguments]. -/
meta def likely_generated_name_p : parser unit := do
  str "a",
  optional (ch '_' *> nat),
  pure ()

/-- See [note unnamed constructor arguments]. -/
meta def is_likely_generated_name (n : name) : bool :=
match n with
| anonymous := ff
| mk_numeral _ _ := ff
| mk_string s anonymous := (likely_generated_name_p.run_string s).is_right
| mk_string _ _ := ff
end

end name


namespace tactic

open expr native

meta def open_binder_aux (n : name) (bi : binder_info) (t e : expr)
  : tactic (expr × name × expr) := do
  c_name ← tactic.mk_fresh_name,
  let c := local_const c_name c_name bi t,
  pure $ ⟨e.instantiate_var c, n, c⟩

/--
Given an `e` with `e = ∀ (x : T), U` or `e = λ (x : T), U`, `open_binder e`
returns

- `U[x/c]`, where `c` is a new local constant with type `T`;
- `x` (the binder name);
- `c` (the local constant).

Note that `c` is not introduced into the context, so `U[x/c]` will not
type-check.

Fails if `e` does not start with a pi or lambda.
-/
meta def open_binder : expr → tactic (expr × name × expr)
| (lam n bi t e) := open_binder_aux n bi t e
| (pi  n bi t e) := open_binder_aux n bi t e
| e := fail! "open_binder: expected an expression starting with a pi or lambda, but got:\n{e}"

/--
For an input expression `e = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U`,
`decompose_constructor_type e` returns the following:

- For each `xᵢ`: the name `xᵢ`; a fresh local constant `cᵢ` which
  replaces `xᵢ` in the other returned expressions; and whether `xᵢ` is a
  dependent argument (i.e. whether it occurs in the remainder of `e`).
  The type `Tᵢ` is the type of `cᵢ`.
- The return type `U`.
-/
meta def decompose_constructor_type_pis
  : expr → tactic (list (name × expr × bool) × expr) := λ e, do
  e ← whnf e,
  match e with
  | (pi _ _ _ rest) := do
    -- TODO the next line makes this function quadratic in the size of the
    -- expression.
    let dep := rest.has_var_idx 0,
    ⟨e, pi_name, cnst⟩ ← open_binder e,
    ⟨args, u⟩ ← decompose_constructor_type_pis e,
    pure $ ⟨⟨pi_name, cnst, dep⟩ :: args, u⟩
  | _ := pure ⟨[], e⟩
  end

meta def get_app_fn_const_normalizing : expr → tactic name := λ e, do
  e ← whnf e,
  match e with
  | (const n _) := pure n
  | (app f _) := get_app_fn_const_normalizing f
  | _ := fail! "expected a constant (possibly applied to some arguments), but got:\n{e}"
  end

/--
`fuzzy_type_match t s` is true iff `t` and `s` are definitionally equal.
-/
-- TODO is it worth extending this check to be more permissive? E.g. if a
-- constructor argument has type `list α` and the index has type `list β`, we
-- may want to consider these types sufficiently similar to inherit the name.
-- Same (but even more obvious) with `vec α n` and `vec α (n + 1)`.
meta def fuzzy_type_match (t s : expr) : tactic bool :=
  (is_def_eq t s *> pure tt) <|> pure ff
  -- (is_def_eq t s *> pure tt) <|> do
  --   (some t_const) ← try_core $ get_app_fn_const_normalizing t | pure ff,
  --   (some s_const) ← try_core $ get_app_fn_const_normalizing s | pure ff,
  --   pure $ t_const = s_const

/-
TODO doc
Input: The local constants representing the constructor arguments.

Assumption: The input expression has the form `e = C x₁ ... xₙ` where
`C` is a local constant.

Output: A map associating each of the arg local constants `cᵢ` with the set of
indexes `j` such that `cᵢ` appears in `xⱼ` and `xⱼ`'s type fuzzily matches that
of `cᵢ`.
-/
meta def decompose_constructor_type_return (num_params : ℕ) (args : expr_set)
  : expr → tactic (rb_multimap expr ℕ) := λ ret_type, do
  ⟨_, ret_args⟩ ← decompose_app_normalizing ret_type,
  ret_args.mfoldl_with_index
    (λ i occ_map ret_arg, do
      if i < num_params
        then pure occ_map
        else do
          let ret_arg_consts := ret_arg.local_constants,
          ret_arg_consts.mfold occ_map $ λ c occ_map, do
            ret_arg_type ← infer_type ret_arg,
            eq ← fuzzy_type_match c.local_type ret_arg_type,
            pure $ if eq then occ_map.insert c i else occ_map)
    (mk_rb_multimap _ _)

/--
TODO doc
-/
meta def decompose_constructor_type (num_params : ℕ) (e : expr)
  : tactic (list (name × expr × bool × rb_set ℕ)) := do
  ⟨args, ret⟩ ← decompose_constructor_type_pis e,
  let arg_constants := rb_map.set_of_list (args.map (λ ⟨_, c, _⟩, c)),
  index_occs ← decompose_constructor_type_return num_params arg_constants ret,
  pure $ args.map $ λ ⟨n, c, dep⟩,
    let occs := (index_occs.find c).get_or_else mk_rb_map in
    ⟨n, c.local_type, dep, occs⟩

/-- Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence. -/
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr)
  : bool :=
let base := arg_type.get_app_fn in
match base with
| (expr.const base _) := base = type_name
| _ := ff
end

@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)

@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(args : list constructor_argument_info)

@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/-- Gathers information about a constructor from the environment. Fails if `c`
does not refer to a constructor. -/
meta def get_constructor_info (env : environment) (num_params : ℕ) (c : name)
  : tactic constructor_info := do
  when (¬ env.is_constructor c) $ exceptional.fail format!
    "Expected {c} to be a constructor.",
  decl ← env.get c,
  args ← decompose_constructor_type num_params decl.type,
  pure
    { cname := decl.to_name,
      args := args.map_with_index $ λ i ⟨name, type, dep, index_occs⟩,
        ⟨name, type, dep, index_occs.to_list⟩,
    }

/-- Gathers information about an inductive type from the environment. Fails if
`T` does not refer to an inductive type. -/
meta def get_inductive_info (env : environment) (T : name)
  : tactic inductive_info := do
  when (¬ env.is_inductive T) $ exceptional.fail format!
    "Expected {T} to be an inductive type.",
  decl ← env.get T,
  let type := decl.type,
  let num_params := env.inductive_num_params T,
  let num_indices := env.inductive_num_indices T,
  let constructor_names := env.constructors_of T,
  constructors ← constructor_names.mmap
    (get_constructor_info env num_params),
  pure
    { iname := T,
      constructors := constructors,
      num_constructors := constructors.length,
      type := type,
      num_params := num_params,
      num_indices := num_indices }

meta structure eliminee_info :=
(ename : name)
(eexpr : expr)
(type : expr)
(args : rb_map ℕ expr)

meta def get_eliminee_info (ename : name) : tactic eliminee_info := do
  e ← get_local ename,
  type ← infer_type e,
  ⟨f, args⟩ ← type.decompose_app_normalizing,
  pure
    { ename := ename,
      eexpr := e,
      type := type,
      args := args.to_rb_map }

meta structure constructor_argument_naming_info :=
(einfo : eliminee_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → tactic (list name)

meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule := λ i,
if is_recursive_constructor_argument i.iinfo.iname i.ainfo.type
  then pure [i.einfo.ename]
  else failed

meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule := λ i,
let index_occs := i.ainfo.index_occurrences in
let eliminee_args := i.einfo.args in
let local_index_instantiations :=
  (index_occs.map (eliminee_args.find >=> expr.local_names_option)).all_some in
-- TODO this needs to be updated when we allow complex indices
match local_index_instantiations with
| none := failed
| some [] := failed
| some ((uname, ppname) :: is) :=
  if is.all (λ ⟨uname', _⟩, uname' = uname)
    then pure [ppname]
    else failed
end

meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule := λ i,
let arg_name := i.ainfo.aname in
let arg_dep := i.ainfo.dependent in
if ! arg_dep && arg_name.is_likely_generated_name
  then failed
  else pure [arg_name]

meta def constructor_argument_naming_rule_type : constructor_argument_naming_rule := λ i, do
typical_variable_names i.ainfo.type

meta def default_constructor_argument_name : name := `x

meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule)
  : tactic (list name) :=
  first (rules.map ($ info)) <|> pure [default_constructor_argument_name]

meta def constructor_argument_names (info : constructor_argument_naming_info)
  : tactic (list name) :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named
  , constructor_argument_naming_rule_type ]

-- TODO this only works with simple names
meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

-- TODO the implementation is a bit of an 'orrible hack
meta def get_unused_name'_aux (n : name) (reserved : name_set)
  : option nat → tactic name := λ suffix, do
  n ← get_unused_name n suffix,
  if ¬ reserved.contains n
    then pure n
    else do
      let new_suffix :=
        match suffix with
        | none := some 1
        | some n := some (n + 1)
        end,
      get_unused_name'_aux new_suffix

/- Precond: ns is nonempty. -/
meta def get_unused_name' (ns : list name) (reserved : name_set) : tactic name := do
  let fallback := ns.head,
  let ns := ns.filter (λ n, ¬ reserved.contains n),
  n ← try_core $ first $ ns.map $ λ n, do {
    guard (¬ reserved.contains n),
    fail_if_success (resolve_name n),
    pure n
  },
  match n with
  | some n := pure n
  | none := get_unused_name'_aux fallback reserved none
  end

/- Precond: ns is nonempty. -/
meta def intro_fresh (ns : list name) (reserved : name_set) : tactic expr := do
  n ← get_unused_name' ns reserved,
  intro n

/- Precond: i is a local constant. -/
meta def type_depends_on_local (h i : expr) : tactic bool := do
  h_type ← infer_type h,
  pure $ h_type.has_local_constant i

/- Precond: i is a local constant. -/
meta def local_def_depends_on_local (h i : expr) : tactic bool := do
  (some h_val) ← try_core $ local_def_value h | pure ff,
  pure $ h_val.has_local_constant i

/- Precond: h and i are local constants. -/
meta def local_depends_on_local (h i : expr) : tactic bool :=
list.mbor
  [ pure $ h = i
  , type_depends_on_local h i
  , local_def_depends_on_local h i
  ]

/--
Reverts all hypotheses except those in `fixed` and those whose type depends
on any of the hypotheses in `fixed`.

TODO example
TODO precond: `fixed` contains only locals
-/
-- TODO efficiency: we could put the locals that appear in each hypothesis in a
-- map to avoid multiple traversals
meta def revert_all_except_locals (fixed : list expr) : tactic (ℕ × list name) := do
  ctx ← local_context,
  to_revert ← ctx.mfilter $ λ hyp,
    fixed.m_all (λ fixed_hyp, bnot <$> local_depends_on_local fixed_hyp hyp),
  let reverted_names := to_revert.map expr.local_pp_name,
  n ← revert_lst to_revert,
  pure ⟨n, reverted_names⟩

meta def constructor_argument_intros (einfo : eliminee_info)
  (iinfo : inductive_info) (cinfo : constructor_info) (reserved_names : name_set)
  : tactic (list (name × expr)) :=
(cinfo.args.drop iinfo.num_params).mmap $ λ ainfo, do
  names ← constructor_argument_names ⟨einfo, iinfo, cinfo, ainfo⟩,
  h ← intro_fresh names reserved_names,
  pure ⟨h.local_pp_name, ainfo.type⟩

meta def ih_intros (iinfo : inductive_info)
  (args : list (name × expr)) (reserved_names : name_set) : tactic (list expr) := do
  let rec_args := args.filter $ λ i,
    is_recursive_constructor_argument iinfo.iname i.2,
  let ih_names := rec_args.map $ λ ⟨n, _⟩, ih_name n,
  match ih_names with
  | []  := pure []
  | [n] := do ih ← intro_fresh ["ih", n] reserved_names, pure [ih]
  | ns := ns.mmap (λ ih, intro_fresh [ih] reserved_names)
  end

meta def constructor_intros (einfo : eliminee_info) (iinfo : inductive_info)
  (cinfo : constructor_info) (reserved_names : name_set) : tactic (list expr) := do
  args ← constructor_argument_intros einfo iinfo cinfo reserved_names,
  ih_intros iinfo args reserved_names

meta def generalize_complex_index_args (eliminee : expr) (index_args : list expr)
  : tactic (expr × list expr × list expr) := do
  let ⟨locals, nonlocals⟩ :=
    index_args.partition (λ arg : expr, arg.is_local_constant),

  -- If there aren't any complex index arguments, we don't need to do anything.
  (_ :: _) ← pure nonlocals | pure ⟨eliminee, [], []⟩,

  -- Revert the eliminee (and any hypotheses depending on it).
  num_reverted_eliminee ← revert eliminee,

  -- Revert any hypotheses depending on one of the complex index arguments
  (num_reverted_args : ℕ) ← list.sum <$> nonlocals.mmap revert_kdependencies,

  -- Introduce variables and equations for the complex index arguments
  index_vars_equations ← nonlocals.mmap $ λ arg, do {
    arg_name ← get_unused_name `index,
    eq_name ← get_unused_name $ arg_name ++ "eq",
    tgt ← target,
    ⟨tgt', _⟩ ← solve_aux tgt (generalize arg arg_name >> target)
      <|> fail "TODO",
    tgt' ← to_expr ``(Π x, x == %%arg → %%(tgt'.binding_body.lift_vars 0 1)),
    t ← assert eq_name tgt',
    swap,
    interactive.exact ``(%%t %%arg heq.rfl),
    arg_var ← intro arg_name,
    arg_var_eq ← intro eq_name,

    -- TODO The original induction clears some stuff at this point; see
    -- commented code below. But if I'm not mistaken, all the stuff that might
    -- be cleared occurs in the index equations, so this wouldn't do anything in
    -- our case. (The original induction doesn't generate index equations.)

    -- let arg_locals :=
    --   arg.fold [] (λ e _ locals, if e.is_local_constant then e::locals else locals),
    -- arg_locals.mmap' (try ∘ clear),

    pure (⟨arg_var, arg_var_eq⟩ : expr × expr)
  },

  -- Re-introduce the indices' dependencies
  intron num_reverted_args,

  -- Re-introduce the eliminee and its dependencies
  intron (num_reverted_eliminee - 1),
  eliminee ← intro1,

  -- Re-revert the index equations
  revert_lst $ index_vars_equations.map prod.snd,

  pure ⟨eliminee, index_vars_equations.map prod.fst, locals⟩

meta def replace' (h : expr) (x : expr) (t : option expr := none) : tactic expr := do
  h' ← note h.local_pp_name t x,
  clear h,
  pure h'

meta inductive simplification_result
| simplified (next_equations : list expr)
| not_simplified
| goal_solved

open simplification_result

meta def simplify_heterogeneous_index_equation (equ lhs_type rhs_type lhs rhs : expr)
  : tactic simplification_result :=
do {
  -- TODO debug
  trace "trying simplify_het_index_equation",
  is_def_eq lhs_type rhs_type,
  p ← to_expr ``(@eq_of_heq %%lhs_type %%lhs %%rhs %%equ),
  t ← to_expr ``(@eq %%lhs_type %%lhs %%rhs),
  equ ← replace' equ p (some t),
  pure $ simplified [equ]
} <|>
pure not_simplified

meta def simplify_defeq_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  -- TODO debug
  trace "trying simplify_defeq_equation",
  is_def_eq lhs rhs,
  clear equ,
  pure $ simplified []
} <|>
pure not_simplified

meta def simplify_var_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  -- TODO debug
  trace "trying simplify_var_equation",
  guard $ lhs.is_local ∨ rhs.is_local,
  subst equ,
  pure $ simplified []
} <|>
pure not_simplified

meta def decompose_and : expr → tactic (list expr) := λ h, do
  t ← infer_type h,
  match t with
  | `(%%P ∧ %%Q) := do
    h₁ ← to_expr ``(@and.elim_left %%P %%Q %%h),
    h₂ ← to_expr ``(@and.elim_right %%P %%Q %%h),
    h₁_name ← get_unused_name $ h.local_pp_name ++ "1",
    h₂_name ← get_unused_name $ h.local_pp_name ++ "2",
    h₁ ← note h₁_name P h₁,
    h₂ ← note h₂_name Q h₂,
    clear h,
    hs ← decompose_and h₂,
    pure $ h₁ :: hs
  | _ := pure [h]
  end

-- TODO This doesn't handle the case "n = n + 1". Does that ever come up?
meta def simplify_constructor_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  -- TODO debug
  trace "trying simplify_constructor_equation",
  (const f _, lhs_args) ← decompose_app_normalizing lhs,
  (const g _, rhs_args) ← decompose_app_normalizing rhs,
  env ← get_env,
  guard $ env.is_constructor f,
  guard $ env.is_constructor g,
  if f ≠ g
    then do
      cases equ,
      -- TODO debug
      trace "solved!",
      pure goal_solved
    else do
      inj ← resolve_name (f ++ "inj"),
      p ← to_expr ``(%%inj %%equ),
      equ ← replace' equ p,
      simplified <$> decompose_and equ
} <|>
pure not_simplified

meta def sequence_simplifiers (s t : tactic simplification_result)
  : tactic simplification_result := do
  r ← s,
  match r with
  | simplified _ := pure r
  | goal_solved := pure r
  | not_simplified := t
  end

meta def simplify_homogeneous_index_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
  list.foldl sequence_simplifiers (pure not_simplified)
    [ simplify_defeq_equation equ type lhs rhs
    , simplify_var_equation equ type lhs rhs
    , simplify_constructor_equation equ type lhs rhs
    ]

meta def simplify_index_equation_once (equ : expr) : tactic simplification_result := do
  t ← infer_type equ,
  match t with
  | `(@eq %%type %%lhs %%rhs) :=
    simplify_homogeneous_index_equation equ type lhs rhs
  | `(@heq %%lhs_type %%lhs %%rhs_type %%rhs) := do
    simplify_heterogeneous_index_equation equ lhs_type rhs_type lhs rhs
  | _ := fail! "Expected {equ} to be an equation, but its type is\n{t}."
  end

-- TODO unused, remove
meta def iterate'' {α} : α → (α → tactic α) → tactic α := λ a t, do
  (some a) ← try_core (t a) | pure a,
  iterate'' a t

meta def simplify_index_equations : list expr → tactic bool
| [] := pure ff
| (h :: hs) := do
  -- TODO debug
  t ← infer_type h,
  trace! "simplifying {h} : {t}",
  trace_state,

  res ← simplify_index_equation_once h,
  match res with
  | simplified hs' := simplify_index_equations $ hs' ++ hs
  | not_simplified := simplify_index_equations hs
  | goal_solved := pure tt
  end

-- TODO remove
meta inductive ih_arg
| refl (type value : expr)
| eq_to_heq (type lhs rhs : expr) (binder_ref : ℕ)
| heq (binder_ref : ℕ)

-- meta def simplify_ih₁
--   : list expr → ℕ → list pexpr → list ih_arg → tactic (ℕ × list pexpr × list ih_arg)
-- | [] num_new_binders new_binders new_args :=
--   pure ⟨num_new_binders, new_binders, new_args⟩
-- | (b@`(@heq %%lhs_type %%lhs %%rhs_type %%rhs) :: binders) num_new_binders new_binders new_args := do
--   types_eq ← succeeds $ is_def_eq lhs_type rhs_type,
--   ⟨num_new_binders, new_binders, new_args⟩ ← do {
--     if ¬ types_eq
--       then
--         pure ( num_new_binders + 1
--              , to_pexpr b :: new_binders
--              , ih_arg.heq num_new_binders :: new_args )
--       else do
--         rhs_eq_lhs ← succeeds $ is_def_eq lhs rhs,
--         if ¬ rhs_eq_lhs
--           then
--             pure ( num_new_binders + 1
--                  , ``(@eq %%lhs_type %%lhs %%rhs) :: new_binders
--                  , ih_arg.eq_to_heq lhs_type lhs rhs num_new_binders :: new_args)
--           else
--             pure ( num_new_binders
--                  , new_binders
--                  , ih_arg.refl lhs_type lhs :: new_args
--                  )
--   },
--   simplify_ih₁ binders num_new_binders new_binders new_args
-- | (b :: _) _ _ _ :=
--   fail! "simplify_ih₁: expected a heterogeneous equation, but got:\n{b}"

meta def simplify_ih₁ : list expr → tactic (ℕ × list pexpr × list ih_arg)
| [] := pure (0, [], [])
| (b@`(@heq %%lhs_type %%lhs %%rhs_type %%rhs) :: binders) := do
  ⟨num_binders, binders, args⟩ ← simplify_ih₁ binders,
  types_eq ← succeeds $ is_def_eq lhs_type rhs_type,
  if ¬ types_eq
    then
      pure ( num_binders + 1
           , to_pexpr b :: binders
           , ih_arg.heq num_binders :: args )
    else do
      rhs_eq_lhs ← succeeds $ is_def_eq lhs rhs,
      if ¬ rhs_eq_lhs
        then
          pure ( num_binders + 1
                , ``(@eq %%lhs_type %%lhs %%rhs) :: binders
                , ih_arg.eq_to_heq lhs_type lhs rhs num_binders :: args )
        else
          pure ( num_binders
                , binders
                , ih_arg.refl lhs_type lhs :: args
                )
| (b :: _) :=
  fail! "simplify_ih₁: expected a heterogeneous equation, but got:\n{b}"

meta def render_ih_arg (num_binders : ℕ) : ih_arg → pexpr
| (ih_arg.refl type value) :=
  ``(@heq.refl %%type %%value)
| (ih_arg.eq_to_heq type lhs rhs binder_ref) :=
  let v : expr := expr.var binder_ref in
  ``(@heq_of_eq %%type %%lhs %%rhs %%v)
| (ih_arg.heq binder_ref) :=
  expr.var $ binder_ref

meta def simplify_ih₂
  : expr → ℕ → list pexpr → list ih_arg → pexpr := λ ih num_binders binder_types args,
let ih_app :=
  args.foldl (λ res arg, ``(%%res %%(render_ih_arg num_binders arg)))
    (to_pexpr ih) in
binder_types.foldr (λ t res, (lam `_a binder_info.default t res)) ih_app

meta def simplify_ih (num_index_vars : ℕ) (ih : expr) : tactic expr := do
  ih_type ← infer_type ih,
  let ⟨args, _⟩ := decompose_pi ih_type,
  let index_eq_args := (args.take num_index_vars).map (λ ⟨_, _, type, _⟩, type),
  ⟨num_binders, new_binders, new_args⟩ ← simplify_ih₁ index_eq_args,
  let new_ih := simplify_ih₂ ih num_binders new_binders new_args,
  trace "before to_expr",
  new_ih ← to_expr new_ih ff ff,
  trace "after to_expr",
  -- let new_ih := new_ih.eta_expand_leading_implicit_arguments,
  replace' ih new_ih

meta def induction'' (eliminee_name : name) (fix : list name) : tactic unit := focus1 $ do
  einfo ← get_eliminee_info eliminee_name,
  let eliminee := einfo.eexpr,
  let eliminee_type := einfo.type,
  let eliminee_args := einfo.args.values,
  env ← get_env,

  -- Find the name of the inductive type
  iname ← do {
    iname ← get_app_fn_const_normalizing eliminee_type,
    guard (env.is_inductive iname),
    pure iname }
  <|> fail format!
    "The type of {eliminee_name} should be an inductive type, but it is {eliminee_type}.",

  iinfo ← get_inductive_info env iname,
  let rec_name := iname ++ "rec_on",
  rec_const ← mk_const rec_name,

  -- TODO We would like to disallow mutual/nested inductive types, since these
  -- have complicated recursors which we probably don't support. However, there
  -- seems to be no way to find out whether an inductive type is mutual/nested.
  -- (`environment.is_ginductive` doesn't seem to work.)

  -- Generalise all generalisable hypotheses except those mentioned in a "fixing"
  -- clause.
  fix_exprs ← fix.mmap get_local,
  ⟨num_generalized, generalized_names⟩ ←
    revert_all_except_locals (eliminee :: fix_exprs),
  let generalized_names := name_set.of_list generalized_names,

  -- Generalise complex indices
  ⟨eliminee, index_vars, _⟩ ←
    generalize_complex_index_args eliminee (eliminee_args.drop iinfo.num_params),
  let num_index_vars := index_vars.length,

  -- NOTE: The previous step may have changed the unique names of all hyps in
  -- the context.

  -- Apply the recursor
  interactive.apply ``(%%rec_const %%eliminee),

  -- For each case (constructor):
  focus $ iinfo.constructors.map $ λ cinfo, do {
    -- Get the eliminee's arguments. (Some of these may have changed due to the
    -- generalising step above.)
    -- TODO propagate this information instead of re-parsing the type here
    eliminee_type ← infer_type eliminee,
    ⟨_, eliminee_args⟩ ← decompose_app_normalizing eliminee_type,

    -- Clear the eliminated hypothesis
    clear eliminee,

    -- Clear the index args (unless other stuff in the goal depends on them)
    eliminee_args.mmap' (try ∘ clear),

    -- TODO is this the right thing to do? I don't think this necessarily
    -- preserves provability: The args we clear could contain interesting
    -- information, even if nothing else depends on them. Is there a way to avoid
    -- this, i.e. clean up even more conservatively?

    -- Introduce the constructor arguments
    ihs ← constructor_intros einfo iinfo cinfo generalized_names,

    -- Introduce the index equations
    index_equations ← intron' num_index_vars,

    -- Simplify the index equations. Stop after this step if the goal has been
    -- solved by the simplification.
    ff ← simplify_index_equations index_equations | pure (),

    -- The previous step may have changed the unique names of the induction
    -- hypotheses, so we have to locate them again. Their pretty names should be
    -- unique in the context, so we can use those.
    ihs ← ihs.mmap (λ h, get_local h.local_pp_name),

    -- Simplify the induction hypotheses
    ihs.mmap' (simplify_ih num_index_vars),

    -- Introduce any hypotheses we've previously generalised
    intron num_generalized
  },

  pure ()

end tactic


namespace tactic.interactive

open interactive lean.parser

precedence `fixing`:0

meta def induction'
  (hyp : parse ident)
  (fix : parse (optional (tk "fixing" *> many ident)))
  : tactic unit :=
  tactic.induction'' hyp (fix.get_or_else [])

end tactic.interactive