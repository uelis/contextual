-- This file type-checks constructions from Sections 3 and 4
--
-- It uses Agda-flat
module internalCCC where

open import Agda.Builtin.Equality
open import Agda.Builtin.List

-- The box type for the ♭-modality
data [_](@♭ A : Set) : Set where
   flat_intro : (@♭ x : A) -> [ A ]

postulate
  obj : Set
  unit : obj
  times : obj -> obj -> obj
  arrow : obj -> obj -> obj

  El : obj -> Set

  -- unit is a terminal object
  terminal : El unit
  is_terminal : (x : El unit) -> x ≡ terminal

  -- times a b is a product
  fst : {c d : obj} -> El (times c d) -> El c
  snd : {c d : obj} -> El (times c d) -> El d
  pair : {c d : obj} -> El c -> El d -> El (times c d)
  times1 : {c d : _} -> (x : El c) -> (y : El d) -> fst (pair x y) ≡ x
  times2 : {c d : _} -> (x : El c) -> (y : El d) -> snd (pair x y) ≡ y
  times3 : {c d : _} -> (x : El (times c d)) -> x ≡ pair (fst x) (snd x)

  -- arrow is an exponential
  arrow_elim : {c d : obj} -> El (arrow c d) -> El c -> El d
  arrow_intro : {c d : obj} -> (El c -> El d) -> El (arrow c d)
  eps_iso1 : {c d : obj} -> (f : El (arrow c d)) -> arrow_intro (arrow_elim f) ≡ f
  eps_iso2 : {c d : obj} -> (f : El c -> El d) -> arrow_elim (arrow_intro f) ≡ f

  -- obj is a flat type, i.e. there is an isomorphism between
  -- obj and Flat obj. The following constant adds that information.
  -- TODO: Agda-flat doesn't know this when checking type
  -- dependencies.
  obj_flat : obj -> [ obj ]

-- Concrete example of an object-level encoding
postulate
  tm : obj
  app : El tm -> El tm -> El tm
  lam : (El tm -> El tm) -> El tm


-- Contextual types are modelled as types of the form [ γ ⊢ a ],
-- where γ ⊢ a is defined as:
_⊢_ : obj -> obj -> Set
γ ⊢ a = El γ -> El a

-- Example: the last variable in a non-empty context
var : {gamma : obj} -> {a : obj} -> (times gamma a) ⊢ a
var {gamma} {a} = λ x ->  snd x

-- Inductive definition of all projections
data Proj : (gamma : obj) -> (a : obj) -> (gamma ⊢ a) -> Set where
  Psingleton : (a : obj) -> Proj a a (λ x -> x)
  Pfst : (gamma : obj) -> (b a : obj) -> (f : _) ->
         Proj gamma a f ->
         Proj (times gamma b) a (λ x -> f (fst x))
  Psnd : (gamma : obj) -> (a : obj) ->
         Proj (times gamma a) a var

-- A contextual type [ γ ⊢v a ] of domain-level variables can be defined
-- as a record type. It consists of all the projections out of a context.
record _⊢v_ (@♭ γ : obj) (@♭ a : obj) : Set where
  constructor _,_
  field
    term : γ ⊢ a
    is_proj : Proj γ a term

-- Coercion from [ γ ⊢v a ] to [ γ ⊢ a ]
of_var : {@♭ gamma : obj } {@♭ a : obj} -> [ gamma ⊢v a ] -> [ gamma ⊢ a ]
of_var (flat_intro x) = flat_intro (_⊢v_.term x)


-- In the following we type-check a shallow embedding of the typing rules
-- for the simple contextual type system. The context Δ therefore disappears
-- to the the meta-level. We therefore only need to type-check the rules
-- for the domain language.


-------------------------------
-- Simply-typed domain terms --
-------------------------------

-- Δ; Φ ⊢ t: a becomes Φ ⊢ a

-- Variable rule
-- (for last position in context; general case follows using r_weak)
dt_var : {@♭ Φ a : obj} -> times Φ a ⊢ a
dt_var = λ ϕ -> snd ϕ

-- Weakening rule
dt_weak : {@♭ Φ a b : obj} ->  Φ ⊢ a  ->  times Φ b ⊢ a
dt_weak h = λ ϕ -> h (fst ϕ)

-- Application rule
dt_app : {@♭ Φ a b : obj} ->  Φ ⊢ arrow a b  ->  Φ ⊢ a  ->  Φ ⊢ b
dt_app h1 h2 = λ ϕ -> arrow_elim (h1 ϕ) (h2 ϕ)

-- Abstraction rule
dt_lam : {@♭ Φ a b : obj} ->  times Φ a ⊢ b  ->  Φ ⊢ arrow a b
dt_lam h = λ ϕ -> arrow_intro (λ arg -> (h (pair ϕ arg)))

dt_constapp : {@♭ Φ : obj} ->  Φ ⊢ arrow tm (arrow tm tm)
dt_constapp = λ ϕ -> arrow_intro (λ x -> arrow_intro (λ y -> app x y))

dt_constlam : {@♭ Φ : obj} ->  Φ ⊢ arrow (arrow tm tm) tm
dt_constlam = λ ϕ -> arrow_intro (λ x -> lam (arrow_elim x))

--------------------------------
-- Domain-level substitutions --
--------------------------------

-- Δ; Φ ⊢ σ: Ψ  becomes a function El Φ -> El Ψ

-- Empty substitution
sub_empty : {@♭ Φ : obj} ->  El Φ -> El unit
sub_empty = λ ϕ -> terminal

-- Identity substitution
-- (the general case from the paper is obtained using sub_weak)
sub_id : {@♭ Φ : obj} ->  El Φ -> El Φ
sub_id = λ ϕ -> ϕ

-- Weakening substitution
sub_weak : {@♭ Φ Ψ a : obj} ->  (El Φ -> El Ψ)  ->  El (times Φ a) -> El Ψ
sub_weak h = λ ϕ -> h (fst ϕ)

-- Extending substitution
sub_pair : {@♭ Φ Ψ a : obj} ->  (El Φ -> El Ψ)  ->  (Φ ⊢ tm) ->  (El Φ -> El (times Ψ tm))
sub_pair h1 h2 = λ ϕ -> pair (h1 ϕ) (h2 ϕ)


------------------------
-- Contextual Objects --
------------------------

-- Introduction of contextual object
ct_tm : {@♭ Φ Ψ a : obj} ->  (@♭ h :  Φ ⊢ a)  ->   [ Φ ⊢ a ]
ct_tm h = flat_intro h

-- Empty context
ct_ctx_empty : obj
ct_ctx_empty = unit

-- Empty context
ct_ctx_append : obj -> obj
ct_ctx_append h = times h tm
