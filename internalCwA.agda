-- This file type-checks constructions from Sections 7 and 8
--
-- It uses Agda-flat:
-- https://github.com/agda/agda/tree/391734cff42587535068b5bee073bdb93b18f8d0
module internalCwA where

open import Agda.Builtin.Equality
open import Product

-- Σ-types
record Sigma (A : Set) (B : A → Set) : Set
record Sigma A B where
  constructor _,_
  field fst : A
        snd : B fst

-- Equational reasoning
sym : {a : Set} {x y : a} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {a : Set} {x y z : a} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl e =  e

eq_rec : { a : Set } -> { x y : a } -> (b : a -> Set) -> b x -> x ≡ y -> b y
eq_rec b u refl = u

-- The box type for the ♭-modality
data [_] (A :{♭} Set) : Set where
  ♭_ : (x :{♭} A) -> [ A ]

-- Structure of a category with attributes
postulate
  Ctx : Set
  Ty : Ctx -> Set

  nil : Ctx
  cons : (c : Ctx) -> Ty c -> Ctx

  El : Ctx -> Set
  terminal : El nil
  p : {c : Ctx} -> {a : Ty c} -> El (cons c a) -> El c
  sub : {c d : Ctx} -> (a : Ty d) -> (El c -> El d) -> Ty c
  q : {c d : Ctx} -> (a : Ty d) -> (f : El c -> El d) -> El (cons c (sub a f)) -> El (cons d a)

  -- nil is terminal object
  terminal_unique : (x : El nil) -> x ≡ terminal

  -- substitution axioms
  sub_id : (c : Ctx) -> (a : Ty c) -> sub a (λ x -> x) ≡ a
  sub_comp : (c d e : Ctx) -> (f : El c -> El d) -> (g : El d -> El e) -> (a : Ty e) ->
               sub a (λ x -> g (f x)) ≡ sub (sub a g) f

  -- substitution is a pullback
  pq_commutes : (c d : Ctx) -> (a : Ty d) -> (f : _)  -> (gamma : El (cons c (sub a f))) ->
                 p (q a f gamma) ≡ f (p gamma)

  pq_pullback : (c d : Ctx) -> (a : Ty c) -> (f : El d -> El c) -> (delta : _) -> (x : _) ->
                  p x ≡ f delta ->
                    Sigma _ (λ y -> p y ≡ delta ×
                                q a f y ≡ x ×
                                ((z : _) -> p z ≡ delta × q a f z ≡ x -> y ≡ z))

-- As a remark, we define the set of terms of the CwA as a type of all sections.
Tm0 : {c : Ctx} -> Ty c -> Set
Tm0 {c} a = Sigma _ (λ (f : El c -> El (cons c a)) -> (x : _) -> p (f x) ≡ x)

-- The term for a variable can be interpreted as follows:
var : {c : Ctx} -> (a : Ty c) -> Tm0 (sub a (p {_} {a}))
var {c} a =
  (λ gamma -> Sigma.fst (pq_pullback c _ a p gamma gamma refl)),
  (λ gamma ->
     let z = Sigma.snd (pq_pullback c _ a p gamma gamma refl) in
     Product.proj₁ z)



record ElTm {c : Ctx} (a : Ty c) (γ : El c) : Set
record ElTm {c} a γ where
  constructor mkElTm
  field value : El (cons c a)
        prf : p value ≡ γ

pair : {c : Ctx} -> {a : Ty c} -> (γ : El c) -> ElTm a γ -> El (cons c a)
pair γ x = ElTm.value x

p' : {c : Ctx} -> {a : Ty c} -> (γ : El (cons c a)) -> ElTm a (p γ)
p' γ = record { value = γ; prf = refl }

-- A few standard properties of pairing and projections.
pair_beta1 : {c : Ctx} -> {a : Ty c} -> (γ : El c) -> (t : ElTm a γ) -> p (pair γ t) ≡ γ
pair_beta1 γ t = ElTm.prf t

pair_beta2 : {c : Ctx} -> {a : Ty c} -> (γ : El c) -> (t : ElTm a γ) ->
  eq_rec (λ γ -> ElTm a γ) (p' (pair γ t)) (pair_beta1 γ t) ≡ t
  -- With extensional equality, this would be: p' (pair γ t) = t
pair_beta2 γ (mkElTm v refl) = refl

pair_eta : {c : Ctx} -> {a : Ty c} -> (γ : El (cons c a)) -> pair (p γ) (p' γ) ≡ γ
pair_eta γ = refl


-- Representation of terms.
-- In the paper, the following type is written as `Tm c a'
_⊢_ : (c :{♭} Ctx) -> (a :{♭} Ty c) -> Set
c ⊢ a = ((γ : El c)  -> ElTm a γ)

-- We note: The type (c ⊢ a) is isormophic to the terms of type a defined by sections.
iso_Tm_⊢ : {c :{♭} Ctx} -> {a :{♭} Ty c} -> Tm0 a -> (c ⊢ a)
iso_Tm_⊢ t gamma = record { value = Sigma.fst t gamma; prf = Sigma.snd t _ }

iso_⊢_Tm :  {c :{♭} Ctx} -> {a :{♭} Ty c} -> (c ⊢ a) -> Tm0 a
iso_⊢_Tm f = (λ gamma -> ElTm.value (f gamma)), (λ x -> ElTm.prf (f x))

-- Short notation for substitution with terms of the form (c ⊢a).
subt : {c :{♭} Ctx} -> {a :{♭} Ty c} -> Ty (cons c a) -> (c ⊢ a) -> Ty c
subt b t = sub b (λ γ -> pair γ (t γ))

-- Relate type substitition to contexts
subElTm : {c d : Ctx} -> {a : Ty c} -> {f : El d -> El c} -> {gamma : _} ->
        ElTm a (f gamma) -> ElTm (sub a f) gamma
subElTm {c} {d} {a} {f} {gamma} t =
  let z = pq_pullback _ _ _ f gamma (ElTm.value t) (ElTm.prf t) in
  let s = Sigma.fst z in
  let Hs = Sigma.snd z in
    record { value = s ; prf = Product.proj₁ Hs }

-- Relate type substitition to contexts
subElTm_inv : {c d : Ctx} -> {a : Ty c} -> {f : El d -> El c} -> {gamma : _} ->
        ElTm (sub a f) gamma -> ElTm a (f gamma)
subElTm_inv {c} {d} {a} {f} {gamma} t =
  record { value = q _ _ (ElTm.value t); prf = trans u1 u2 }
    where
      u1 : p (q _ f (ElTm.value t)) ≡ f (p (ElTm.value t))
      u1 = pq_commutes _ _ _ _ _
      u2 : f (p (ElTm.value t)) ≡ f gamma
      u2 rewrite (ElTm.prf t) = refl

-- Example use: weakening
weak : {c :{♭} Ctx} -> {a b :{♭} Ty c} -> (c ⊢ b) -> (cons c a ⊢ sub b p)
weak x = λ γ -> subElTm (x (p γ))


-- Dependent Products in the index category
postulate
  Π : {c : Ctx} -> (a : Ty c) -> (b : Ty (cons c a)) -> Ty c
  prod_elim : {c : Ctx} -> {a : Ty c} -> {b : _} -> {gamma : _} ->
     (f : ElTm (Π a b) gamma) -> (x : ElTm a gamma) -> ElTm b (ElTm.value x)
  prod_intro : {c : Ctx} -> {a : Ty c} -> {b : _} -> {gamma : _} ->
     ((x : ElTm a gamma) -> ElTm b (pair gamma x)) -> ElTm (Π a b) gamma
  beck_chevalley : {c d : Ctx} -> {a : Ty c} -> {b : Ty (cons c a)} -> (f : El d -> El c) ->
      sub (Π a b) f ≡ Π (sub a f) (sub b (q a f))


-- Example object-level encoding
postulate
  tp : {c : Ctx} -> Ty c
  o : {c : Ctx } -> (γ : El c) -> ElTm tp γ
  arr : {c : Ctx} -> {γ : El c} -> ElTm tp γ -> ElTm tp γ -> ElTm tp γ

  tm : {c : Ctx} -> Ty (cons c tp)
  app : {c :{♭} Ctx} -> {γ : El c} -> {a b : ElTm tp γ} ->
          ElTm tm (pair γ (arr a b)) -> ElTm tm (pair γ a) -> ElTm tm (pair γ b)
  lam : {c : Ctx} -> {γ : El c} -> {a b : ElTm tp γ} ->
          (ElTm tm (pair γ a) -> ElTm tm (pair γ b)) -> ElTm tm (pair γ (arr a b))

  rec_tm : {A : {psi :{♭} Ctx} -> {γ : El psi} -> (a : ElTm tp γ) -> (x : ElTm tm (pair γ a)) -> Set} ->
              -- input
            {phi :{♭} Ctx} ->
            {γ :{♭} El phi} ->
            (a :{♭} ElTm tp γ) ->
            (u :{♭} ElTm tm (pair γ a)) ->
            -- variables
            ((phi :{♭} Ctx) -> (γ : El phi) -> (b : ElTm tp γ) -> (x : ElTm tm (pair γ b)) -> A b x) ->
            -- application
            ((phi :{♭} Ctx) -> (γ : El phi) -> (b c : ElTm tp γ) -> (x : ElTm tm (pair γ (arr b c))) -> (y : ElTm tm (pair γ b)) ->
                 A (arr b c) x -> A b y -> A c (app x y)) ->
            -- abstraction
            ((phi :{♭} Ctx) -> (γ : El phi) -> (b c : ElTm tp γ) -> (f : (x : ElTm tm (pair γ b)) -> ElTm tm (pair γ c)) ->
                    ((x : _) -> (ih : A b x) -> A c (f x)) -> A (arr b c) (lam f)) ->
            -- result
            A a u

----------------------------------
-- Rules for domain-level types --
----------------------------------

tpI : {c :{♭} Ctx} -> Ty c
tpI = tp

tmI : {c :{♭} Ctx} -> (c ⊢ tp) -> Ty c
tmI t = sub tm (λ γ -> ElTm.value (t γ))

prodI : {c :{♭} Ctx} -> (a :{♭} Ty c) -> (b : Ty (cons c a)) -> Ty c
prodI a b = Π a b

----------------------------------
-- Rules for domain-level terms --
----------------------------------

varI : {c :{♭} Ctx} -> {a :{♭} Ty c} -> cons c a ⊢ (sub a p)
varI = λ γ -> subElTm (p' γ)

absI : {c :{♭} Ctx} -> {a :{♭} Ty c} -> {b :{♭} Ty (cons c a)}
         -> cons c a ⊢ b
         -> c ⊢ (Π a b)
absI t = λ γ -> prod_intro (λ x -> t (pair γ x))

appI : {c :{♭} Ctx} -> {a :{♭} Ty c} -> {b :{♭} Ty (cons c a)}
         -> c ⊢ (Π a b)
         -> (s :{♭} c ⊢ a)
         -> c ⊢ (sub b (λ γ -> ElTm.value (s γ)))
appI t s = λ γ -> subElTm (prod_elim (t γ) (s γ))

esubI : {c d :{♭} Ctx} -> {a :{♭} Ty c} -> {b :{♭} Ty (cons c a)}
         -> (sigma :{♭} El d -> El c)
         -> (x :{♭} c ⊢ a)
         -> d ⊢ sub a sigma
esubI sigma x = λ δ -> subElTm (x (sigma δ))

constarrI : {c :{♭} Ctx} -> c ⊢ tp -> c ⊢ tp -> c ⊢ tp
constarrI a b = λ γ -> arr (a γ) (b γ)

constappI : {c :{♭} Ctx} -> (a :{♭} c ⊢ tp) -> (b :{♭} c ⊢ tp) ->
    c ⊢ (subt tm (constarrI a b))  ->  c ⊢ subt tm a ->  c ⊢ subt tm b
constappI a b x y = λ γ -> subElTm (app (subElTm_inv (x γ)) (subElTm_inv (y γ)))

-- We omit the constant for lam, since its type requires either the use
-- of an eliminator for the identity type or extensional identity types.
-- The problem is that we need to use the equation (sub tp p ≡ tp), which
-- is validated by the model, even just to state the type.
-- In the paper, we just use the extensionality in the model, so we omit
-- the definition of lam here. Up to the issue with weakening, it is as
-- the interpretation of application.
-- constlamI : {c :{♭} Ctx} -> (a :{♭} c ⊢ tp) -> (b :{♭} c ⊢ tp) ->
--     (cons c (subt tm a) ⊢ subt tm (λ γ -> subElTm p _ (b (p γ)))) -> (c ⊢ subt tm (constarrI a b))


------------------------------------------
-- Rules for domain-level substitutions --
------------------------------------------

subsEmptyI : {c : Ctx} -> El c -> El nil
subsEmptyI _ = terminal

subsVarI : {c :{♭} Ctx} -> El c -> El c
subsVarI = λ phi -> phi

subsWeakI : {c d :{♭} Ctx} -> {a :{♭} Ty c} ->
            (El c -> El d) -> (El (cons c a) -> El d)
subsWeakI sigma = λ phi_x -> sigma (p phi_x)

subsPairI : {c d :{♭} Ctx} -> {a :{♭} Ty d} ->
            (sigma :{♭} El c -> El d) ->  c ⊢ sub a sigma  ->
            (El c -> El (cons d a))
subsPairI sigma t = λ γ -> ElTm.value (subElTm_inv (t γ))
