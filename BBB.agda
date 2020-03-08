module BBB where

open import Relation.Binary.PropositionalEquality

data nat : Set where
  ze : nat
  su : nat → nat

data fin : nat → Set where
  ze : ∀ {n} → fin (su n)
  su : ∀ {n} → fin n → fin (su n)

data _⊆_ : nat → nat → Set where
  bot : ze ⊆ ze
  skip : ∀ {m n} → m ⊆ n → m ⊆ (su n)
  keep : ∀ {m n} → m ⊆ n → su m ⊆ (su n)

lift⊆ : ∀ {m n} → m ⊆ n → fin m → fin n
lift⊆ (skip x) i = su (lift⊆ x i)
lift⊆ (keep x) ze = ze
lift⊆ (keep x) (su i) = su (lift⊆ x i)

data bool : Set where true false : bool

data vec (A : Set) : nat → Set where
  [] : vec A ze
  _∷_ : ∀ {n} → A → vec A n → vec A (su n)

data _⇒_ {A} : ∀ {m n} → vec A m → vec A n → Set where
  nil :                                                       []       ⇒ []
  con : ∀ {m n} {xs : vec A m} {ys : vec A n} {v} → xs ⇒ ys → (v ∷ xs) ⇒ (v ∷ ys)
  add : ∀ {m n} {xs : vec A m} {ys : vec A n} {v} → xs ⇒ ys → xs       ⇒ (v ∷ ys)
  del : ∀ {m n} {xs : vec A m} {ys : vec A n} {v} → xs ⇒ ys → (v ∷ xs) ⇒ ys

record presord (A : Set) (R : A → A → Set) : Set where
  field
    tra : ∀ {a b c} → R a b → R b c → R a c



{-data patch {A} : ∀ {m n} → vec A n → vec A m → Set where
  nil : patch [] []
  add : ∀ {m n} {xs : vec A m} {ys : vec A n} {v} → patch xs ys → patch xs (v ∷ ys)
  con : ∀ {m n} {xs : vec A m} {ys : vec A n} {v} → patch xs ys → patch (v ∷ xs) (v ∷ ys)

get : ∀ {A n} → vec A n → fin n → A
get (x ∷ xs) ze = x
get (x ∷ xs) (su i) = get xs i

data edit (A : Set) : nat → nat → Set where
  ins : ∀ {n} → fin (su n) → A → edit A n (su n)
  del : ∀ {n} → fin (su n) → edit A (su n) n

apply : ∀ {A m n} → vec A n → edit A n m → vec A m
apply xs       (ins ze a) = a ∷ xs
apply (x ∷ xs) (ins (su i) a) = x ∷ apply xs (ins i a)
apply (x ∷ xs) (del ze) = xs
apply (_∷_ {su _} x xs) (del (su i)) = x ∷ apply xs (del i)-}

{-del : ∀ {A n} → vec A (su n) → fin (su n) → vec A n
del (x ∷ xs) ze = xs
del {n = su n} (x ∷ xs) (su i) = x ∷ del xs i

ins : ∀ {A n} → vec A n → fin (su n) → A → vec A (su n)
ins xs ze a = a ∷ xs
ins (x ∷ xs) (su i) a = x ∷ ins xs i a-}

  
{-record file (A : Set) : Set where
  field
    len : nat
    lines : fin len → A
open file public

record patch {A} (F G : file A) : Set where
  field
    map : len F ⊆ len G
    coh : ∀ i → lines F i ≡ lines G (lift⊆ map i)
open patch public-}
