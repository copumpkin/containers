{-# OPTIONS --universe-polymorphism #-}
module Containers.CommutativeSemigroup where

open import Algebra
import Algebra.FunctionProperties as FunctionProperties

open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Data.Nat hiding (fold)
open import Data.Nat.Properties using (commutativeSemiring; i+j≡0⇒i≡0)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec

open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (setoid to ≡-setoid)
import Relation.Binary.EqReasoning as EqReasoning

open import Containers.Semigroup

foldr-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) z (xs : Vec A n) → foldr _ f z xs ≡ fold rightA f (xs ∷ʳ z)
foldr-fold f z [] = refl
foldr-fold f z (x ∷ xs) = cong (f x) (foldr-fold f z xs)

foldl-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) z (xs : Vec A n) → foldl _ f z xs ≡ fold leftA f (z ∷ xs)
foldl-fold f z xs rewrite sym (foldl₁-fold f (z ∷ xs)) = refl

infixr 5 _∷_

data Permutation : ℕ → Set where
  []  : Permutation 0
  _∷_ : {n : ℕ} → (p : Fin (1 + n)) → (ps : Permutation n) → Permutation (1 + n)

max : ∀ {n} → Fin (suc n)
max {zero} = zero
max {suc n} = suc max

idP : ∀ {n} → Permutation n
idP {zero} = []
idP {suc n} = zero ∷ idP

reverseP : ∀ {n} → Permutation n
reverseP {zero} = []
reverseP {suc n} = max ∷ reverseP

insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
insert xs zero a = a ∷ xs
insert [] (suc ()) a
insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

permute : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
permute [] [] = []
permute (p ∷ ps) (x ∷ xs) = insert (permute ps xs) p x

idP-id : ∀ {n} {a} {A : Set a} (xs : Vec A n) → permute idP xs ≡ xs
idP-id [] = refl
idP-id (x ∷ xs) = cong (_∷_ x) (idP-id xs)

insert-max : ∀ {n} {a} {A : Set a} (ys : Vec A n) x → insert ys max x ≡ ys ∷ʳ x
insert-max [] x = refl
insert-max (y ∷ ys) x = cong (_∷_ y) (insert-max ys x)

reverse-∷ʳ : ∀ {n} {a} {A : Set a} (ys : Vec A n) x → reverse ys ∷ʳ x ≡ reverse (x ∷ ys)
reverse-∷ʳ {A = A} xs x = 
  foldl-elim
    (λ xs b → b ∷ʳ x ≡ reverse (x ∷ xs)) 
    refl 
    (λ {_} {_} {_} {xs} eq → trans (cong (_∷_ _) eq) (foldl-lemma {B = λ n -> Vec A (suc n)} xs))
    xs

reverseP-reverse : ∀ {n} {a} {A : Set a} (xs : Vec A n) → permute reverseP xs ≡ reverse xs
reverseP-reverse [] = refl
reverseP-reverse {suc n} {_} {A} (x ∷ xs) = 
    begin
      insert (permute reverseP xs) max x
    ≈⟨ insert-max (permute reverseP xs) x ⟩
      permute reverseP xs ∷ʳ x
    ≈⟨ cong (λ q → q ∷ʳ x) (reverseP-reverse xs) ⟩
      reverse xs ∷ʳ x
    ≈⟨ reverse-∷ʳ xs x ⟩
      reverse (x ∷ xs)
    ∎
  where open EqReasoning (≡-setoid (Vec A (1 + n)))


module Commutative-Proof {a b} (S : Semigroup a b) where
  open Semigroup S renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  module Inner (∙-comm : FunctionProperties.Commutative _≈_ _∙_) where
    open EqReasoning setoid
    open Associative-Proof S

    open CommutativeSemiring commutativeSemiring using (+-comm)

    foldr₁-∷ʳ : ∀ {n} x (ys : Vec Carrier (1 + n)) → foldr₁ _∙_ ys ∙ x ≈ foldr₁ _∙_ (ys ∷ʳ x)
    foldr₁-∷ʳ x (y ∷ []) = ≈-refl
    foldr₁-∷ʳ x (y₀ ∷ y₁ ∷ ys) = ≈-trans (assoc y₀ (foldr₁ _∙_ (y₁ ∷ ys)) x) (∙-cong ≈-refl (foldr₁-∷ʳ x (y₁ ∷ ys)))

    foldr₁-flip : ∀ {n} (zs : Vec Carrier n) x y → x ∙ foldr₁ _∙_ (y ∷ zs) ≈ y ∙ foldr₁ _∙_ (x ∷ zs)
    foldr₁-flip [] x y = ∙-comm x y
    foldr₁-flip (z ∷ zs) x y =
      begin
        x ∙ (y ∙ foldr₁ _∙_ (z ∷ zs))
      ≈⟨ ≈-sym (assoc x y _) ⟩
        (x ∙ y) ∙ foldr₁ _∙_ (z ∷ zs)
      ≈⟨ ∙-cong (∙-comm x y) ≈-refl ⟩
        (y ∙ x) ∙ foldr₁ _∙_ (z ∷ zs)
      ≈⟨ assoc y x _ ⟩
        y ∙ (x ∙ foldr₁ _∙_ (z ∷ zs))
      ∎

    foldr₁-∷ : ∀ {n} (ys : Vec Carrier (1 + n)) x → foldr₁ _∙_ (x ∷ ys) ≈ x ∙ foldr₁ _∙_ ys
    foldr₁-∷ (y ∷ ys) x = ≈-refl

    foldr₁-insert : ∀ {n} (ys : Vec Carrier n) (i : Fin (1 + n)) x → foldr₁ _∙_ (x ∷ ys) ≈ foldr₁ _∙_ (insert ys i x)
    foldr₁-insert [] zero x = ≈-refl
    foldr₁-insert [] (suc ()) x
    foldr₁-insert (y ∷ ys) zero x = ≈-refl
    foldr₁-insert (y ∷ ys) (suc zero) x = foldr₁-flip ys x y
    foldr₁-insert (y ∷ ys) (suc (suc i)) x = 
      begin
        x ∙ foldr₁ _∙_ (y ∷ ys)
      ≈⟨ foldr₁-flip ys x y ⟩
        y ∙ foldr₁ _∙_ (x ∷ ys)
      ≈⟨ ∙-cong ≈-refl (foldr₁-insert ys (suc i) x) ⟩
        y ∙ foldr₁ _∙_ (insert ys (suc i) x)
      ≈⟨ ≈-sym (foldr₁-∷ (insert ys (suc i) x) y) ⟩
        foldr₁ _∙_ (y ∷ insert ys (suc i) x)
      ∎

    foldr₁-permute : ∀ {n} p (xs : Vec Carrier (1 + n)) → foldr₁ _∙_ xs ≈ foldr₁ _∙_ (permute p xs)
    foldr₁-permute (zero ∷ []) (x ∷ []) = ≈-refl
    foldr₁-permute (suc () ∷ []) (x ∷ [])
    foldr₁-permute (p₀ ∷ p₁ ∷ ps) (x₀ ∷ x₁ ∷ xs) = 
      begin
        x₀ ∙ foldr₁ _∙_ (x₁ ∷ xs)
      ≈⟨ ∙-cong ≈-refl (foldr₁-permute (zero ∷ ps) (x₁ ∷ xs)) ⟩
        x₀ ∙ foldr₁ _∙_ (permute (zero ∷ ps) (x₁ ∷ xs))
      ≈⟨ ∙-cong ≈-refl (foldr₁-insert (permute ps xs) p₁ x₁) ⟩
        x₀ ∙ foldr₁ _∙_ (insert (permute ps xs) p₁ x₁)
      ≈⟨ ≈-sym (foldr₁-∷ (insert (permute ps xs) p₁ x₁) x₀) ⟩
        foldr₁ _∙_ (x₀ ∷ insert (permute ps xs) p₁ x₁)
      ≈⟨ foldr₁-insert (insert (permute ps xs) p₁ x₁) p₀ x₀ ⟩
        foldr₁ _∙_ (insert (permute (p₁ ∷ ps) (x₁ ∷ xs)) p₀ x₀)
      ∎

    fold-permute : ∀ {n} (a b : Association n) (p : Permutation n) (xs : Vec Carrier n) → fold a _∙_ xs ≈ fold b _∙_ (permute p xs)
    fold-permute a b p xs with lemma a
    ...                   | na , refl = 
      begin
        fold a _∙_ xs
      ≈⟨ foldr₁-equivalent a xs ⟩
        foldr₁ _∙_ xs
      ≈⟨ foldr₁-permute p xs ⟩
        foldr₁ _∙_ (permute p xs)
      ≈⟨ ≈-sym (foldr₁-equivalent b (permute p xs)) ⟩
        fold b _∙_ (permute p xs)
      ∎



  open Inner public



test : Vec ℕ 5
test = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

test₀ : permute reverseP test ≡ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test₀ = refl


postulate _^_ : ℕ → ℕ → ℕ

test₁ : fold leftA _^_ test ≡ (((1 ^ 2) ^ 3) ^ 4) ^ 5
test₁ = refl

test₂ : fold rightA _^_ test ≡ 1 ^ (2 ^ (3 ^ (4 ^ 5)))
test₂ = refl
