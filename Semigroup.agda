{-# OPTIONS --universe-polymorphism #-}
module Containers.Semigroup where

open import Level using (_⊔_)
open import Algebra
import Algebra.FunctionProperties as FunctionProperties

open import Data.Empty
open import Data.Nat hiding (fold; _⊔_)
open import Data.Nat.Properties using (commutativeSemiring; i+j≡0⇒i≡0)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec
open import Data.Sum
open import Data.Product

open import Relation.Binary using (Setoid; module Setoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality hiding (setoid)
import Relation.Binary.EqReasoning as EqReasoning

open import Coinduction hiding (fold)

open CommutativeSemiring commutativeSemiring using (+-comm)

-- Full trees, representing associations
data Association : ℕ → Set where
  leaf : Association 1
  node : ∀ {m n} → (l : Association m) → (r : Association n) → Association (m + n)

leftA : ∀ {n} → Association (1 + n)
leftA {zero} = leaf
leftA {suc n} rewrite +-comm 1 n = node (leftA {n}) leaf

rightA : ∀ {n} → Association (1 + n)
rightA {zero} = leaf
rightA {suc n} = node leaf rightA


fold : ∀ {n} {a} {A : Set a} → Association n → (A → A → A) → Vec A n → A
fold leaf _∙_ (x ∷ xs) = x
fold (node {m} l r) _∙_ xs with splitAt m xs
...                        | ls , rs , pf = fold l _∙_ ls ∙ fold r _∙_ rs

foldl₁-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) → (xs : Vec A (1 + n)) → foldl₁ f xs ≡ fold leftA f xs
foldl₁-fold {zero} f (x ∷ []) = refl
foldl₁-fold {suc n} f xs rewrite +-comm 1 n with splitAt (suc n) xs
foldl₁-fold {suc n} f .(ls ++ r ∷ [])           | ls , r ∷ [] , refl rewrite sym (foldl₁-fold f ls) = foldl₁-snoc f r ls
  where
  foldl₁-snoc : ∀ {a} {A : Set a} {n} f x (xs : Vec A (1 + n)) → foldl₁ f (xs ++ x ∷ []) ≡ f (foldl₁ f xs) x
  foldl₁-snoc f x₀ (x₁ ∷ []) = refl
  foldl₁-snoc f x₀ (x₁ ∷ x ∷ xs) = foldl₁-snoc f x₀ (f x₁ x ∷ xs)

foldr₁-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) → (xs : Vec A (1 + n)) → foldr₁ f xs ≡ fold rightA f xs
foldr₁-fold f (x ∷ []) = refl
foldr₁-fold f (x₀ ∷ x₁ ∷ xs) = cong (f x₀) (foldr₁-fold f (x₁ ∷ xs))

module Associative-Proof {a b} (S : Semigroup a b) where
  open Semigroup S renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

  lemma : ∀ {n} → Association n → ∃ (λ m → n ≡ suc m)
  lemma leaf = zero , refl
  lemma (node l r) with lemma l
  ...               | x , refl = x + _ , refl

  foldr₁-lemma : ∀ {m n} (xs : Vec Carrier (1 + m)) (ys : Vec Carrier (1 + n)) p q → p ≈ foldr₁ _∙_ xs → q ≈ foldr₁ _∙_ ys → p ∙ q ≈ foldr₁ _∙_ (xs ++ ys)
  foldr₁-lemma (x ∷ []) (y ∷ ys) p q pf₁ pf₂ = ∙-cong pf₁ pf₂
  foldr₁-lemma (x₀ ∷ x₁ ∷ []) (y ∷ ys) p q pf₁ pf₂ = ≈-trans (∙-cong pf₁ pf₂) (assoc x₀ x₁ (foldr₁ _∙_ (y ∷ ys)))
  foldr₁-lemma (x₀ ∷ x₁ ∷ x ∷ xs) (y ∷ ys) p q pf₁ pf₂ = 
      begin
        p ∙ q
      ≈⟨ ∙-cong pf₁ pf₂ ⟩
        x₀ ∙ (x₁ ∙ foldr₁ _∙_ (x ∷ xs)) ∙ foldr₁ _∙_ (y ∷ ys)
      ≈⟨ ∙-cong (≈-sym (assoc x₀ x₁ (foldr₁ _∙_ (x ∷ xs)))) ≈-refl ⟩
        x₀ ∙ x₁ ∙ foldr₁ _∙_ (x ∷ xs) ∙ foldr₁ _∙_ (y ∷ ys)
      ≈⟨ assoc (x₀ ∙ x₁) (foldr₁ _∙_ (x ∷ xs)) (foldr₁ _∙_ (y ∷ ys)) ⟩
        x₀ ∙ x₁ ∙ (foldr₁ _∙_ (x ∷ xs) ∙ foldr₁ _∙_ (y ∷ ys))
      ≈⟨ ∙-cong ≈-refl (foldr₁-lemma (x ∷ xs) (y ∷ ys) (foldr₁ _∙_ (x ∷ xs)) (foldr₁ _∙_ (y ∷ ys)) ≈-refl ≈-refl) ⟩
        x₀ ∙ x₁ ∙ foldr₁ _∙_ (x ∷ xs ++ y ∷ ys)
      ≈⟨ assoc x₀ x₁ (foldr₁ _∙_ (x ∷ xs ++ y ∷ ys)) ⟩
        x₀ ∙ (x₁ ∙ foldr₁ _∙_ (x ∷ xs ++ y ∷ ys))
      ∎
    where open EqReasoning setoid

  foldr₁-equivalent : ∀ {n} (p : Association (1 + n)) (xs : Vec Carrier (1 + n)) → fold p _∙_ xs ≈ foldr₁ _∙_ xs
  foldr₁-equivalent p zs = helper p zs zs (≋-refl zs)
    where
    open import Data.Vec.Equality
    open Equality setoid renaming (_≈_ to _≋_; refl to ≋-refl)
    open EqReasoning setoid
  
    foldr₁-cong : ∀ {m n} {xs : Vec Carrier (1 + m)} {ys : Vec Carrier (1 + n)} → xs ≋ ys → foldr₁ _∙_ xs ≈ foldr₁ _∙_ ys
    foldr₁-cong (x≈y ∷-cong []-cong) = x≈y
    foldr₁-cong (x₀≈y₀ ∷-cong (x₁≈y₁ ∷-cong xs≋ys)) = ∙-cong x₀≈y₀ (foldr₁-cong (x₁≈y₁ ∷-cong xs≋ys))

    helper : ∀ {n m} (p : Association n) → (xs : Vec Carrier n) → (ys : Vec Carrier (1 + m)) → xs ≋ ys → fold p _∙_ xs ≈ foldr₁ _∙_ ys
    helper leaf (x ∷ xs) (y ∷ []) (x≈y ∷-cong xs≋ys) = x≈y
    helper leaf (x ∷ xs) (y₀ ∷ y₁ ∷ ys) (x≈y ∷-cong ())
    helper (node {m} l r) xs ys xs≋ys with lemma l | lemma r | splitAt m xs
    helper (node l r) .(ls ++ rs) ys xs≋ys | ln , refl | rn , refl | ls , rs , refl = 
      begin
        fold l _∙_ ls ∙ fold r _∙_ rs
      ≈⟨ ∙-cong (helper l ls ls (≋-refl ls)) (helper r rs rs (≋-refl rs)) ⟩
        foldr₁ _∙_ ls ∙ foldr₁ _∙_ rs
      ≈⟨ foldr₁-lemma ls rs (foldr₁ _∙_ ls) (foldr₁ _∙_ rs) ≈-refl ≈-refl ⟩
        foldr₁ _∙_ (ls ++ rs)
      ≈⟨ foldr₁-cong xs≋ys ⟩
        foldr₁ _∙_ ys
      ∎

  fold-associative : ∀ {n} (p q : Association n) (xs : Vec Carrier n) → fold p _∙_ xs ≈ fold q _∙_ xs
  fold-associative p q xs with lemma p
  ...                     | pn , refl = ≈-trans (foldr₁-equivalent p xs) (≈-sym (foldr₁-equivalent q xs))


{-
data PairwisePermutation : ∀ {n} → Association n → Set where
  leaf : PairwisePermutation leaf
  node : ∀ {m n} {a : Association m} {b : Association n} → (l : PairwisePermutation a) → (r : PairwisePermutation b) → PairwisePermutation (node a b)
  flip : ∀ {n m} {a : Association m} {b : Association n} → (l : PairwisePermutation a) → (r : PairwisePermutation b) → PairwisePermutation (node b a)

foldPermute : ∀ {n} {a} {A : Set a} {a : Association n} (p : PairwisePermutation a) → (A → A → A) → Vec A n → A
foldPermute leaf f (x ∷ xs) = x
foldPermute (node {m} l r) _∙_ xs with splitAt m xs
...                               | ls , rs , pf = foldPermute l _∙_ ls ∙ foldPermute r _∙_ rs
foldPermute (flip {n} l r) _∙_ xs with splitAt n xs
...                               | ls , rs , pf = foldPermute r _∙_ ls ∙ foldPermute l _∙_ rs
-}

