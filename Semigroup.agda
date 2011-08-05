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

open CommutativeSemiring commutativeSemiring using (+-identity; +-comm; distrib)

-- This belongs elsewhere
foldl-lemma : ∀ {a b} {A : Set a} {B : ℕ → Set b} {f : ∀ {n} → B n → A → B (suc n)} {z : B 0} {n} {x} (xs : Vec A n) → f (foldl B f z xs) x ≡ foldl B f z (xs ∷ʳ x)
foldl-lemma [] = refl
foldl-lemma {B = B} (y ∷ ys) = foldl-lemma {B = λ n → B (suc n)} ys

foldl-elim : ∀ {a b c} {A : Set a} {B : ℕ → Set b} (P : ∀ {n} → Vec A n → B n → Set c) {f : ∀ {n} → B n → A → B (1 + n)} {z : B 0} 
           → P [] z
           → (∀ {n x′ z′} {xs′ : Vec A n} → P xs′ z′ → P (xs′ ∷ʳ x′) (f z′ x′)) 
           → ∀ {n} (xs : Vec A n) → P xs (foldl B f z xs)
foldl-elim P Pz Ps [] = Pz
foldl-elim {A} {B} P {f} {z} Pz Ps (x ∷ xs) = foldl-elim (λ xs′ → P (x ∷ xs′)) (Ps Pz) Ps xs

-- Full trees, representing associations
data Association : ℕ → Set where
  leaf : Association 1
  node : ∀ {m n} → (l : Association m) → (r : Association n) → Association (m + n)

cons : ∀ {n} → Association n → Association (1 + n)
cons leaf = node leaf leaf
cons (node l r) = node (cons l) r

1+m+n≡m+1+n : ∀ m n → 1 + (m + n) ≡ m + (1 + n)
1+m+n≡m+1+n zero n = refl
1+m+n≡m+1+n (suc m) n = cong suc (1+m+n≡m+1+n m n)

snoc : ∀ {n} → Association n → Association (1 + n)
snoc leaf = node leaf leaf
snoc (node {m} {n} l r) rewrite 1+m+n≡m+1+n m n = node l (snoc r)

lemma : ∀ {n} → Association n → ∃ (λ m → n ≡ suc m)
lemma leaf = zero , refl
lemma (node l r) with lemma l
...               | x , refl = x + _ , refl

+-one : ∀ n m → n + m ≡ 1 → n ≡ 0 ⊎ m ≡ 0
+-one zero m pf = inj₁ refl
+-one (suc n) zero pf = inj₂ refl
+-one (suc n) (suc m) pf rewrite +-comm n (suc m) with pf
...                                               | ()

¬Association0 : Association 0 → ⊥
¬Association0 x with lemma x
...             | n , ()

Association-leaf : (a : Association 1) → a ≡ leaf
Association-leaf a = ≅-to-≡ (helper a refl)
  where
  open import Relation.Binary.HeterogeneousEquality
  helper : ∀ {n} → (a : Association n) → n ≡ 1 → a ≅ leaf
  helper leaf n≡1 = refl
  helper (node {m} {n} l r) n≡1 with +-one m n n≡1
  ...                           | inj₁ p rewrite p = ⊥-elim (¬Association0 l)
  ...                           | inj₂ q rewrite q = ⊥-elim (¬Association0 r)


leftA : ∀ {n} → Association (1 + n)
leftA {zero} = leaf
leftA {suc n} rewrite +-comm 1 n = node (leftA {n}) leaf

rightA : ∀ {n} → Association (1 + n)
rightA {zero} = leaf
rightA {suc n} = node leaf rightA

data Parity : ℕ → Set where
  even : ∀ n → Parity (2 * n)
  odd  : ∀ n → Parity (1 + 2 * n)

parity : ∀ n → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(n + (n + 0))) | even n = odd n
parity (suc .(suc (n + (n + 0)))) | odd n rewrite sym (proj₁ distrib 2 1 n) = even (suc n)

foldParity : ∀ {a} (P : ℕ → Set a) → (∀ n → P n → P (2 * n)) → (∀ n → P n → P (1 + 2 * n)) → ∀ n → P n
foldParity P e o n with parity n
foldParity P e o .(n + (n + 0)) | even n = e n {!!}
foldParity P e o .(suc (n + (n + 0))) | odd n = o n ?

balancedA : ∀ {n} → Association (1 + n)
balancedA {zero} = leaf
balancedA {suc n} with parity n
balancedA {suc .(n + (n + 0))} | even n rewrite sym (proj₁ distrib 2 1 n) | proj₂ +-identity n = node (balancedA {n}) (balancedA {n})
balancedA {suc .(suc (n + (n + 0)))} | odd n = {!!}

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
