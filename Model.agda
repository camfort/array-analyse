module Model where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.List.Any

open import Function
open import Data.Product as Prod using (∃; _×_; _,_)
open import Level using (Level; _⊔_)
open import Size

Depth : Set
Depth = ℕ

Dimension : Set
Dimension = ℕ

infix 4 _∈_ 
_∈_ : {A : Set} -> A → List A → Set _
x ∈ xs = Any (_≡_ x) xs

-- Imported from CamFort's Stencils.hs
data Spec : {i : Size} -> Set where
  Reflexive : {i : Size} -> Spec {i}
  Forward   : {i : Size} -> Depth -> List Dimension -> Spec {↑ i}

⟦_⟧ : Spec -> (((d : Dimension) -> Depth) -> ℕ -> Set)
⟦ Reflexive          ⟧        = λ ix m -> ((d : Dimension) -> ix d ≡ 0)
⟦ Forward zero dims  ⟧        = λ ix m -> ((d : Dimension) -> ix d ≡ 0) -- ⟦ Reflexive ⟧
⟦ Forward (suc depth) dims ⟧ = λ ix m -> ((d : Dimension) -> (d ∈ dims -> ix d ≤ (suc depth))) -- × (⟦ Forward depth dims ⟧ ix m)

forwardCoalesceL : ∀ {depth : ℕ} {dims : List Dimension} ->
                   ∀ {ix : ((d : Dimension) -> Depth)} {m : ℕ} ->
                      (((⟦ Forward depth dims ⟧ ix m) × (⟦ Forward (suc depth) dims ⟧ ix m)) ≡ ⟦ Forward (suc depth) dims ⟧ ix m)
forwardCoalesceL {depth} {dims} {ix} {m} = {!!}

{-
forwardCoalesceR : ∀ {depth : ℕ} {dims : List Dimension} ->
                   ∀ {ix : ((d : Dimension) -> Depth)} {m : ℕ} ->
                      (⟦ Forward (suc depth) dims ⟧ ix m -> ((⟦ Forward depth dims ⟧ ix m) × (⟦ Forward (suc depth) dims ⟧ ix m)))
forwardCoalesceR {depth} {dims} {ix} {m} (p1 , p2) = (p2 , (p1 , p2))

-}

