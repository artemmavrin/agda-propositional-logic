open import Agda.Primitive using (Level) renaming (Set to Type)

module Logic.Propositional.Syntax.Context.Base {a : Level} (Atom : Type a) where

open import Logic.Propositional.Syntax.Formula (Atom)

infixl 6 _,_
infixl 5 _,,_
infix 4 _∈_ _⊆_
infixr 4 ∈S_

data Context : Type a where
  ∅   : Context
  _,_ : Context → Formula → Context

private
  variable
    A B : Formula
    Γ Δ : Context

_,,_ : Context → Context → Context
Γ ,, ∅     = Γ
Γ ,, Δ , A = (Γ ,, Δ) , A

data _∈_ : Formula → Context → Type a where
  ∈Z  : A ∈ Γ , A
  ∈S_ : A ∈ Γ → A ∈ Γ , B

data _⊆_ : Context → Context → Type a where
  ⊆Z : ∅ ⊆ Δ
  ⊆S : Γ ⊆ Δ → A ∈ Δ → Γ , A ⊆ Δ
