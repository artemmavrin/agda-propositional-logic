module Logic.Propositional.Syntax.Context.Base where

open import Agda.Builtin.Nat using (suc; _+_) renaming (Nat to ℕ) public
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Logic.Propositional.Syntax.Formula

infixr 6 _,_ _,,_
infix 4 _∈_ _⊆_
infixr 4 ∈S_

private
  variable
    a : Level
    A : Type a
    ϕ ψ : Formula A
    m n : ℕ

data Context {a : Level} (A : Type a) : ℕ → Type a where
  *   : Context A 0
  _,_ : Formula A → Context A n → Context A (suc n)

private
  variable
    Γ : Context A m
    Δ : Context A n

data _∈_ {a : Level} {A : Type a} : Formula A → {n : ℕ} → Context A n → Type a where
  ∈Z  : ϕ ∈ ϕ , Γ
  ∈S_ : ϕ ∈ Γ → ϕ ∈ ψ , Γ

data _⊆_ {a : Level} {A : Type a} : {m : ℕ} → Context A m → {n : ℕ} → Context A n → Type a where
  ⊆Z : * ⊆ Δ
  ⊆S : Γ ⊆ Δ → ϕ ∈ Δ → ϕ , Γ ⊆ Δ

_,,_ : Context A m → Context A n → Context A (m + n)
*       ,, Δ = Δ
(ϕ , Γ) ,, Δ = ϕ , Γ ,, Δ
