module Logic.Propositional.Syntax.Context.Base where

open import Agda.Builtin.Nat using (suc; _+_) renaming (Nat to ℕ) public
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Logic.Propositional.Syntax.Formula

infixr 6 _,_
infixr 5 _,,_
infix 4 _∈_ _⊆_
infixr 4 ∈S_

data Context {a : Level} (A : Type a) : ℕ → Type a where
  *   : Context A 0
  _,_ : {n : ℕ} → Formula A → Context A n → Context A (suc n)

_,,_ : {a : Level} {A : Type a} {m n : ℕ} → Context A m → Context A n → Context A (m + n)
* ,, Δ     = Δ
ϕ , Γ ,, Δ = ϕ , (Γ ,, Δ)

data _∈_ {a : Level} {A : Type a} : Formula A → {n : ℕ} → Context A n → Type a where
  ∈Z  : {ϕ : Formula A} {n : ℕ} {Γ : Context A n} → ϕ ∈ ϕ , Γ
  ∈S_ : {ϕ ψ : Formula A} {n : ℕ} {Γ : Context A n} → ϕ ∈ Γ → ϕ ∈ ψ , Γ

data _⊆_ {a : Level} {A : Type a} : {m : ℕ} → Context A m → {n : ℕ} → Context A n → Type a where
  ⊆Z : {n : ℕ} {Δ : Context A n} → * ⊆ Δ
  ⊆S : {ϕ : Formula A} {m n : ℕ} {Γ : Context A m} {Δ : Context A n} → Γ ⊆ Δ → ϕ ∈ Δ → ϕ , Γ ⊆ Δ
