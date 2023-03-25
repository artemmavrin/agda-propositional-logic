module Logic.Propositional.Syntax.Context.Properties where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ) public
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Logic.Propositional.Syntax.Context.Base
open import Logic.Propositional.Syntax.Formula

private
  variable
    a : Level
    A : Type a
    ϕ ψ : Formula A
    m n p : ℕ
    Γ : Context A m
    Δ : Context A n
    Θ : Context A p

⊆-elim : Γ ⊆ Δ → ϕ ∈ Γ → ϕ ∈ Δ
⊆-elim (⊆S _ q) ∈Z     = q
⊆-elim (⊆S p _) (∈S r) = ⊆-elim p r

⊆-intro : (∀ {ϕ} → ϕ ∈ Γ → ϕ ∈ Δ) → Γ ⊆ Δ
⊆-intro {Γ = *} _ = ⊆Z
⊆-intro {Γ = ϕ , Γ} p = ⊆S (⊆-intro (λ q → p (∈S q))) (p ∈Z)

⊆-append : Γ ⊆ Δ → Γ ⊆ ϕ , Δ
⊆-append ⊆Z              = ⊆Z
⊆-append (⊆S ⊆Z r)       = ⊆S ⊆Z (∈S r)
⊆-append (⊆S (⊆S p q) r) = ⊆S (⊆S (⊆-append p) (∈S q)) (∈S r)

⊆-extend : Γ ⊆ Δ → ϕ , Γ ⊆ ϕ , Δ
⊆-extend ⊆Z       = ⊆S ⊆Z ∈Z
⊆-extend (⊆S p q) = ⊆S (⊆S (⊆-append p) (∈S q)) ∈Z

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = *}     = ⊆Z
⊆-refl {Γ = _ , _} = ⊆-extend ⊆-refl

⊆-trans : Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
⊆-trans ⊆Z       _ = ⊆Z
⊆-trans (⊆S p q) r = ⊆S (⊆-trans p r) (⊆-elim r q)

⊆-swap : ϕ , ψ , Γ ⊆ ψ , ϕ , Γ
⊆-swap = ⊆S (⊆S (⊆-append (⊆-append ⊆-refl)) ∈Z) (∈S ∈Z)

⊑-implies-⊆ : Γ ⊑ Δ → Γ ⊆ Δ
⊑-implies-⊆ ⊑Z = ⊆-refl
⊑-implies-⊆ ⊑S = ⊆-append (⊆-refl)
