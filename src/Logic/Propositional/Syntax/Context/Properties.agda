module Logic.Propositional.Syntax.Context.Properties where

open import Agda.Primitive using (Level) renaming (Set to Type)

open import Data.Nat
open import Logic.Propositional.Syntax.Context.Base
open import Logic.Propositional.Syntax.Formula

private
  variable
    a : Level
    A : Type a
    ϕ ψ : Formula A
    m n k : ℕ
    Γ : Context A m
    Δ : Context A n
    Ξ : Context A k

∈-lemma : ϕ ∈ Γ ,, ϕ , Δ
∈-lemma {Γ = *}     = ∈Z
∈-lemma {Γ = _ , Γ} = ∈S ∈-lemma

∈-concat-front : ϕ ∈ Γ → ϕ ∈ Δ ,, Γ
∈-concat-front {Δ = *}                 ∈Z       = ∈Z
∈-concat-front {Δ = _ , _}             ∈Z       = ∈S (∈-concat-front ∈Z)
∈-concat-front {Γ = _ , _} {Δ = *}     (∈S ϕ∈Γ) = ∈S ϕ∈Γ
∈-concat-front {Γ = _ , _} {Δ = _ , _} (∈S ϕ∈Γ) = ∈S (∈-concat-front (∈S ϕ∈Γ))

∈-concat-back : ϕ ∈ Γ → ϕ ∈ Γ ,, Δ
∈-concat-back ∈Z     = ∈Z
∈-concat-back (∈S p) = ∈S (∈-concat-back p)

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

⊆-concat-front : Γ ⊆ Δ → Γ ⊆ Ξ ,, Δ
⊆-concat-front {Ξ = *}     Γ⊆Δ = Γ⊆Δ
⊆-concat-front {Ξ = _ , _} Γ⊆Δ = ⊆-append (⊆-concat-front Γ⊆Δ)

⊆-concat-back : Γ ⊆ Δ → Γ ⊆ Δ ,, Ξ
⊆-concat-back {Γ = *}     {Δ = *}     ⊆Z               = ⊆Z
⊆-concat-back {Γ = *}     {Δ = _ , _} _                = ⊆Z
⊆-concat-back {Γ = _ , _} {Δ = _ , _} (⊆S Γ⊆δ,Δ γ∈δ,Δ) = ⊆S (⊆-concat-back Γ⊆δ,Δ) (∈-concat-back γ∈δ,Δ)

⊆-concat-extend-front : Γ ⊆ Δ → Ξ ,, Γ ⊆ Ξ ,, Δ
⊆-concat-extend-front {Ξ = *}     Γ⊆Δ = Γ⊆Δ
⊆-concat-extend-front {Ξ = _ , _} Γ⊆Δ = ⊆-extend (⊆-concat-extend-front Γ⊆Δ)

⊆-concat-extend-back : Γ ⊆ Δ → Γ ,, Ξ ⊆ Δ ,, Ξ
⊆-concat-extend-back ⊆Z       = ⊆-concat-front ⊆-refl
⊆-concat-extend-back (⊆S p q) = ⊆S (⊆-concat-extend-back p) (∈-concat-back q)

⊆-intro : ({θ : Formula A} → θ ∈ Γ → θ ∈ Δ) → Γ ⊆ Δ
⊆-intro {Γ = *}     _ = ⊆Z
⊆-intro {Γ = _ , _} p = ⊆S (⊆-intro (λ x -> p (∈S x))) (p ∈Z)

⊆-elim : Γ ⊆ Δ → ϕ ∈ Γ → ϕ ∈ Δ
⊆-elim (⊆S _ q) ∈Z     = q
⊆-elim (⊆S p _) (∈S r) = ⊆-elim p r

⊆-trans : Γ ⊆ Δ → Δ ⊆ Ξ → Γ ⊆ Ξ
⊆-trans ⊆Z           Δ⊆Ξ = ⊆Z
⊆-trans (⊆S Γ⊆Δ ϕ∈Δ) Δ⊆Ξ = ⊆S (⊆-trans Γ⊆Δ Δ⊆Ξ) (⊆-elim Δ⊆Ξ ϕ∈Δ)

⊆-swap-front-to-middle : ϕ , Γ ,, Δ ⊆ Γ ,, ϕ , Δ
⊆-swap-front-to-middle {Γ = *}     = ⊆-refl
⊆-swap-front-to-middle {Γ = _ , _} = ⊆S (⊆-extend (⊆-concat-extend-front (⊆-append ⊆-refl))) (∈S ∈-lemma)

⊆-swap-middle-to-front : Γ ,, ϕ , Δ ⊆ ϕ , Γ ,, Δ
⊆-swap-middle-to-front {Γ = *}             = ⊆-refl
⊆-swap-middle-to-front {Γ = _ , Γ} {Δ = Δ} = ⊆S (⊆-trans ⊆-swap-middle-to-front (⊆-concat-extend-back {Ξ = Δ} (⊆-extend (⊆-append ⊆-refl)))) (∈S ∈Z)
