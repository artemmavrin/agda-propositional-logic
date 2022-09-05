module Logic.Propositional.NaturalDeduction.Judgement.AdmissibleRules where

open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to _∙_)
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Data.Nat
open import Logic.Propositional.Syntax
open import Logic.Propositional.NaturalDeduction.Judgement.Base

private
  ⊢-struct-impl : {a : Level} {A : Type a} {ϕ : Formula A} {m n : ℕ}
                  {Γ : Context A m} {Δ : Context A n} {s : Shape}
                  → Γ ⊆ Δ → Γ ⊢ ϕ [ s ] → Δ ⊢ ϕ [ s ]
  ⊢-struct-impl Γ⊆Δ (axiom ϕ∈Γ)        = axiom (⊆-elim Γ⊆Δ ϕ∈Γ)
  ⊢-struct-impl Γ⊆Δ (⊃-intro Γ,ϕ⊢ψ)    = ⊃-intro (⊢-struct-impl (⊆-extend Γ⊆Δ) Γ,ϕ⊢ψ)
  ⊢-struct-impl Γ⊆Δ (⊃-elim Γ⊢ϕ⊃ψ Γ⊢ϕ) = ⊃-elim (⊢-struct-impl Γ⊆Δ Γ⊢ϕ⊃ψ) (⊢-struct-impl Γ⊆Δ Γ⊢ϕ)

⊢-struct : {a : Level} {A : Type a} {ϕ : Formula A} {m n : ℕ} {Γ : Context A m} {Δ : Context A n}
  → Γ ⊆ Δ
  → Γ ⊢ ϕ
    -----
  → Δ ⊢ ϕ
⊢-struct Γ⊆Δ Γ⊢ϕ = _ ∙ ⊢-struct-impl Γ⊆Δ (snd Γ⊢ϕ)

private
  ⊢-subst-impl : {a : Level} {A : Type a} {ϕ ψ : Formula A} {n : ℕ} {Γ : Context A n} {s t : Shape}
                 → Γ ⊢ ϕ [ s ] → ϕ , Γ ⊢ ψ [ t ] → Σ Shape (Γ ⊢ ψ [_])
  ⊢-subst-impl Γ⊢ϕ ϕ,Γ⊢ψ@(axiom ∈Z) = shape-of Γ⊢ϕ ∙ Γ⊢ϕ
  ⊢-subst-impl Γ⊢ϕ ϕ,Γ⊢ψ@(axiom (∈S ψ∈Γ)) = 𝟘 ∙ axiom ψ∈Γ
  ⊢-subst-impl Γ⊢ϕ ϕ,Γ⊢α⊃β@(⊃-intro α,ϕ,Γ⊢β) = _ ∙ ⊃-intro α,Γ⊢β where
    α,Γ⊢ϕ   = ⊢-struct-impl (⊆-append ⊆-refl) Γ⊢ϕ
    ϕ,α,Γ⊢β = ⊢-struct-impl (⊆S (⊆S (⊆-append (⊆-append ⊆-refl)) ∈Z) (∈S ∈Z)) α,ϕ,Γ⊢β
    α,Γ⊢β   = snd (⊢-subst-impl α,Γ⊢ϕ ϕ,α,Γ⊢β)
  ⊢-subst-impl Γ⊢ϕ ϕ,Γ⊢ψ@(⊃-elim ϕ,Γ⊢θ⊃ψ ϕ,Γ⊢θ) = _ ∙ ⊃-elim Γ⊢θ⊃ψ Γ⊢θ where
    Γ⊢θ⊃ψ = snd (⊢-subst-impl Γ⊢ϕ ϕ,Γ⊢θ⊃ψ)
    Γ⊢θ   = snd (⊢-subst-impl Γ⊢ϕ ϕ,Γ⊢θ)

⊢-subst : {a : Level} {A : Type a} {ϕ ψ : Formula A} {m n : ℕ} {Γ : Context A m} {Δ : Context A n}
  → Γ ⊢ ϕ
  → Δ ,, ϕ , Γ ⊢ ψ
    --------------
  → Δ ,, Γ ⊢ ψ
⊢-subst {Γ = Γ} {Δ = Δ} Γ⊢ϕ Δ,ϕ,Γ⊢ψ = _ ∙ snd (⊢-subst-impl Δ,Γ⊢ϕ ϕ,Δ,Γ⊢ψ)  where
  Δ,Γ⊢ϕ   = snd (⊢-struct (⊆-concat-front {Ξ = Δ} ⊆-refl) Γ⊢ϕ)
  ϕ,Δ,Γ⊢ψ = snd (⊢-struct (⊆-swap-middle-to-front {Δ = Γ}) Δ,ϕ,Γ⊢ψ)
  
