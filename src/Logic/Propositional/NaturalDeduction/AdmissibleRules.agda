module Logic.Propositional.NaturalDeduction.AdmissibleRules where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ) public
open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to [_,_])
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Logic.Propositional.NaturalDeduction.Base
open import Logic.Propositional.Syntax

private
  variable
    a : Level
    A : Type a
    m n : ℕ
    ϕ ψ : Formula A
    Γ : Context A m
    Δ : Context A n
    s t : Shape

-- Structural rule, including weakening, contraction, and exchange
struct : Γ ⊆ Δ → Γ ⊢ ϕ [ s ] → Δ ⊢ ϕ [ s ]
struct Γ⊆Δ Γ⊢ϕ@(axiom ϕ∈Γ)         = axiom (⊆-elim Γ⊆Δ ϕ∈Γ)
struct Γ⊆Δ Γ⊢⊤@(⊤-intro Γ⊢ψ)       = ⊤-intro (struct Γ⊆Δ Γ⊢ψ)
struct Γ⊆Δ Γ⊢ϕ⊃ψ@(⊃-intro ϕ,Γ⊢ψ)   = ⊃-intro (struct (⊆-extend Γ⊆Δ) ϕ,Γ⊢ψ)
struct Γ⊆Δ Γ⊢ϕ@(⊃-elim Γ⊢ψ⊃ϕ Γ⊢ψ)  = ⊃-elim (struct Γ⊆Δ Γ⊢ψ⊃ϕ) (struct Γ⊆Δ Γ⊢ψ)
struct Γ⊆Δ Γ⊢ϕ∧ϕ@(∧-intro Γ⊢ϕ Γ⊢ψ) = ∧-intro (struct Γ⊆Δ Γ⊢ϕ) (struct Γ⊆Δ Γ⊢ψ)
struct Γ⊆Δ Γ⊢ϕ@(∧-elimˡ Γ⊢ϕ∧ψ)     = ∧-elimˡ (struct Γ⊆Δ Γ⊢ϕ∧ψ)
struct Γ⊆Δ Γ⊢ψ@(∧-elimʳ Γ⊢ϕ∧ψ)     = ∧-elimʳ (struct Γ⊆Δ Γ⊢ϕ∧ψ)

-- Cut rule
cut : Γ ⊢ ϕ [ s ] → ϕ , Γ ⊢ ψ [ t ] → Γ ⊢ ψ
cut Γ⊢ϕ ϕ,Γ⊢ψ@(axiom ∈Z)              = [ _ , Γ⊢ϕ ]
cut Γ⊢ϕ ϕ,Γ⊢ψ@(axiom (∈S ψ∈Γ))        = [ _ , axiom ψ∈Γ ]
cut Γ⊢ϕ ϕ,Γ⊢⊤@(⊤-intro ϕ,Γ⊢θ)         = [ _ , ⊤-intro (snd (cut Γ⊢ϕ ϕ,Γ⊢θ)) ]
cut Γ⊢ϕ ϕ,Γ⊢α⊃β@(⊃-intro α,ϕ,Γ⊢β)     = [ _ , ⊃-intro α,Γ⊢β ] where
  α,Γ⊢ϕ   = struct (⊆-append ⊆-refl) Γ⊢ϕ
  ϕ,α,Γ⊢β = struct (⊆S (⊆S (⊆-append (⊆-append ⊆-refl)) ∈Z) (∈S ∈Z)) α,ϕ,Γ⊢β
  α,Γ⊢β   = snd (cut α,Γ⊢ϕ ϕ,α,Γ⊢β)
cut Γ⊢ϕ ϕ,Γ⊢ψ@(⊃-elim ϕ,Γ⊢θ⊃ψ ϕ,Γ⊢θ)  = [ _ , ⊃-elim (snd (cut Γ⊢ϕ ϕ,Γ⊢θ⊃ψ)) (snd (cut Γ⊢ϕ ϕ,Γ⊢θ)) ]
cut Γ⊢ϕ ϕ,Γ⊢α∧β@(∧-intro ϕ,Γ⊢α ϕ,Γ⊢β) = [ _ , ∧-intro (snd (cut Γ⊢ϕ ϕ,Γ⊢α)) (snd (cut Γ⊢ϕ ϕ,Γ⊢β)) ]
cut Γ⊢ϕ ϕ,Γ⊢α@(∧-elimˡ ϕ,Γ⊢α∧β)       = [ _ , ∧-elimˡ (snd (cut Γ⊢ϕ ϕ,Γ⊢α∧β)) ]
cut Γ⊢ϕ ϕ,Γ⊢β@(∧-elimʳ ϕ,Γ⊢α∧β)       = [ _ , ∧-elimʳ (snd (cut Γ⊢ϕ ϕ,Γ⊢α∧β)) ]
