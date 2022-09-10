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
struct :
    Γ ⊆ Δ
  → Γ ⊢ ϕ [ s ]
    -----------
  → Δ ⊢ ϕ [ s ]
struct p (axiom q)     = axiom (⊆-elim p q)
struct p ⊤-intro       = ⊤-intro
struct p (⊃-intro π)   = ⊃-intro (struct (⊆-extend p) π)
struct p (⊃-elim π ρ)  = ⊃-elim (struct p π) (struct p ρ)
struct p (∧-intro π ρ) = ∧-intro (struct p π) (struct p ρ)
struct p (∧-elimˡ π)   = ∧-elimˡ (struct p π)
struct p (∧-elimʳ π)   = ∧-elimʳ (struct p π)

-- Substitution rule
subst :
    Γ ⊢ ϕ [ s ]
  → ϕ , Γ ⊢ ψ [ t ]
    ---------------
  → Γ ⊢ ψ
subst π (axiom ∈Z)     = [ _ , π ]
subst _ (axiom (∈S p)) = [ _ , axiom p ]
subst _ ⊤-intro        = [ _ , ⊤-intro ]
subst π (⊃-intro ρ)    = [ _ , ⊃-intro (snd (subst (struct (⊆-append ⊆-refl) π) (struct ⊆-swap ρ))) ]
subst π (⊃-elim ρ σ)   = [ _ , ⊃-elim (snd (subst π ρ)) (snd (subst π σ)) ]
subst π (∧-intro ρ σ)  = [ _ , ∧-intro (snd (subst π ρ)) (snd (subst π σ)) ]
subst π (∧-elimˡ ρ)    = [ _ , ∧-elimˡ (snd (subst π ρ)) ]
subst π (∧-elimʳ ρ)    = [ _ , ∧-elimʳ (snd (subst π ρ)) ]
