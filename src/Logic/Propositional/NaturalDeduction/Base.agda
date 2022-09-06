module Logic.Propositional.NaturalDeduction.Base where

open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Data.Nat using (ℕ)
open import Logic.Propositional.Syntax

infix 4 _⊢_ _⊢_[_]

data Shape : Type where
  𝟘 : Shape
  _⊕_ : Shape → Shape → Shape
  𝕤𝕦𝕔 : Shape → Shape

-- Shape-aware derivation trees; we track shape information to ensure termination

data _⊢_[_] {a : Level} {A : Type a} : {n : ℕ} → Context A n → Formula A → Shape → Type a where
  axiom : {ϕ : Formula A} {n : ℕ} {Γ : Context A n}
    → ϕ ∈ Γ
      -----------
    → Γ ⊢ ϕ [ 𝟘 ]

  ⊃-intro : {ϕ ψ : Formula A} {n : ℕ} {Γ : Context A n} {s : Shape}
    → ϕ , Γ ⊢ ψ [ s ]
      -------------------
    → Γ ⊢ ϕ ⊃ ψ [ 𝕤𝕦𝕔 s ]

  ⊃-elim : {ϕ ψ : Formula A} {n : ℕ} {Γ : Context A n} {s t : Shape}
    → Γ ⊢ ϕ ⊃ ψ [ s ]
    → Γ ⊢ ϕ [ t ]
      ---------------
    → Γ ⊢ ψ [ s ⊕ t ]

shape-of : {a : Level} {A : Type a} {n : ℕ} {Γ : Context A n} {ϕ : Formula A} {s : Shape} → Γ ⊢ ϕ [ s ] → Shape
shape-of {s = s} _ = s

_⊢_ : {a : Level} {A : Type a} {n : ℕ} → Context A n → Formula A → Type a
Γ ⊢ ϕ = Σ Shape (Γ ⊢ ϕ [_])
