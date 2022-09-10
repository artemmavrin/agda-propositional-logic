module Logic.Propositional.NaturalDeduction.Base where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ) public
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Logic.Propositional.Syntax

infix 4 _⊢_ _⊢_[_]

data Shape : Type where
  * : Shape
  suc : Shape → Shape
  _⊕_ : Shape → Shape → Shape

private
  variable
    a : Level
    A : Type a
    n : ℕ
    ϕ ψ : Formula A
    Γ : Context A n
    s t : Shape

data _⊢_[_] {a : Level} {A : Type a} : {n : ℕ} → Context A n → Formula A → Shape → Type a where
  axiom :
      ϕ ∈ Γ
      -----------
    → Γ ⊢ ϕ [ * ]

  ⊤-intro :
      -----------
      Γ ⊢ ⊤ [ * ]

  ⊃-intro :
      ϕ , Γ ⊢ ψ [ s ]
      -------------------
    → Γ ⊢ ϕ ⊃ ψ [ suc s ]

  ⊃-elim :
      Γ ⊢ ϕ ⊃ ψ [ s ]
    → Γ ⊢ ϕ [ t ]
      ---------------
    → Γ ⊢ ψ [ s ⊕ t ]

  ∧-intro :
      Γ ⊢ ϕ [ s ]
    → Γ ⊢ ψ [ t ]
      -------------------
    → Γ ⊢ ϕ ∧ ψ [ s ⊕ t ]

  ∧-elimˡ :
      Γ ⊢ ϕ ∧ ψ [ s ]
      ---------------
    → Γ ⊢ ϕ [ suc s ]

  ∧-elimʳ :
      Γ ⊢ ϕ ∧ ψ [ s ]
      ---------------
    → Γ ⊢ ψ [ suc s ]

_⊢_ : {a : Level} {A : Type a} {n : ℕ} → Context A n → Formula A → Type a
Γ ⊢ ϕ = Σ Shape (Γ ⊢ ϕ [_])
