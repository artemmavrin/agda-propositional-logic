module Logic.Propositional.NaturalDeduction.Examples where

open import Agda.Builtin.Sigma using () renaming (_,_ to _∙_)
open import Agda.Primitive using (Level) renaming (Set to Type)

open import Logic.Propositional.Syntax
open import Logic.Propositional.NaturalDeduction.Base

private
  variable
    a : Level
    A : Type a
    ϕ ψ θ α β : Formula A

  _ : * ⊢ ϕ ⊃ ϕ
  _ = _ ∙ ⊃-intro (axiom ∈Z)

  _ : ϕ ⊃ ψ , ϕ , * ⊢ ψ
  _ = _ ∙ ⊃-elim (axiom ∈Z) (axiom (∈S ∈Z))

  _ : ϕ , ϕ ⊃ ψ , * ⊢ ψ
  _ = _ ∙ ⊃-elim (axiom (∈S ∈Z)) (axiom ∈Z)

  _ : ψ ⊃ θ , ϕ ⊃ ψ , * ⊢ ϕ ⊃ θ
  _ = _ ∙ ⊃-intro (⊃-elim (axiom (∈S ∈Z)) (⊃-elim (axiom (∈S ∈S ∈Z)) (axiom ∈Z)))

  _ : ϕ , ψ , * ⊢ ϕ ∧ ψ
  _ = _ ∙ ∧-intro (axiom ∈Z) (axiom (∈S ∈Z))

  _ : ϕ ∧ ψ , * ⊢ ψ ∧ ϕ
  _ = _ ∙ ∧-intro (∧-elimʳ (axiom ∈Z)) (∧-elimˡ (axiom ∈Z))

  _ : ϕ ∧ ψ , ϕ ⊃ α , ψ ⊃ β , * ⊢ α ∧ β
  _ = _ ∙ ∧-intro (⊃-elim (axiom (∈S ∈Z)) (∧-elimˡ (axiom ∈Z))) (⊃-elim (axiom (∈S ∈S ∈Z)) (∧-elimʳ (axiom ∈Z)))

  _ : ϕ , * ⊢ ϕ ∧ ϕ
  _ = _ ∙ ∧-intro (axiom ∈Z) (axiom ∈Z)
