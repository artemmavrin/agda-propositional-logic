module Logic.Propositional.NaturalDeduction.Judgement.Examples where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ)

open import Logic.Propositional.Syntax (ℕ)
open import Logic.Propositional.NaturalDeduction.Judgement.Base (ℕ)

private
  variable
    A B C : Formula

  _ : ∅ ⊢ A ⊃ A
  _ = ⊃I (ax ∈Z)

  _ : ∅ , A , A ⊃ B ⊢ B
  _ = ⊃E (ax ∈Z) (ax (∈S ∈Z))

  _ : ∅ , A ⊃ B , A ⊢ B
  _ = ⊃E (ax (∈S ∈Z)) (ax ∈Z)

  _ : ∅ , A ⊃ B , B ⊃ C ⊢ A ⊃ C
  _ = ⊃I (⊃E (ax (∈S ∈Z)) (⊃E (ax (∈S ∈S ∈Z)) (ax ∈Z)))
