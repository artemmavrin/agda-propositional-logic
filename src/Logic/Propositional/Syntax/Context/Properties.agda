open import Agda.Primitive using (Level) renaming (Set to Type)

module Logic.Propositional.Syntax.Context.Properties {a : Level} (Atom : Type a) where

open import Logic.Propositional.Syntax.Context.Base (Atom)
open import Logic.Propositional.Syntax.Formula (Atom)

private
  variable
    A B : Formula
    Γ Δ : Context

{-
∈-lemma : A ∈ Γ , A ,, Δ
∈-lemma {Δ = ∅}     = ∈Z
∈-lemma {Δ = Δ , _} = ∈S ∈-lemma {Δ = Δ}
-}

⊆-step : Γ ⊆ Δ → Γ ⊆ Δ , A
⊆-step ⊆Z              = ⊆Z
⊆-step (⊆S ⊆Z r)       = ⊆S ⊆Z (∈S r)
⊆-step (⊆S (⊆S p q) r) = ⊆S (⊆S (⊆-step p) (∈S q)) (∈S r)

weakening-is-monotonic : Γ ⊆ Δ → Γ , A ⊆ Δ , A
weakening-is-monotonic ⊆Z       = ⊆S ⊆Z ∈Z
weakening-is-monotonic (⊆S p q) = ⊆S (⊆S (⊆-step p) (∈S q)) ∈Z

⊆I : ({A : Formula} → A ∈ Γ → A ∈ Δ) → Γ ⊆ Δ
⊆I {Γ = ∅}     _ = ⊆Z
⊆I {Γ = _ , _} p = ⊆S (⊆I (λ x -> p (∈S x))) (p ∈Z)

⊆E : Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
⊆E (⊆S _ q) ∈Z     = q
⊆E (⊆S p _) (∈S r) = ⊆E p r

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = ∅}     = ⊆Z
⊆-refl {Γ = _ , _} = weakening-is-monotonic ⊆-refl
