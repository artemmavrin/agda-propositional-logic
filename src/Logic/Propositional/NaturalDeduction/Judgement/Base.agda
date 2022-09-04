open import Agda.Primitive using (Level) renaming (Set to Type)

module Logic.Propositional.NaturalDeduction.Judgement.Base {a : Level} (Atom : Type a) where

open import Logic.Propositional.Syntax (Atom)

private
  variable
    A B : Formula
    Γ Δ : Context

infix 4 _⊢_

data _⊢_ : Context → Formula → Type a where
  ax :
      A ∈ Γ
      -----
    → Γ ⊢ A

  ⊃I :
      Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⊃ B

  ⊃E :
      Γ ⊢ A ⊃ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

struct :
    Γ ⊆ Δ
  → Γ ⊢ A
    -----
  → Δ ⊢ A
struct Γ⊆Δ (ax A∈Γ)       = ax (⊆E Γ⊆Δ A∈Γ)
struct Γ⊆Δ (⊃I Γ,A⊢B)     = ⊃I (struct (weakening-is-monotonic Γ⊆Δ) Γ,A⊢B)
struct Γ⊆Δ (⊃E Γ⊢A⊃B Γ⊢A) = ⊃E (struct Γ⊆Δ Γ⊢A⊃B) (struct Γ⊆Δ Γ⊢A)

{-
trans :
    Γ ⊢ A
  → Γ , A ⊢ B
    ---------
  → Γ ⊢ B
trans (ax p) q = struct (⊆S ⊆-refl p) q
trans (⊃I Γ,C⊢D) Γ,C⊃D⊢B = _
trans _ _ = _
-}
