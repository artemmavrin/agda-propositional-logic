module Data.Fin where

open import Agda.Primitive using () renaming (Set to Type)
open import Data.Nat

private
  variable
    n : ℕ

data Fin : ℕ → Type where
  zero : Fin (suc n)
  suc  : (i : Fin n) → Fin (suc n)
