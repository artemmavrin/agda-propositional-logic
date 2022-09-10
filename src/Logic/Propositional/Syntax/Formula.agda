module Logic.Propositional.Syntax.Formula where

open import Agda.Primitive using (Level) renaming (Set to Type)

infixr 7 _⊃_
infixl 9 _∧_

data Formula {a : Level} (A : Type a) : Type a where
  ⌈_⌉ : A → Formula A
  ⊤   : Formula A
  _⊃_ : Formula A → Formula A → Formula A
  _∧_ : Formula A → Formula A → Formula A
