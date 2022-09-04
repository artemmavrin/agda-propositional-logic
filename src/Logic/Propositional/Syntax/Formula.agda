open import Agda.Primitive using (Level) renaming (Set to Type)

module Logic.Propositional.Syntax.Formula {a : Level} (Atom : Type a) where

infixr 7 _⊃_

data Formula : Type a where
  ⌈_⌉ : Atom → Formula
  _⊃_ : Formula → Formula → Formula
