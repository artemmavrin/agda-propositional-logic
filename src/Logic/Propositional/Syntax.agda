open import Agda.Primitive using (Level) renaming (Set to Type)

module Logic.Propositional.Syntax {a : Level} (Atom : Type a) where

open import Logic.Propositional.Syntax.Formula (Atom) public
open import Logic.Propositional.Syntax.Context (Atom) public
