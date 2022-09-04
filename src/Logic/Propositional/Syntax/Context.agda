open import Agda.Primitive using (Level) renaming (Set to Type)

module Logic.Propositional.Syntax.Context {a : Level} (Atom : Type a) where

open import Logic.Propositional.Syntax.Context.Base (Atom) public
open import Logic.Propositional.Syntax.Context.Properties (Atom) public
