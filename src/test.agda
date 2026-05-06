{-# OPTIONS --cubical --guardedness --cohesion #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

data ♭ {@♭ l : Level} (@♭ A : Type l) : Type l where
  𝄫 : (@♭ x : A) → ♭ A

counit : {@♭ l : Level} {@♭ A : Type l} → ♭ A → A
counit (𝄫 x) = x

-- ind : (P : ♭ A → Type) → 

-- next : (@♭ n : ℕ) → ℕ
-- next n = ?

-- x : ℕ
-- x = next 5

-- next : (n : ♭ ℕ) → ℕ
-- next n = ?

-- x : ℕ
-- x = next 5

flat-eta : (@♭ A : Type) (C : ♭ A → Type) (f : (x : ♭ A) → C x) (x : ♭ A) → C x
flat-eta A C f (𝄫 x) = f (𝄫 x)
