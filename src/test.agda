{-# OPTIONS --cohesion --without-K #-}

-- open import Cubical.Foundations.Prelude hiding (J)
open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding (J)

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




J : {ℓ ℓ' : Level} {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ') → P x refl → {y : A} (p : x ≡ y) → P y p
J P r refl = r

-- non-based variant
J' : {ℓ ℓ' : Level} {A : Type ℓ} (P : (x y : A) → x ≡ y → Type ℓ') → ((x : A) → P x x refl) → {x y : A} (p : x ≡ y) → P x y p
-- J' P r {x = x} refl = r x
J' P r {x = x} p = J (λ y p → P x y p) (r x) p

-- based follows from non-based
J'' : {ℓ ℓ' : Level} {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ') → P x refl → {y : A} (p : x ≡ y) → P y p
J'' {A = A} {x} P r p = J' D R p P r
  where
  D : (x y : A) → x ≡ y → Type _
  D x y p = (P : (y : A) → x ≡ y → Type _) → P x refl → P y p
  R : (x : A) → D x x refl
  R x P r = r


-- another variant
K : {A : Type} → (x : A) (y : A) (P : (x y : A) → x ≡ y → Type) → P x x refl → (p : x ≡ y) → P x y p
K x y P r refl = r

K-to-J' : {A : Type} (P : (x y : A) → x ≡ y → Type) → ((x : A) → P x x refl) → {x y : A} (p : x ≡ y) → P x y p
K-to-J' P r {x} {y} p = K x y P (r x) p
