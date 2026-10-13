# The BATT language

BATT checks files written in a dependently typed language whose syntax is close
to Agda's. On top of the usual dependent types (Π, Σ, identity types,
universes), the language provides the _bunched_ connectives of bunched affine
type theory:

- a tensor product `A ⨂ B`, whose elements are pairs `a ⊗ b` of terms that use
  disjoint resources,
- two _lax_ function types `A →ₗ B` and `A →ᵣ B`, adjoint to the tensor on the
  left and on the right,
- a flat modality `♭A`, together with _crisp_ variables, written `x ∷ A`.

The language is affine: a variable can always be discarded (weakening), and
cartesian constructions (`→`, `×`, `Σ`) can use a variable several times. Only
the tensor restricts duplication.

## Running the checker

```sh
dune build
./src/batt.exe -I stdlib file.batt
```

The `-I` option adds a directory to the search path for `import`. A file is
checked declaration by declaration, and the checker reports any metavariable
that is still unsolved at the end.

## Lexical conventions

- Line comments start with `--`.
- Identifiers start with a letter (Latin or Greek, except `λ`) and may
  contain letters, digits, `'`, `-`, `_`, `→`, `⁻`, `ₗ`, `ᵣ`, `≡`, `≃` and
  `𝕀`. So `tens-to-prod`, `flat-tens≃prod`, `arr-to-arrₗ` and `f'` are all
  single identifiers: put spaces around operators like `-`.
- A line starting with a space continues the previous line. A declaration
  spanning several lines must therefore indent its continuation lines.

Most symbols have an ASCII or LaTeX-like alternative:

| Symbol | Alternatives | Meaning |
|--------|--------------|---------|
| `→` | `->`, `\to` | function type |
| `→ₗ` | `⇀`, `->l`, `\tol` | left lax function type |
| `→ᵣ` | `⇁`, `->r`, `\tor` | right lax function type |
| `λ` | `fun` | abstraction |
| `∷` | `::` | crisp typing |
| `Σ` | `\Sigma` | dependent sum |
| `×` | `\times` | cartesian product |
| `⨂` | `\bigotimes` | tensor product (type) |
| `⊗` | `\otimes` | tensor pair (term) |
| `♭` | `\flat` | flat modality (type) |
| `𝄫` | `\fflat` | flat introduction (term and pattern) |
| `≡` | `\equiv` | identity type |
| `⊥` | `\bot` | empty type |
| `⊤` | `\top` | unit type |
| `ℕ` | `Nat` | natural numbers |
| `𝕀`, `𝕀0`, `𝕀1`, `𝕀∨`, `𝕀∧` | `II`, `II0`, `II1`, `IIv`, `IIw` | interval |

A few infix symbols are notations for ordinary identifiers, which must be
defined (usually by the standard library) before they are used:

| Notation | Stands for | Fixity |
|----------|------------|--------|
| `A ≃ B` | `_≃_ A B` | non-associative |
| `x ≤ y`, `x ≥ y` | `leq x y`, `geq x y` | non-associative |
| `g ∘ f` | `circ g f` | left-associative |
| `x ∨ y` | `or x y` | left-associative |
| `¬ A` | `not A` | prefix |

## Declarations

A file is a sequence of declarations.

### Definitions

A definition is a type signature followed by one or more clauses:

```
id : {A : U} → A → A
id x = x
```

The signature uses `:` for a _normal_ definition or `∷` for a _crisp_ one.
Only crisp definitions can be used in crisp positions (under `♭`, `𝄫`, or as a
crisp argument, see [Crisp variables](#crisp-variables-and-the-flat-modality)).
Most of the standard library is declared crisp.

The arguments on the left of `=` are patterns (see
[Pattern matching](#pattern-matching)). The same name can be redefined: the
new definition hides the previous one.

### Postulates

```
postulate A ∷ U
```

A postulate is an opaque constant: it has a type but no definition and does not
compute.

### Abstract definitions

```
abstract double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ rec)
```

The body of an abstract definition is type-checked but never unfolded:
afterwards, `double` behaves like a postulate. This is mostly used for proofs,
whose computational content is irrelevant and which would otherwise slow down
conversion checking.

### Imports and modules

```
open import Stdlib
```

`open import Foo` checks the file `Foo.batt` (looked up in the current
directory and in the `-I` directories) and brings its definitions into scope.

Without `open`, `import Foo` binds the module as a record named `Foo`, whose
definitions are accessed with a dot. A module can be opened later:

```
import Bool

f : bool → bool
f = Bool.bool-not

open Bool

g : bool → bool
g = bool-not
```

A file is checked only once, even if imported several times, and cyclic imports
are rejected.

## Terms

### Universes

`Type` (or `U`) is the universe of small types. `Type n` is the universe of
level `n`, `Type` being `Type 0`, and `Type n : Type (n+1)`. Universes are
cumulative. The builtin `TYPE` is a name for `Type 1`.

### Functions

Dependent function types are written with binder groups, as in Agda:

```
(x : A) → B x
(x y : A) (z : C) → D x y z
{A B : Type} → A → B
```

A non-dependent function type is `A → B`. A binder can be crisp, `(x ∷ A)` or
`{A ∷ U}`. Arrows associate to the right.

Abstractions are written `λ x y . t` or `fun x y → t` (`.` and `→` are
interchangeable). The binders of an abstraction can be patterns, e.g.
`λ (a , b) . a`, `fun 𝄫x → x`, `fun refl → refl`.

Application is juxtaposition, `f x y`, and implicit arguments are passed
explicitly between braces, `f {A} x`.

### Implicit arguments

Arguments declared with braces `{x : A}` are implicit: they are inserted
automatically and inferred by unification. They can be bound explicitly in
clauses or abstractions with `{x}`:

```
id : {A : U} → A → A
id {A} x = x

b : bool
b = id false

f : bool → bool
f = comp not (id {bool})
```

### Dependent sums

`Σ (x : A) . B x` is the dependent sum and `A × B` the non-dependent one. Pairs
are written `t , u` (the comma binds weaker than any other construction, so
parentheses are often unnecessary) and are eliminated by matching on a pattern
`(x , y)`.

```
swap : {A B : U} → A × B → B × A
swap (a , b) = (b , a)
```

### Local definitions

```
let x : A = t in u
let x ∷ A = t in u
```

The second form introduces a crisp local definition, which requires `t` to be
crisp. Local definitions are frequently used to perform a pattern match on an
intermediate value:

```
flat-split ∷ {A B ∷ U} → ♭(A × B) → ♭A × ♭B
flat-split {A} {B} 𝄫x =
  let h : (x ∷ A × B) → ♭A × ♭B = fun (a , b) → (𝄫a , 𝄫b) in
  h x
```

### Holes and metavariables

- `_` is a metavariable, which has to be solved by unification.
- `?` is a hole: the checker displays its expected type and the context, which
  is useful to develop a proof interactively.

```
id' : (A : U) → A → A
id' A x = id _ x
```

## Base types

The following types are built in.

| Type | Constructors | Patterns |
|------|--------------|----------|
| `⊥` (`empty`) | none | `()` |
| `⊤` (`unit`) | `tt` | `tt` |
| `bool` | `false`, `true` | `false`, `true` |
| `ℕ` | `zero` (or `0`), `succ`, numerals `1`, `2`, … | `zero`, `0`, `(succ n)` |
| `List A` | `nil`, `cons` | `nil`, `(cons x l)` |

`succ : ℕ → ℕ` and `cons : {A : Type} → A → List A → List A` are ordinary
functions, so they can be partially applied (`cong succ p`, `map (cons x) l`).
`List` is a keyword and must always be applied to a type.

### Recursion on ℕ and List

Functions out of `ℕ` and `List A` are defined by clauses, but the function's own
name is not in scope in its body: recursion is _structural_ only, through the
reserved variable `rec`. In the clause for `(succ n)` (resp. `(cons x l)`),
`rec` is the result of the recursive call on `n` (resp. `l`), abstracted over the
arguments that come after the matched one:

```
-- matching on the first argument: rec is a function of the second one
add ∷ ℕ → ℕ → ℕ
add zero n = n
add (succ m) n = succ (rec n)

-- matching on the last argument: rec is just the value of the recursive call
add' ∷ ℕ → ℕ → ℕ
add' m zero = m
add' m (succ n) = succ rec

append ∷ {A : Type} → List A → List A → List A
append nil m = m
append (cons x l) m = cons x (rec m)
```

The same applies to proofs by induction:

```
append-nil ∷ {A : Type} → (l : List A) → append l nil ≡ l
append-nil nil = refl
append-nil (cons x l) = cong (cons x) rec
```

### Empty type

A clause whose last pattern is `()` eliminates an argument of type `⊥`; it has
no right-hand side:

```
crispify-empty ∷ ⊥ → ♭⊥
crispify-empty ()
```

## Identity types

`t ≡ u` is the type of identifications between `t` and `u`; the type can be
given explicitly as `t ≡{A} u`. Its constructor is `refl : t ≡ t`, and it is
eliminated by matching on `refl` (based path induction), from which the usual
operations are derived in `stdlib/Equality.batt`:

```
J ∷ {A : Type} (x : A) (P : (y : A) → x ≡ y → Type) → P x refl → {y : A} (p : x ≡ y) → P y p
J x P r refl = r

sym ∷ {A : Type} {x y : A} → x ≡ y → y ≡ x
sym {A} {x} refl = refl

cong ∷ {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f {x} refl = refl
```

Definitional equality includes β-rules and the η-rule for functions, so that
for instance `f ≡ λ x . f x` holds by `refl` (there is no definitional η-rule
for pairs).

## Bunched structure

### Contexts

A typing context has two parts:

- the _crisp_ context, made of variables declared with `∷`, which can be used
  anywhere, any number of times;
- the _bunched_ context, made of normal variables declared with `:`, organized
  as a tree whose nodes are either cartesian (`,`) or tensor (`⊗`).

The usual binders (`(x : A) → B`, `λ`, `Σ`, `let`) extend the bunched context
cartesianly. Within a cartesian bunch, variables can be duplicated and
discarded freely, as in ordinary type theory. Variables separated by a tensor
node are used _separately_ when building a tensor pair.

### Tensor products

`A ⨂ B` is the tensor product. Its elements are built with `a ⊗ b`, which is
only accepted when the context can be split as a tensor of two parts, the left
part providing the variables of `a` and the right one those of `b`. Crisp
variables are shared by both sides. Tensors are eliminated by matching on
`(a ⊗ b)`, which places `a` and `b` in the context separated by a tensor node.

```
-- a tensor can be turned into a product…
tens-to-prod ∷ {A B ∷ U} → A ⨂ B → A × B
tens-to-prod (a ⊗ b) = (a , b)

-- …but a variable cannot be used on both sides of a tensor
diag-tens ∷ (A ∷ U) → A → A ⨂ A
diag-tens A a = (a ⊗ a)              -- rejected

-- unless it is crisp
crisp-diag ∷ (A ∷ U) (a ∷ A) → A ⨂ A
crisp-diag A a = a ⊗ a
```

The tensor is associative and unital (with unit `⊤`) up to equivalence, but it
is _not_ symmetric: `swap (x ⊗ y) = y ⊗ x` is rejected, the order of the bunch
being recorded. Not every element of a tensor is a pure tensor either:
`x ≡ tens-fst x ⊗ tens-snd x` cannot be proved.

### Lax function types

The tensor has two right adjoints, the lax function types:

- `A →ᵣ B`: the argument is added to the _right_ of the context, so that
  `(A ⨂ B →ᵣ C) ≃ (A →ᵣ B →ᵣ C)`;
- `A →ₗ B`: the argument is added to the _left_ of the context, so that
  `(A ⨂ B →ₗ C) ≃ (B →ₗ A →ₗ C)`.

They are introduced by `λ` and eliminated by application, like ordinary
functions. When applying `f a` with `f : A →ᵣ B`, the context must split as a
tensor with `f` on the left and `a` on the right (symmetrically for `→ₗ`).

```
tens-curry-right ∷ {A B C ∷ U} → (A ⨂ B →ᵣ C) → (A →ᵣ B →ᵣ C)
tens-curry-right f a b = f (a ⊗ b)

tens-uncurry-right ∷ {A B C ∷ U} → (A →ᵣ B →ᵣ C) → (A ⨂ B →ᵣ C)
tens-uncurry-right f (a ⊗ b) = f a b
```

Since the language is affine, every ordinary function is in particular a lax
one, and lax arrows do not prevent duplication of their arguments in a
cartesian context:

```
arr-to-arrᵣ ∷ {A B ∷ U} → (A → B) → (A →ᵣ B)
arr-to-arrᵣ f a = f a

duplicate ∷ {A B ∷ U} → A →ₗ ((A → A → B) → B)
duplicate a f = f a a
```

Lax function types are non-dependent.

### Crisp variables and the flat modality

A variable is declared crisp with `∷`: `(x ∷ A) → B`, `{A ∷ U}`, `let x ∷ A = …`,
or a top-level `f ∷ A`. A term is _crisp_ when it only uses crisp variables;
crisp arguments and crisp `let`s must be given crisp terms.

The flat modality `♭A` is the type of crisp elements of `A`:

- `♭A` is only well-formed when `A` is crisp,
- `𝄫t : ♭A` when `t : A` is crisp,
- matching on the pattern `𝄫x` binds `x` as a crisp variable.

```
unflatten ∷ {A ∷ U} → ♭A → A
unflatten 𝄫x = x

flat-map ∷ {A B ∷ Type} (f ∷ A → B) → ♭A → ♭B
flat-map f 𝄫a = 𝄫(f a)

-- does not type-check: a is not crisp
-- flatten ∷ (A ∷ U) → A → ♭A
-- flatten A a = 𝄫a
```

The file `stdlib/Flat.batt` formalizes a part of Shulman's _Brouwer's
fixed-point theorem in real-cohesive homotopy type theory_ (discrete types,
`♭` commutes with `Σ`, `×` and identity types, etc.) as well as the interaction
of `♭` with the tensor: `♭(A ⨂ B) ≃ ♭(A × B)` and `♭A ⨂ B ≃ ♭A × B`.

## The interval

`𝕀` is an interval type with two endpoints `𝕀0` and `𝕀1` and two binary
operations `𝕀∨` and `𝕀∧`. Definitional equality makes `𝕀` a _distributive
lattice_: all the lattice laws hold by `refl` (it is not a boolean algebra, and
`𝕀0 ≡ 𝕀1` is not provable).

```
sup-inf ∷ (i j : 𝕀) → i 𝕀∨ (i 𝕀∧ j) ≡ i
sup-inf i j = refl
```

There is no eliminator out of `𝕀`. It is used to define directed paths,
possibly lax ones (`stdlib/Arrow.batt`):

```
arr ∷ U → U
arr A = 𝕀 → A

arrₗ ∷ (A ∷ U) → U
arrₗ A = 𝕀 →ₗ A
```

## Pattern matching

A definition can consist of several clauses, one per case. The available
patterns are:

| Pattern | Matches |
|---------|---------|
| `x`, `_` | anything |
| `{x}` | an implicit argument |
| `tt` | `⊤` |
| `false`, `true` | `bool` |
| `zero`, `0`, `(succ n)` | `ℕ` |
| `nil`, `(cons x l)` | `List A` |
| `(x , y)` | `Σ`, `×` |
| `(x ⊗ y)` | `⨂` |
| `𝄫x` | `♭` |
| `refl` | `≡` |
| `()` | `⊥` (last argument only, no right-hand side) |

Patterns are not nested: the components of `(x , y)`, `(x ⊗ y)`, `𝄫x`,
`(succ n)` and `(cons x l)` must be variables (use a `let` or an auxiliary
function to match further). Clauses must cover all cases, and a variable at a
given position must have the same name in all the clauses that bind it:

```
xor : bool → bool → bool
xor false x = x
xor true  x = bool-not x
```

## Precedence

From loosest to tightest:

1. `t , u` (pairs, right-associative)
2. `λ`, `let`, `Σ`, dependent function types, `→`, `→ₗ`, `→ᵣ` (arrows are
   right-associative)
3. `≃`, `≤`, `≥` (non-associative)
4. `≡` (non-associative)
5. `×` (right-associative)
6. `⊗` (right-associative)
7. `⨂` (right-associative)
8. `∘`, `∨` (left-associative)
9. `𝕀∨`, `𝕀∧` (left-associative)
10. application, `List A`
11. `♭`, `𝄫` (prefix)
12. `t.x` (record field / module access)

For instance `♭A × B` is `(♭A) × B`, and `𝄫f a` is `𝄫(f) a`: write `𝄫(f a)`.

## Standard library

The `stdlib` directory contains, among others:

| File | Contents |
|------|----------|
| `Stdlib.batt` | imports everything below |
| `Equality.batt` | `J`, `sym`, `trans`, `cong`, `subst`, `transport`, … |
| `Bool.batt`, `Nat.batt`, `List.batt` | operations and properties of base types |
| `Sum.batt`, `Product.batt`, `Unit.batt`, `Empty.batt` | type formers |
| `Contr.batt`, `Prop.batt`, `Set.batt`, `Trunc.batt` | homotopy levels |
| `Equivalence.batt`, `Funext.batt`, `Univalence.batt` | equivalences, `_≃_` |
| `Pullback.batt`, `Pushout.batt`, `Cocone.batt` | (co)limits |
| `Tensor.batt` | properties of `⨂`, currying for lax arrows |
| `Flat.batt` | properties of `♭`, discrete types |
| `Interval.batt`, `Arrow.batt`, `Cube.batt`, `Path.batt` | the interval and directed paths |
