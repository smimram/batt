# Bug: η-rule for Σ/⊗ eliminators loops on stuck eliminators (unbounded memory)

Reproduction: [`eta-stuck-eliminator.batt`](eta-stuck-eliminator.batt), in this directory.
Found on 2026-09-25, repository at `5f9200c`.

> ⚠ **Do not run the reproduction uncapped.** It allocates without bound, goes past 2 GB in a
> few seconds and froze a 16 GB machine. Run it like this instead:
>
> ```sh
> ( ulimit -v 1000000; timeout -s KILL 10 _build/install/default/bin/batt test/todo/eta-stuck-eliminator.batt )
> ```
>
> `test/todo/` is not globbed by any `dune` rule, so `dune runtest` does not run it.

## Symptom

```
f ∷ {A ∷ U} → A ⨂ ⊤ → A
f (a ⊗ x) = a

t ∷ {A ∷ U} (u : A ⨂ ⊤) (a : A) → f u ≡ a
t u a = refl
```

- **Expected:** a type error, since `f u` is stuck on the variable `u` and is not `a`.
- **Actual:** the checker never returns and its memory grows until it hits the limit:
  ```
  Fatal error: allocation failure during minor GC
  ```

The last line that `--debug` prints before the blowup is

```
UNIFY ((λ(x3⊗x4).x-3) x-1) WITH x-2
```

## Scope (all runs capped at 1 GB and 10 s)

| variant | result |
|---|---|
| ⊗-eliminator stuck on a variable, compared with a variable (the file above) | loops, out of memory |
| same with Σ: `f (a , x) = a` on `A × ⊤` | loops, out of memory |
| ⊗-eliminator stuck on a **hole**: `g a = ?` then `t a = refl : f (g a) ≡ a` | loops, out of memory |
| eliminator not stuck: `f (a ⊗ tt) ≡ a` by `refl` | fine |
| plain mismatch `b ≡ a` by `refl` | fails as it should (but see the aside at the end) |

In practice it shows up when **replacing a definition's body by a hole**, whenever a later `refl`
unfolds that definition. That's how it was found: `stdlib/Tensor.batt` line 40,
`tens-counit-right a = ?`, followed by `tens-unit-counit-right a = refl` on line 43. It also
froze VS Code, whose extension re-runs the checker on every edit. (The extension now runs the
checker under memory, time and output limits and kills the whole process group.)

## Cause

A `Tens_ind (t, l)` value is the eliminator `λ(x⊗y). t` applied to the spine `l`
(`src/value.ml:171–172`):

```ocaml
| Tens_ind (t, []), TensPair (u, v) -> capp2 t u v   (* computes *)
| Tens_ind (t, l), u -> Tens_ind (t, u::l)           (* stuck: argument pushed onto the spine *)
```

(`Pair_ind` at lines 169–170 works the same way.) So a `Tens_ind` with a **non-empty** spine is a
stuck elimination: a neutral term, not a function.

The unifier's η-rule (`src/lang.ml:426–438`) matches **every** `Tens_ind` and `Pair_ind`, whatever
its spine:

```ocaml
(* eta-expansion (needs to be after meta-variables, …) *)
| (Pair_ind _ as t), u
| t, (Pair_ind _ as u) ->
  let x = V.var k in
  let y = V.var (k+1) in
  let p = V.Pair (x,y) in
  unify (k+2) (V.app t p) (V.app u p)
| (Tens_ind _ as t), u
| t, (Tens_ind _ as u) ->
  … V.TensPair (x,y) …
  unify (k+2) (V.app t p) (V.app u p)
```

On a stuck eliminator, `V.app t p` only pushes the fresh pair onto the spine, so the result is
still a stuck `Tens_ind`. The other side becomes `Var (x, [p])`. The same clause fires again,
and so on:

```
unify  (λ(x⊗y).x) u                       with  a
unify  (λ(x⊗y).x) u (x₀⊗y₀)               with  a (x₀⊗y₀)
unify  (λ(x⊗y).x) u (x₀⊗y₀) (x₂⊗y₂)       with  a (x₀⊗y₀) (x₂⊗y₂)
…
```

- **It never reaches the `CLASH` case.** The recursive call is a tail call, so the stack doesn't
  overflow either.
- **It allocates on every round:** the spines grow, and fresh variables are created each time.
- **It's never ill-typed along the way** (`V.app` accepts anything on a stuck eliminator), so
  nothing stops it.

## Suggested fix (not applied, not tested)

η-expansion is only sound, and only terminates, for an **unapplied** eliminator (empty spine),
which really is a function out of Σ / ⊗. Restricting both clauses to empty spines should be
enough:

```ocaml
| (Pair_ind (_, []) as t), u
| t, (Pair_ind (_, []) as u) -> …   (* unchanged body *)
| (Tens_ind (_, []) as t), u
| t, (Tens_ind (_, []) as u) -> …   (* unchanged body *)
```

A stuck eliminator then falls through to `CLASH` and raises `Unification`, which is the right
answer for the reproduction. Two stuck eliminators are still compared structurally by the existing
`Pair_ind`/`Tens_ind` vs `Pair_ind`/`Tens_ind` clause (`src/lang.ml:390–393`).

Things worth double-checking:

- whether some existing development relied on η firing on a stuck eliminator against a meta.
  Metas are handled by the earlier clauses, so probably not;
- that `dune runtest` still passes.

I haven't touched the OCaml sources, so none of this has been run.

## Aside: failing `refl` gives an uncaught exception

The control case

```
t ∷ {A ∷ U} (b a : A) → b ≡ a
t b a = refl
```

fails correctly, but as `Fatal error: exception Lang.Unification` (exit 2), with no position and no
`Error:` message. It looks like `Unification` escapes from the `refl` check without being turned
into a located type error. It's minor and separate from the loop, but with the fix above the
reproduction would end the same way.
