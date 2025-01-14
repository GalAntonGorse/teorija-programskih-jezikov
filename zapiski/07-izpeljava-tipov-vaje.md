---
jupytext:
  text_representation:
    extension: .md
    format_name: myst
    format_version: 0.12
    jupytext_version: 1.8.0
kernelspec:
  display_name: OCaml 4.11
  language: OCaml
  name: ocaml-jupyter
---

# Vaje

```{code-cell}
:tags: [remove-cell, remove-stdout]

(* Ko se v Jupytru prvič požene OCaml, program Findlib izpiše neko sporočilo.
   Da se to sporočilo ne bi videlo v zapiskih, je tu ta celica, ki sproži izpis,
   vendar ima nastavljeno, da je v zapiskih v celoti skrita. *)
```

## Naloga 1

Izpeljite in rešite enačbe za izpeljavo tipov naslednjih programov:

1. `|- (fun x -> x * x) 14`
2. `f : α, v : bool |- if f v then 1 else 0`
3. `g : bool -> α |- (fun f -> f (g true)) (fun x -> x + 2)`

Preverite, ali vrstni red enačb vpliva na rezultat. Ugotovite kje se pojavi problem pri določanju tipa funkcije `fun f -> f f`.

## Naloga 2

Algoritem za izpeljavo tipov dopolnite za:

1. rekurzijo
2. pare
3. vsote
4. sezname

## Naloga 3

Izpeljite tip funkcije `map`. Napišite še kakšen program, ki uporablja konstrukte iz naloge 2 in mu določite tip.
