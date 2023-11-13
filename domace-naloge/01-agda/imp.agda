module imp where


-- Logične vrednosti

data Bool : Set where
    true : Bool
    false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

¬ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ true = false
false ∧ false = false

_∨_ : Bool → Bool → Bool
true ∨ true = true
true ∨ false = true
false ∨ true = true
false ∨ false = false

-- Naravna števila

data Nat : Set where
    zero : Nat
    suc : Nat → Nat 

-- Namesto suc (suc zero) lahko napišemo kar 2
{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = suc (plus m n)

times : Nat → Nat → Nat
times zero n = zero
times (suc m) n = plus (times m n) n

_==_ : Nat → Nat → Bool
zero == zero = true
(suc n) ==  (suc m) = (n == m)
_ == _ = false

_lessthan_ : Nat → Nat → Bool
zero lessthan (suc n) = true
(suc n) lessthan (suc m) = n lessthan m
_ lessthan _ = false

pow : Nat → Nat → Nat
pow n zero = 1
pow n (suc m) = times n (pow n m)

-- Seznami

data List (A : Set) : Set where
    [] :  List A
    _::_ : A → List A → List A

_++_ : {A : Set} → List A → A → List A
[] ++ a = a :: []
(a :: tail) ++ b = a :: (tail ++ b)


-- Končne množice

data Fin : Nat → Set where
    zero : {n : Nat} → Fin (suc n)
    suc : {n : Nat} → Fin n → Fin (suc n)

infixl 25 _/_

_/_ : (m n : Nat) → Fin (suc (plus m n))
zero / n = zero
suc m / n = suc (m / n)


-- Vektorji

data Vec (A : Set) : Nat → Set where
    [] : Vec A zero
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

_[_] : {A : Set} {n : Nat} → Vec A n → Fin n → A
[] [ () ]
(x :: v) [ zero ] = x
(x :: v) [ suc ind ] = v [ ind ]

_[_]←_ : {A : Set} {n : Nat} → Vec A n → Fin n → A → Vec A n
_[_]←_ [] ()
_[_]←_ (x :: xs) zero v = v :: xs
_[_]←_ (x :: xs) (suc i) v = x :: (xs [ i ]← v)


-- Sintaksa jezika

infixr 3 _；_ 
infix 4 _:=_
infix 5 IF_THEN_ELSE_END
infix 6 WHILE_DO_DONE
infix 6 SKIP
infix 7 _OR_
infix 8 _AND_
infix 9 NOT_
infix 10 _≡_
infix 10 _>_
infix 10 _<_

infixl 11 _+_
infixl 12 _*_
infixr 13 _**_
infix 14 !_
infix 15 `_

-- Artimetične in logične izraze ter ukaze parametriziramo z naravnim številom `n`,
-- ki pove, da izraz uporablja spremenljivke indeksirane med `0` in `n - 1`.

data Exp (n : Nat) : Set where
    `_ : Nat → Exp n
    !_ : Fin n → Exp n -- Spremenljivke nazivamo z naravnimi števili manjšimi od `n`
    _+_ : Exp n → Exp n → Exp n
    _*_ : Exp n → Exp n → Exp n
    _**_ : Exp n → Exp n → Exp n

data BExp (n : Nat) : Set where
    𝔹 : Bool → BExp n
    _≡_ : Exp n → Exp n → BExp n
    _<_ : Exp n → Exp n → BExp n
    _>_ : Exp n → Exp n → BExp n
    _AND_ : BExp n → BExp n → BExp n
    NOT_ : BExp n → BExp n
    _OR_ : BExp n → BExp n → BExp n

data Cmd : (n : Nat) → Set where
    IF_THEN_ELSE_END : {n : Nat} → BExp n → Cmd n → Cmd n → Cmd n
    WHILE_DO_DONE : {n : Nat} → BExp n → Cmd n → Cmd n
    _；_ : {n : Nat} → Cmd n → Cmd n → Cmd n
    _:=_ : {n : Nat} → (Fin n) → Exp n → Cmd n
    SKIP : {n : Nat} → Cmd n
    FOR_:=_TO_DO_DONE : {n : Nat} → Fin n → Exp n → Exp n → Cmd n → Cmd n
    PRINT_ : {n : Nat} → Exp n → Cmd n

-- Primer aritmetičnega izraza, ki sešteje vrednosti spremenljivk na mestu 1 in 0 v stanju s tremi spremenljivkami. 
primer : Exp 3
primer = ! 1 / 1 + ! 0 / 2 -- Da lahko uporabimo vrednost na mestu 0 in 1 v izrazu velikosti do 3.

-- Program, ki sešteje prvih n naravnih števil
vsota : Nat → Cmd 3
vsota n = 
    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    1 / 1 := ` 0 ；
    2 / 0 :=  ! (0 / 2) ；
    WHILE ! (1 / 1) < ! (0 / 2) DO
        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
        1 / 1 := ! 1 / 1 + ` 1
    DONE

-- Program, ki sešteje prvih n naravnih števil s pomočjo for zanke

sestevek : Nat → Cmd 3
sestevek n = 
    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    1 / 1 := ` 0 ；
    2 / 0 :=  ! (0 / 2) ；
    FOR (1 / 1) := (` 1) TO ! (0 / 2) DO
        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
        1 / 1 := ! 1 / 1 + ` 1
    DONE



-- Stanje

State : Nat → Set
State n = Vec Nat n

--Result : Nat → Set
--Result n = State n

-- Če želite, lahko za nadgradnjo rezultatov uporabite spodnje tipe

record Pair (A B : Set) : Set where
     constructor _,_
     field
         fst : A
         snd : B

--Result : Nat → Set
--Result n = Pair (State n) (List Nat)

data Maybe (A : Set) : Set where
     nothing : Maybe A
     just : A → Maybe A

Result : Nat → Set
Result n = Pair (Maybe (State n)) (List Nat)

evalExp : {n : Nat} → State n → Exp n → Nat
evalExp st (` x) = x
evalExp st (! i) = st [ i ]
evalExp st (exp₁ + exp₂) = plus (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ * exp₂) = times (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ ** exp₂) = pow (evalExp st exp₁) (evalExp st exp₂)

evalBExp : {n : Nat} → State n → BExp n → Bool
evalBExp st (𝔹 bexp) = bexp
evalBExp st (exp₁ ≡ exp₂) = (evalExp st exp₁) == (evalExp st exp₂)
evalBExp st (exp₁ < exp₂) = (evalExp st exp₁) lessthan (evalExp st exp₂)
evalBExp st (exp₁ > exp₂) = (evalExp st exp₂) lessthan (evalExp st exp₁)
evalBExp st (bexp₁ AND bexp₂) = (evalBExp st bexp₁) ∧ (evalBExp st bexp₂)
evalBExp st (NOT bexp) = ¬ (evalBExp st bexp)
evalBExp st (bexp₁ OR bexp₂) = (evalBExp st bexp₁) ∨ (evalBExp st bexp₂)

evalCmd : {n : Nat} → Nat → Result n → Cmd n → Result n
evalCmd n (just st , lst) IF bexp THEN cmd₁ ELSE cmd₂ END =
    if evalBExp (st) bexp then
        evalCmd n (just st , lst) cmd₁
    else
        evalCmd n (just st , lst) cmd₂
evalCmd (suc n) (just st , lst) WHILE bexp DO cmd DONE =
    if evalBExp st bexp then
        evalCmd n (evalCmd n (just st , lst) cmd) (WHILE bexp DO cmd DONE)
    else
        (just st , lst) 
evalCmd n (just st , lst) (cmd₁ ； cmd₂) = evalCmd n (evalCmd n (just st , lst) cmd₁) cmd₂
evalCmd _ (just st , lst) (ℓ := exp) = (just (st [ ℓ ]← (evalExp st exp)), lst) 
evalCmd _ (just st , lst) SKIP = (just st , lst)
evalCmd zero (just st , lst) (WHILE bexp DO cmd DONE) = (nothing , lst)
evalCmd (suc n) (just st , lst) FOR ℓ := n₁ TO n₂ DO cmd DONE =
    if evalBExp st (n₁ < n₂) then
        evalCmd n (evalCmd n (just st , lst) cmd) (FOR ℓ := n₁ + ` 1 TO n₂ DO cmd DONE)
    else
        (just st , lst)
evalCmd zero (just st , lst) FOR ℓ := n₁ TO n₂ DO cmd DONE =
    (nothing , lst)
evalCmd n (just st , lst) (PRINT exp) = (just st , (lst ++ (evalExp st exp)))
evalCmd n (nothing , lst) cmd = (nothing , lst)

-- Pozor: tip funkcije ima smisel zgolj za osnovni tip rezultata
--vsotaPrvihN : Nat → Nat
--vsotaPrvihN n = (evalCmd 125 ( 0 :: (0 :: (0 :: []))) (vsota n)) [ 2 / 0 ]
