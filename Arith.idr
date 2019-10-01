module Arith

plusReduces : (n : Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesZ : (n : Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong (plusReducesZ k)

plusReducesS : (n: Nat) -> (m: Nat) -> S (plus n m) = plus (S n) m
plusReducesS n m = Refl

plusReducesSZ : (n : Nat) -> (m : Nat) -> S (plus n m) = plus n (S m)
plusReducesSZ Z m = Refl
plusReducesSZ (S k) m = cong (plusReducesSZ k m)

data Foo = FInt Int | FBool Bool

optional : Foo -> Maybe Int
optional (FInt x) = Just x
optional (FBool b) = Nothing

isFInt : (foo : Foo) -> Maybe (x : Int ** (optional foo = Just x))
isFInt foo with (optional foo) proof p
    isFInt foo | Nothing = Nothing
    isFInt foo | (Just x) = Just (x ** Refl)

fiveIsFive : 5 = 5
fiveIsFive = Refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

disjoint : (n : Nat) -> Z = S n -> Void
disjoint n prf = replace {P = disjointTy} prf ()
    where
        disjointTy : Nat -> Type
        disjointTy Z = ()
        disjointTy (S k) = Void

succBoth : S n = S m -> n = m
succBoth Refl = Refl

zEqOne : Z = S Z -> Void
zEqOne Refl impossible


addWorks : (n : Nat) -> n = S n -> Void
addWorks Z Refl impossible
addWorks (S k) prf = addWorks k (succBoth prf)


data Parity : Nat -> Type where
    Even : Parity (n + n)
    Odd : Parity (S (n + n))

helpEven : (j : Nat) -> Parity ((S j) + (S j)) -> Parity (S (S (plus j j)))
helpEven j p = rewrite plusSuccRightSucc j j in p

helpOdd : (j : Nat) -> Parity (S ((S j) + (S j))) -> Parity (S (S (S (plus j j))))
helpOdd j p = rewrite plusSuccRightSucc j j in p

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | Even = let result = Even {n=S j} in
        helpEven j result
    parity (S (S (S (j + j)))) | Odd = let result = Odd {n = S j} in
        helpOdd j result

natToBin : Nat -> List Bool
natToBin Z = Nil
natToBin k with (parity k)
    natToBin (j + j) | Even = False :: natToBin j
    natToBin (S (j + j)) | Odd = True :: natToBin j

four_eq : 4 = 4
four_eq = Refl

plus_reduces_Sk : (k, m: Nat) -> plus (S k) m = S (plus k m)
plus_reduces_Sk k m = Refl


nat_induction : (P : Nat -> Type) ->
    (base: P Z) ->
    ((k: Nat) -> P k -> P (S k)) ->
    (x : Nat) ->
    P x
nat_induction P base f Z = base
nat_induction P base f (S k) = f k (nat_induction P base f k)

plus_ind : Nat -> Nat -> Nat
plus_ind n m = nat_induction (\x => Nat)
    m
    (\k, k_rec => S k_rec)
    n

induct_base : (m : Nat) -> plus m 0 = m
induct_base Z = Refl
induct_base (S k) = eqSucc (k + 0) (k) (induct_base k)

plus_commutes_Z : plus m 0 = m
plus_commutes_Z {m = Z} = Refl
plus_commutes_Z {m = (S k)} = let rec = plus_commutes_Z {m=k} in
    rewrite rec in Refl

total
plus_commutes_rhs : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_rhs k Z = Refl
plus_commutes_rhs k (S j) = rewrite plus_commutes_rhs k j in Refl

total
plus_commutes : (n: Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z m = sym plus_commutes_Z
plus_commutes (S k) m = rewrite plus_commutes k m in (plus_commutes_rhs k m)

add : (n : Nat) -> (m : Nat ) -> Nat
add Z m = m
add (S k) m = S (add k m)

prove_works : (n : Nat) -> (m : Nat) -> add n m = n + m
prove_works Z m = Refl
prove_works (S k) m = cong (prove_works k m)

total 
tn_eval : (n : Nat) -> Nat
tn_eval Z = Z
tn_eval (S k)  = (S k) + tn_eval k

total 
tn_closed : (n: Nat) -> Nat
tn_closed Z = Z
tn_closed (S k) = divNatNZ ((S k) * ((S k) - 1)) 2 SIsNotZ

total 
tn_closed_proof : (n : Nat) -> (tn_eval n) = (tn_closed n)
tn_closed_proof Z = Refl
tn_closed_proof (S k) = let rec = tn_closed_proof {n=k} in ?what


--- Proofs involving square numbers

total mult_eval : (n: Nat) -> (m: Nat) -> Nat 
mult_eval Z m = Z
mult_eval (S k) m = m + (mult_eval k m)

total mult_proof : (n: Nat) -> (m: Nat) -> (mult_eval n m) = (n * m) 
mult_proof Z Z = Refl
mult_proof Z m = Refl
mult_proof (S k) m = cong (mult_proof k m)


total sq_eval : (n : Nat) -> Nat 
sq_eval Z = Z 
sq_eval (S k) = (sq_eval k) + (S k) + k

total sq_mult : (n : Nat) -> sq_eval n = mult_eval n n 
sq_mult Z = Refl
sq_mult (S k) = ?sq_mult_rhs_2

total sq_eval_induc : (n : Nat) -> (sq_eval (S n)) = (sq_eval n) + (S n) + n
sq_eval_induc Z = Refl
sq_eval_induc (S k) = Refl


total sq_prf : (x: Nat) -> (x * x) + (S (x + x)) = (S x) * (S x) 
sq_prf Z = Refl
sq_prf (S k) = cong (sq_prf k)

total 
sq_closed_proof : (n: Nat) -> (sq_eval n) = n * n
sq_closed_proof Z = Refl
sq_closed_proof (S k) = let rec = sq_closed_proof k in rewrite rec in ?hole
