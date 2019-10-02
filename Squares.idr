module Squares

-- Define evaluative multiplication.
total mult_eval : (n: Nat) -> (m: Nat) -> Nat
mult_eval Z m = Z
mult_eval (S k) m = m + (mult_eval k m)

-- Proof that our evaluative multiplication is the same as built in.
total mult_proof : (n: Nat) -> (m: Nat) -> (mult_eval n m) = (n * m)
mult_proof Z Z = Refl
mult_proof Z m = Refl
mult_proof (S k) m = cong (mult_proof k m)

-- Proof that (n*m) + m = ((n+1) * m)
total mult_plus_n : (n: Nat) -> (m: Nat) -> (n * m) + m = (S n) * m
mult_plus_n Z Z = Refl
mult_plus_n Z (S k) = cong (mult_plus_n Z k)
mult_plus_n (S k) m = rewrite plusCommutative (plus m (mult k m)) m in
    Refl

-- Proofs involving squaring numbers.
-- Give a definition of a square number.
total sq_def : (n: Nat) -> Nat
sq_def n = n * n

-- Give an evaluative method to compute a square number.
total sq_eval : (n : Nat) -> Nat
sq_eval n = mult_eval n n

-- Show that our square eval method is the same as the definitional method.
total sq_mult : (n : Nat) -> sq_eval n = sq_def n
sq_mult Z = Refl
sq_mult (S k) = rewrite mult_proof k (S k) in Refl
