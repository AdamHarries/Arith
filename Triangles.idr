-- Proofs of triangular numbers?

-- tn2 eval computes the nth triangular number
total
tn_eval : (n : Nat) -> Nat
tn_eval Z = Z
tn_eval (S k) = (S k) + tn_eval k

-- define SUPER associativity!
superAssoc : (n: Nat) -> (m: Nat) -> (n + m) + (n + m) = n + (n + (m + m))
superAssoc n m = rewrite sym $ plusAssociative n m (n + m) in
    rewrite plusCommutative m (plus n m) in
    rewrite sym $ plusAssociative n m m in
    Refl

-- Two triangles make a square
tn_eval_sq : (n: Nat) -> (tn_eval n) + (tn_eval n) = n + (n * n)
tn_eval_sq Z = Refl
tn_eval_sq (S k) =
    rewrite sym $ plusSuccRightSucc (plus k (tn_eval k)) (plus k (tn_eval k)) in
    rewrite multCommutative k (S k) in
    rewrite superAssoc k (tn_eval k) in
    rewrite tn_eval_sq k in
    rewrite plusSuccRightSucc k (plus k (plus k (mult k k))) in
    Refl
