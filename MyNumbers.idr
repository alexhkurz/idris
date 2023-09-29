module MyNumbers

data N = O | S N

add : N -> N -> N
add O m = m
add (S n) m = S (add n m)

add_assoc : (a : N) -> (b : N) -> (c : N) -> add (add a b) c = add a (add b c)
add_assoc O b c = Refl
add_assoc (S a) b c = rewrite add_assoc a b c in Refl

add_zero : (n : N) -> add n O = n
add_zero O = Refl
add_zero (S n) = rewrite add_zero n in Refl

comm_add : (m : N) -> (n : N) -> add m n = add n m
comm_add O n = rewrite add_zero n in rewrite sym $ add_zero (add n O) in Refl
comm_add (S m) n = rewrite comm_add m n in rewrite add (S m) n in rewrite add n (S m) in
                   rewrite comm_add n (S m) in Refl
