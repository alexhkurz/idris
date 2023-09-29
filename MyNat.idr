module MyNumbers

data N = O | S N

add : N -> N -> N
add O m = m
add (S n) m = S (add n m)


