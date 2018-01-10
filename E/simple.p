tff(term_type, type, term: $tType).
tff(mul_type, type, times: (term * term) > term).
tff(transpose_type, type, transpose: term > term).
tff(lower_tri_type, type, lower_tri: term > $o).
tff(mat_type, type, mat: $int > term).

# tff(ditranspose, axiom, ! [X: term] : transpose(transpose(X)) = X).

# tff(transpose_times, axiom, ! [X: term, Y: term] : transpose(times(X, Y)) = times(transpose(Y), transpose(X))).

tff(lower_tri_times, axiom, ! [X: term, Y: term] : ((lower_tri(X) & lower_tri(Y)) <=> lower_tri(times(X, Y)))).

tff(mats_distinct, axiom, ![M: $int, N: $int] :  (M = N) <=> (mat(M) = mat(N))).
tff(mat_not_mul, axiom, ![M: $int, B: term, C: term] : mat(M) != times(B, C)).
tff(mat_not_transpose, axiom, ![M: $int, B: term] : mat(M) != transpose(B)).

tff(prob, conjecture, (lower_tri(mat(0)) & ~lower_tri(mat(1))) => lower_tri(times(mat(0), mat(1)))).
