tff(term_type, type, term: $tType).
tff(add_type, type, plus: (term * term) > term).
tff(mul_type, type, times: (term * term) > term).
tff(transpose_type, type, transpose: term > term).
tff(lower_tri_type, type, lower_tri: term > $o).
tff(upper_tri_type, type, upper_tri: term > $o).
tff(mat_type, type, mat: $i > term).

tff(add_comm, axiom, ! [X: term, Y: term] : plus(X, Y) = plus(Y, X)).

tff(add_assoc, axiom, ! [X: term, Y: term, Z: term] : plus(plus(X, Y), Z) = plus(X, plus(Y, Z))).

tff(mul_assoc, axiom, ! [X: term, Y: term, Z: term] : times(times(X, Y), Z) = times(X, times(Y, Z))).

tff(left_distrib, axiom, ! [A: term, B: term, C: term] : times(A, plus(B, C)) = plus(times(A, B), times(A, C))).

tff(right_distrib, axiom, ! [A: term, B: term, C: term] : times(plus(A, B), C) = plus(times(A, C), times(B, C))).

tff(ditranspose, axiom, ! [X: term] : transpose(transpose(X)) = X).

tff(transpose_times, axiom, ! [X: term, Y: term] : transpose(times(X, Y)) = times(transpose(Y), transpose(X))).

tff(lower_tri_trans, axiom, ! [X: term] : lower_tri(X) => upper_tri(transpose(X))).

tff(upper_tri_trans, axiom, ! [X: term] : upper_tri(X) => lower_tri(transpose(X))).

tff(lower_tri_times, axiom, ! [X: term, Y: term] : ((lower_tri(X) & lower_tri(Y)) => lower_tri(times(X, Y)))).

tff(upper_tri_times, axiom, ! [X: term, Y: term] : ((upper_tri(X) & upper_tri(Y)) => upper_tri(times(X, Y)))).

tff(matrices_distinct, axiom, ! [A: $i, B: $i] : A = B <=> mat(A) = mat(B)).

tff(mat_is_not_plus, axiom, ! [A: $i, B: term, C: term] : mat(A) != plus(B, C)).
tff(mat_is_not_times, axiom, ! [A: $i, B: term, C: term] : mat(A) != times(B, C)).
tff(mat_is_not_transpose, axiom, ! [A: $i, B: term] : mat(A) != transpose(B)).

tff(test_false, conjecture, ! [A: $i, B: $i] : A != B => mat(A) = mat(B)).
#tff(test, conjecture, lower_tri(times(mat(a), transpose(mat(b))))).
#tff(test2, conjecture, lower_tri(transpose(times(mat(b), transpose(mat(a)))))).
#tff(false1, conjecture, lower_tri(plus(a, b))).
