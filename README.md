# yasuosat

A SAT-Solver implementation written by [yasuo-ozu](https://github.com/yasuo-ozu).

yasuosat is not an inclemental SAT solver, which means it not allows:

- adding new clauses.
- adding new variables. (because of the upper condition).
- having multiple states.

yasuosat is hoped to be (a bit) faster than inclemental SAT solvers because of this limitations.

Because of the first one, we can store clauses in fixed heap which is allocated in advance. It means we can refer to the clauses using fixed memory address. If we use dynamic vector, we cannot use fixed pointer because the vector may be reallocated and the addresses of the clauses are changed. Managing clauses by fixed pointer is hoped to be more efficient than other ways, for example, referrence counters or indexes in the vector.

Second limitation leads to simplify managing data which is coresponded to the literals. Literals takes the integer of -N .. -1, 1 .. N, where N is the number of variables. If N is fixed, we can store managing data in a (2N+1) vector, which is indexed as (N + lit). Here, in Rustlang, we can use `NonZeroI32` to represent literals, which has good compatibility with `Option<NonZeroI32>`. If N is not fixed, we can also use (2N) vector with (abs(lit) * 2 + sign(lit)), where sign() is one of 0 and 1, but here the representation of literals is not good with Option.
