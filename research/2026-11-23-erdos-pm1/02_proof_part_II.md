# Part II, written out: (a) and (b) with odd values force q to be a square

Referee's own write-up (2026-11-23) of the algebraic part of `00_summary.md`, sections 4 and 5. Every step
was checked by hand; the statements were also tested by `python/erdos_pm1_referee.py` (see
`01_referee_report.md`). Nothing here uses analysis except one rearrangement of an absolutely convergent
series (Lemma 2, step 1). ASCII only. The notation differs from the summary where the summary reuses a
letter (its c_p is both a number and a group generator): generators are called t_p here.

## 0. Statement

q > 1 odd; P = set of primes dividing q; k_p = v_p(q); s_p = v_2(p - 1) >= 1.
M(q) = set of integers m >= 1 all of whose prime factors lie in P.
Z2 = ring of rational numbers with odd denominator; "x is odd" means x is a unit of Z2;
"x = y mod 2^j" means x - y in 2^j Z2.
f : Z/q -> Q is a function. For a unit a mod q and p in P put

    g(a) = sum_{m in M(q)} f(a m)/m          (absolutely convergent: sum_{m in M(q)} 1/m is finite)
    c_p  = sum_{r = 1..q} f(r) lam(r,p),     lam(r,p) = v_p(r) if v_p(r) < k_p, and k_p + 1/(p-1) otherwise.

Hypotheses:  (H0) f(0) = 0.   (Hodd) f(r) is odd for every r != 0.
             (a) g(a) = 0 for every unit a.   (b) c_p = 0 for every p in P.
Put  ell_p = sum of f(r) over the r != 0 in Z/q with p^(k_p) | r   (an empty sum if q = p^(k_p)).

    Theorem A.  (H0), (Hodd), (a)          =>  ell_p = (p-1) k_p  mod 2^(s_p + 1)   for every p in P.
    Theorem B.  (H0), (Hodd), c_p = 0      =>  ell_p = 0          mod 2^(s_p + 1).
    Theorem C.  (H0), (Hodd), (a), (b)     =>  every k_p is even, i.e. q is a perfect square.

C follows from A and B: (p-1) k_p = 0 mod 2^(s_p+1) and v_2(p-1) = s_p give k_p even.

Dependencies:  Lemma 1 <- (C1).   Lemma 2 <- (C1), (C2), (C3), (C4), (F1).   Lemma D <- (F1), (F2).
Lemma KL <- Lemma D, (L1), (L2), (F1).   Theorem A <- Lemmas 1, 2, KL, (F1), (F2 i), (G).
Theorem B <- no lemma (a count and a congruence).   Theorem C <- Theorems A, B.

External facts used (complete list):
(X1) Chinese remainder theorem; for an odd prime p and j >= 1 the reduction (Z/p^j)^* -> (Z/p)^* is onto;
     (Z/p)^* is cyclic of order p - 1.
(X2) Unique factorization of integers.
(X3) An absolutely convergent series may be rearranged and grouped.
(X4) A polynomial ring modulo a monic polynomial of degree e is a free module of rank e; a group ring R[T] is
     a free R-module with basis T.
(X5) Lattice duality over Z2, stated as (L1) below.

## 1. Notation

For p in P let C_p be a cyclic group of order 2^(s_p), written multiplicatively, with generator t_p, and
chi_p : (Z/p)^* -> C_p a surjective homomorphism (exists by X1; its kernel is the subgroup of odd order
(p-1)/2^(s_p)). For a subset n of P:
    S_n = product of the C_p, p in n (S_empty = 1), a subgroup of S = S_P;
    [u]_n = (chi_p(u mod p))_{p in n} in S_n, for an integer u prime to every p in n;
    s_n = sum of s_p;  phi(n) = product of (p-1);  o(n) = phi(n)/2^(s_n) (an odd integer);
    nu(n) = product of k_p   (all over p in n; empty products are 1).
Group rings: for a commutative ring R, R[S_n] is a subring of R[S]. eps : Q[S] -> Q is the sum of the
coefficients (a ring homomorphism). N_p = sum of the elements of C_p; N_n = product of N_p, p in n.
(G) Elementary rules: N_p t_p = N_p; (1 - t_p) N_p = 0; x N_P = eps(x) N_P for x in Q[S]; eps(N_n) = 2^(s_n);
    if x in Q[S] and (1 - c) x = 0 for all c in C_p, then x = N_p w with a unique w in Q[S_{P - p}], and w has
    coefficients in Z2 if x has (the coefficients of w are coefficients of x).
For r in Z/q: d(r) = gcd(r,q), N(r) = q/d(r), n(r) = set of primes dividing N(r) = {p : v_p(r) < k_p},
    cl(r) = [r/d(r)]_{n(r)} in S_{n(r)}   (r/d(r) is well defined and a unit modulo N(r)).
n(r) is empty exactly for r = 0. For a non-empty subset n of P and a divisor N > 1 of q:
    Phi_N = sum_{r : N(r) = N} f(r) cl(r),        g_n = o(n)^(-1) sum_{r : n(r) = n} f(r) cl(r)   in Q[S_n],
so o(n) g_n = sum of Phi_N over the divisors N whose set of primes is n (there are nu(n) of them).
    u_p = product over p' in P, p' != p, of chi_{p'}(p)^(-1)   in S_{P - p};
    a_p = p - u_p in Z[S];      a_n = product of a_p, p in n.

Counting facts.
(C1) Let N > 1 divide q, with set of primes n. u -> [u]_n is a surjective homomorphism (Z/N)^* -> S_n (X1).
     So each class sigma in S_n contains exactly phi(N)/2^(s_n) = (N / rad N) o(n) units mod N: an odd number.
     The r in Z/q with N(r) = N are the r = (q/N) u, u a unit mod N, and cl(r) = [u]_n.
(C2) Let x in S and A_x = {a in (Z/q)^* : [a]_P = x}; |A_x| = phi(q)/2^(s_P). Let N, n be as in (C1) and x_n
     the component of x in S_n. Then a -> a mod N maps A_x onto {u in (Z/N)^* : [u]_n = x_n}, and every
     fibre has |A_x| 2^(s_n) / phi(N) elements.
     Proof: a -> (a mod N, [a]_{P - n}) is a homomorphism (Z/q)^* -> (Z/N)^* x S_{P-n}; by X1 it is the
     product, over p in P, of the surjections (Z/p^(k_p))^* -> (Z/p^(v_p(N)))^* (p in n) or -> C_p (p not
     in n), so it is onto with fibres of equal size. A_x is the preimage of {u : [u]_n = x_n} x {x_{P-n}}.
(C3) Every m in M(q) is uniquely  m = d * product_{p in P - n} p^(j_p)  with d a divisor of q, n the set of
     primes of N = q/d, and integers j_p >= 0; here d = gcd(m,q). (For p in n: v_p(m) = v_p(d) < k_p; for p
     not in n: v_p(m) >= k_p = v_p(d). X2.) For a unit a and r = a m mod q: d(r) = d, N(r) = N,
     cl(r) = [a]_n * product_{p in P - n} [p]_n^(j_p).
(C4) If N = q/d has set of primes n, then phi(q)/(d phi(N)) = product_{p in P - n} (1 - 1/p).

Ring facts.
(F1) Let R be a commutative ring whose additive group is torsion-free (R = 0 allowed), T a finite abelian
     group, pi an integer different from 1 and -1, and u = zeta sigma with sigma in T and zeta in R,
     zeta^e = 1 for some e >= 1. Then multiplication by pi - u is injective on R[T]; if R contains Q, pi - u
     is invertible in R[T].
     Proof: u^E = 1 for E = e |T|, and (pi - u)(sum_{j<E} pi^(E-1-j) u^j) = pi^E - 1, a non-zero integer.
     R[T] is a free R-module, so torsion-free, so a non-zero integer acts injectively (invertibly over Q).
(F2) Let L' be a commutative ring, C a cyclic group of order e with generator t, L = L'[C],
     N = 1 + t + ... + t^(e-1), and beta : L -> L' the L'-algebra homomorphism with beta(t) = 1. Then
     (i)   {x in L : (1 - t) x = 0} = N L = N L';  N x = N beta(x) for all x in L;  w -> N w is injective
           on L';
     (ii)  the kernel of beta is (1 - t) L;
     (iii) if L' = R[T], then L/NL = R'[T] with R' = R[C]/(N) = R[X]/(1 + X + ... + X^(e-1)), a free R-module
           of rank e - 1 (X4); so R' is torsion-free if R is, and the image of t in R' has e-th power 1.
     Proof: write x = sum x_i t^i with x_i in L'. (1-t)x = 0 iff all x_i are equal iff x = N x_0. N t = N
     gives N x = N beta(x). The coefficient of t^0 in N w is w. x - beta(x) = sum x_i (t^i - 1) lies in
     (1-t)L. (iii): R[C] = R[X]/(X^e - 1) and X^e - 1 = (X - 1)(1 + ... + X^(e-1)).

## 2. Lemma 1 and Theorem B (parity only)

Lemma 1. Assume (Hodd). For every non-empty n: g_n = nu(n) N_n + 2 e_n with e_n in Z2[S_n].
Proof. Fix a divisor N of q with set of primes n and sigma in S_n. By (C1) the coefficient of sigma in Phi_N
is a sum of (N/rad N) o(n) values f(r), r != 0: an odd number of odd elements of Z2, hence odd. Summing over
the nu(n) divisors N and dividing by the odd integer o(n): every coefficient of g_n is = nu(n) mod 2. QED

Theorem B. Assume (H0), (Hodd) and c_p = 0; write k = k_p, s = s_p. Then ell_p = 0 mod 2^(s+1).
Proof. The term r = q of c_p is f(0) lam(q,p) = 0. Multiply c_p = 0 by p - 1:
    sum_{r != 0, v_p(r) < k} (p-1) v_p(r) f(r)  +  ((p-1) k + 1) ell_p  =  0.
In the first sum f(r) = 1 mod 2 and p - 1 = 0 mod 2^s, so each term is = (p-1) v_p(r) mod 2^(s+1). The number
of r in Z/q with v_p(r) = j (0 < j < k) is (q/p^j)(1 - 1/p) = (q/p^k) p^(k-j-1) (p-1), so the first sum is
= (p-1)^2 * integer = 0 mod 2^(2s), and 2s >= s + 1. Finally (p-1) k + 1 is odd. QED

## 3. Lemma 2 (the main equation)

Lemma 2. Assume (H0) and (a). Then
    (M)     sum over non-empty subsets n of P of   a_n N_{P - n} g_n   =  0     in Q[S].
Proof. Step 1 (X3, C3): for a unit a,
    g(a) = sum_{d | q, d < q} (1/d) sum_{(j_p) in N^(P-n)} f(a d prod p^(j_p)) prod p^(-j_p),
where n is the set of primes of N = q/d; the terms with d = q vanish by (H0).
Step 2. Fix x in S, a divisor N = q/d > 1 with set of primes n, and a tuple (j_p). Put theta = prod_{p in
P-n} [p]_n^(j_p) in S_n. By (C2), as a runs over A_x the residue a mod N takes each unit u with [u]_n = x_n
exactly |A_x| 2^(s_n)/phi(N) times; u -> u prod p^(j_p) is a bijection onto the units of class x_n theta;
with (C1), (C3):
    sum_{a in A_x} f(a d prod p^(j_p)) = (|A_x| 2^(s_n)/phi(N)) * (coefficient of x_n theta in Phi_N).
Step 3. Put Gam = sum_{x in S} (sum_{a in A_x} g(a)) x in Q[S]. For F in Q[S_n] and theta in S_n,
sum_{x in S} (coefficient of x_n theta in F) x = N_{P-n} theta^(-1) F, and N_{P-n} [p]_n^(-1) = N_{P-n} u_p for p
in P - n (u_p and [p]_n^(-1) differ by an element of S_{P-n}). With (C4) and |A_x| = phi(q)/2^(s_P):
    Gam = sum_{N > 1} 2^(-s_{P-n}) prod_{p in P-n} (1 - 1/p) [ sum_{(j_p)} prod (u_p/p)^(j_p) ] N_{P-n} Phi_N.
The inner sum is prod_{p in P-n} (1 - u_p/p)^(-1) = prod p a_p^(-1) (geometric series in the finite
dimensional algebra Q[S]; a_p is invertible by F1). Since (1 - 1/p) p = p - 1 and 2^(-s_{P-n}) phi(P-n)
= o(P-n), grouping the N by their set of primes n gives
    Gam = sum_n o(P-n) o(n) a_{P-n}^(-1) N_{P-n} g_n = o(P) sum_n a_{P-n}^(-1) N_{P-n} g_n.
Step 4. By (a), Gam = 0. Multiply by a_P = a_n a_{P-n} and divide by o(P). QED
(Only "sum of g over each class A_x is 0" was used.)

## 4. Lemma D

Setting D. R a commutative ring with torsion-free additive group (R = 0 allowed); m a finite set; for each p
in m: a finite cyclic group C_p with generator t_p, an integer pi_p not in {1, -1}, and u_p = zeta_p sigma_p
with zeta_p in R, zeta_p^e = 1 for some e >= 1, sigma_p in S_{m - p} (S_n = product of the C_p, p in n).
L = R[S_m];  a_p = pi_p - u_p;  a_n = prod_{p in n} a_p;  Delta_n = prod_{p in n} (1 - t_p);  N_n as before.
    I   = sum over subsets n of m of  a_n N_{m-n} L,
    I^# = {x in L : x Delta_n lies in a_n L for every subset n of m}.
Lemma D. I = I^#.
Proof. By (F1) every a_n acts injectively on L.
I inside I^#: for subsets k, n: if some p lies in n but not in k then N_{m-k} Delta_n = 0 because
N_p (1 - t_p) = 0; otherwise n is inside k and a_k N_{m-k} Delta_n = a_n (a_{k-n} N_{m-k} Delta_n).
I^# inside I: induction on |m|, for all settings at once. If m is empty, I = L = I^#. Let r in m,
m' = m - {r}, L' = R[S_m'], so L = L'[C_r]; let beta : L -> L' send t_r to 1 and write N = N_r. Two smaller
settings: (S1) (R, m', beta(u_p)): here beta(u_p) = zeta_p beta(sigma_p), beta(sigma_p) in S_{m'-p}; its
elements are beta(a_p). (S2) (R', m', images), R' = R[C_r]/(N), ring L'' = L/NL = R'[S_m'] (F2 iii): if
sigma_p = t_r^j sigma'_p with sigma'_p in S_{m'-p}, the image of u_p is (zeta_p t_r^j) sigma'_p, and
zeta_p t_r^j has finite order in R'. Note a_r lies in L' (sigma_r is in S_m'). Let x in I^#.
(1) Condition n = {r}: x (1 - t_r) = a_r z. Apply beta: 0 = a_r beta(z), so beta(z) = 0 (F1 in L'), so
    z = (1 - t_r) y (F2 ii), so (1 - t_r)(x - a_r y) = 0, so x = a_r y + N w with w in L' (F2 i).
(2) Let n be a subset of m'. The condition for n + r gives x Delta_n (1 - t_r) = a_n a_r z_n, and
    x (1 - t_r) = a_r y (1 - t_r) by (1). Cancel a_r: y Delta_n (1 - t_r) = a_n z_n. Apply beta:
    0 = beta(a_n) beta(z_n), so beta(z_n) = 0 (F1 for S1), z_n = (1 - t_r) t'_n,
    (1 - t_r)(y Delta_n - a_n t'_n) = 0, so y Delta_n lies in a_n L + N L. Hence the image of y in L'' lies in
    the #-ideal of (S2), which by induction is its I-ideal: y = y_1 + N y_2 with
    y_1 in sum_{n in m'} a_n N_{m'-n} L and y_2 in L. Then a_r y_1 lies in I (a_r a_n = a_{n+r},
    N_{m'-n} = N_{m-(n+r)}), and x - a_r y_1 = N (a_r y_2 + w) = N w_1 with w_1 = beta(a_r y_2 + w) in L'.
(3) N w_1 = x - a_r y_1 lies in I^# (I is inside I^#). Let n be a subset of m': N w_1 Delta_n = a_n z. Multiply
    by 1 - t_r: a_n (1 - t_r) z = 0, so (1 - t_r) z = 0, so z = N z' with z' in L' (F2 i). As N a_n
    = N beta(a_n): N (w_1 Delta_n - beta(a_n) z') = 0 with the bracket in L', so w_1 Delta_n = beta(a_n) z'
    (F2 i). So w_1 lies in the #-ideal of (S1), hence by induction in its I-ideal:
    w_1 = sum_{n in m'} beta(a_n) N_{m'-n} l_n, l_n in L'. Then N w_1 = sum a_n N_{m-n} l_n lies in I.
So x = a_r y_1 + N w_1 lies in I. QED
(Used with R = Z2 and all zeta_p = 1 only; the general R is needed for the induction.)

## 5. Lemma KL

Lattice facts. Let T be a finite abelian group; on Q[T] put <x,y> = sum_g x_g y_g and let * be the linear
involution g -> g^(-1).
(L2) <x z, y> = <x, y z^*> for x, y, z in Q[T] (both are the coefficient of 1 in x^* z^* y).
     {x in Q[T] : <x, Z2[T]> inside Z2} = Z2[T].
(L1) If J is a finitely generated Z2-submodule of Q[T] that spans Q[T], and J^v = {x : <x,J> inside Z2}, then
     (J^v)^v = J. (Z2 is a principal ideal domain: J has a basis; J^v is spanned by the dual basis.)

Setting KL. C_0 a finite abelian group; m a finite set; for p in m an integer pi_p not in {1, -1}, a finite
cyclic group C_p whose order divides pi_p - 1, with generator t_p, and u_p in C_0 x S_{m-p}.
G = C_0 x S_m; a_p = pi_p - u_p in Z[G]; a_n, N_n, Delta_n as before; N_0 = sum of the elements of C_0;
    I = sum over subsets n of m of a_n N_{m-n} Z2[G].
Lemma KL. If w in Z2[S_m] and N_0 w lies in I, then eps(w) lies in |S_m| Z2.
Proof. Let pr : Q[G] -> Q[S_m] be the ring homomorphism induced by the projection G -> S_m.
(K1) For w in Q[S_m] and y in Q[G]: <N_0 w, y> = <w, pr(y)> (the coefficient of N_0 w at (c,g) is w_g).
(K2) Put gam_n = Delta_n^* (a_n^*)^(-1) in Q[G] (F1), so gam_n^* = Delta_n a_n^(-1). For subsets n, k of m:
     gam_n^* a_k N_{m-k} = 0 if n is not inside k (as in Lemma D), and = Delta_n a_{k-n} N_{m-k} in Z[G] if
     n is inside k. Hence, by (L2), <gam_n l, y> = <l, y gam_n^*> lies in Z2 for all l in Z2[G], y in I.
(K3) Claim: e = N_m/|S_m| equals sum_n pr(gam_n) l_n for suitable l_n in Z2[S_m].
     Let J = sum_n pr(gam_n) Z2[S_m]; it contains Z2[S_m] (n empty), so it spans Q[S_m]. By (L2), x lies in
     J^v iff x pr(gam_n)^* = x Delta_n pr(a_n)^(-1) lies in Z2[S_m] for all n, i.e. (n empty) x in Z2[S_m]
     and x Delta_n in pr(a_n) Z2[S_m] for all n. So J^v is the ideal I^# of Lemma D for the setting
     (Z2, m, pr(u_p)) (pr(u_p) lies in S_{m-p}), hence J^v = I' := sum_n pr(a_n) N_{m-n} Z2[S_m], and by (L1)
     J = (I')^v. Now e lies in (I')^v: <e, y> = eps(y)/|S_m|, and for y = pr(a_n) N_{m-n} l,
     eps(y) = prod_{p in n} (pi_p - 1) * prod_{p not in n} |C_p| * eps(l), which lies in |S_m| Z2 because |C_p|
     divides pi_p - 1.
(K4) Put xi = sum_n gam_n l_n in Q[G] (l_n from K3, viewed in Z2[G]). Then pr(xi) = e. If N_0 w lies in I:
     <xi, N_0 w> lies in Z2 by (K2), and <xi, N_0 w> = <N_0 w, xi> = <w, e> = eps(w)/|S_m| by (K1). QED

## 6. Proof of Theorem A

Assume (H0), (Hodd), (a). Fix p_0 in P; write m = P - {p_0}, C_0 = C_{p_0}, N_0 = N_{p_0}, s_0, k_0, u_0 =
u_{p_0} (an element of S_m), and let pr : Q[S] -> Q[S_m] kill C_0. By Lemma 1 all g_n have coefficients in Z2.
Step 1 (split M). For non-empty n inside m: N_{P-n} = N_0 N_{m-n} and N_0 a_n = N_0 pr(a_n). For n = n' + p_0
with n' inside m: a_n = (p_0 - u_0) a_{n'} and N_{P-n} = N_{m-n'}. So (M) reads
    N_0 Z + (p_0 - u_0) B = 0,     Z = sum_{non-empty n in m} pr(a_n) N_{m-n} g_n            in Z2[S_m],
                                   B = sum_{n in m} a_n N_{m-n} g_{n + p_0}                   in Z2[S].
Step 2. For c in C_0: (1 - c) N_0 = 0, so (p_0 - u_0)(1 - c) B = 0, so (1 - c) B = 0 (F1). By (G),
B = N_0 w with w in Z2[S_m]. Then N_0 (Z + (p_0 - u_0) w) = 0 with the bracket in Q[S_m], so
    Z = -(p_0 - u_0) w.
Step 3 (augmentation). eps(pr(a_n)) = phi(n) = 2^(s_n) o(n), eps(N_{m-n}) = 2^(s_{m-n}), and o(n) eps(g_n) is
the sum of f(r) over n(r) = n. The r != 0 with n(r) inside m are those with p_0^(k_0) | r. Hence
    eps(Z) = 2^(s_m) ell_{p_0},   and by step 2:   2^(s_m) ell_{p_0} = -(p_0 - 1) eps(w).
Step 4 (w modulo 2). By Lemma 1, g_{n+p_0} = nu(n + p_0) N_0 N_n + 2 e_n with e_n in Z2[S_{n+p_0}]. As
a_n N_{m-n} N_0 N_n = a_n N_P = phi(n) N_P (G),
    B = c0 N_P + 2 B_e,   c0 = k_0 sum_{n in m} prod_{p in n} k_p (p-1) = k_0 prod_{p in m} (1 + k_p (p-1)),
    B_e = sum_{n in m} a_n N_{m-n} e_n.
c0 = k_0 mod 2 because every p - 1 is even. B_e lies in the ideal I of Lemma KL for (C_0, m, pi_p = p,
C_p, u_p): indeed u_p lies in S_{P-p} = C_0 x S_{m-p} and |C_p| = 2^(s_p) divides p - 1. Since B and N_P are
invariant under C_0, so is 2 B_e, hence B_e = N_0 w_e with w_e in Z2[S_m], and w = c0 N_m + 2 w_e.
Step 5. Lemma KL gives eps(w_e) in 2^(s_m) Z2. So eps(w) = c0 2^(s_m) + 2 eps(w_e) = 2^(s_m) (k_0 + 2 z) with
z in Z2, and by step 3
    ell_{p_0} = -(p_0 - 1)(k_0 + 2 z) = -(p_0 - 1) k_0 = (p_0 - 1) k_0     mod 2^(s_0 + 1)
(2 (p_0 - 1) lies in 2^(s_0+1) Z). QED
(If m is empty, i.e. q = p_0^(k_0): Z = 0, ell = 0, B = g_{p_0}, u_0 = 1, and the argument reads
(p_0 - 1) g_{p_0} = 0, so k_0 N_0 + 2 e = 0, so k_0 is even.)

## 7. Where each hypothesis is used

- f(0) = 0: Lemma 2 step 1 (the divisor d = q), Theorem B (the term r = q).
- f(r) odd: Lemma 1 only (and the first sum in Theorem B).
- q odd: every p in P is odd, so p - 1 is even (c0 = k_0 mod 2 in Theorem A; 2s >= s+1 in Theorem B) and
  p is neither 1 nor -1 (F1).
- C_p is the full 2-part quotient of (Z/p)^*: fibres of odd size (C1) for Lemma 1; o(n) odd.
- C_p cyclic: (F2), i.e. Lemma D. |C_p| divides p - 1: Lemma KL (K3). p not in {1, -1}: (F1).
- (a): only through "the sum of g over each class A_x vanishes" (Lemma 2). (b): only in Theorem B, for
  the same prime p.
