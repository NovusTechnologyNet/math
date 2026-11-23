# Erdos's conjecture for f = +-1 (sum f(n)/n != 0): the 2-adic obstruction, checked and proved

Date 2026-11-23. Marks: [P] proved here (section 5), [C] computed here (exact arithmetic unless stated),
[N] numerical (60 digits or more), [T] taken on trust. I read NONE of the papers; everything about the
literature comes from the two helper reports (research/2026-11-22-wide/Q06_chowla_erdos.md and
W2_Q11_erdos_pm1.md). Program: python/erdos_pm1_check.py (new; `selftest` passes in under a minute).

## 0. Verdict

The claim is TRUE, in a stronger and simpler form, and I have a complete proof (given Baker's theorem).

**Theorem [P].** Let q be odd and f: Z -> Q periodic mod q with f(n) = 0 for q | n and f(n) a rational
number with odd numerator and odd denominator for q not dividing n. If sum_{n>=1} f(n)/n = 0, then q is a
perfect square. In particular Erdos's conjecture (f(n) = +-1 for q not dividing n) holds for every q that
is not a perfect square (even q is trivial: the sum of f over a period is odd, so the series diverges).

- "q = 1 mod 4" and "not a prime power" are not needed; only "not a square" matters.
- The converse also holds [P, N]: for every odd square q there is an odd-valued f with sum f(n)/n = 0
  (explicit formula in 6.3). So no argument that uses only "f(n) is odd" can treat squares; the conjecture
  stays open exactly for odd squares not covered by size arguments (smallest: 11025 = 105^2, then 27225).
- The proof is new work of this session and has been checked only by me and by the computations below.
  Novelty is NOT verified (section 8).

## 1. The criterion (Okada), exact statement and derivation

q odd, P = set of primes dividing q, k_p = v_p(q), M(q) = {m >= 1 : every prime factor of m is in P}.
For f: Z/q -> Q define, for a in (Z/q)^* and p in P,

    g(a) = sum_{m in M(q)} f(am)/m          (absolutely convergent; an exact rational number)
    c_p  = sum_{r=1..q} f(r) lam(r,p),      lam(r,p) = v_p(r) if v_p(r) < k_p,  = k_p + 1/(p-1) otherwise.

**Formula [P, N].** If sum_{r<=q} f(r) = 0 (equivalent to convergence) then
    sum_{n>=1} f(n)/n = -(1/q) [ sum_{a in (Z/q)^*} g(a) psi(a/q) + sum_{p in P} c_p log p ],  psi = digamma.
**Criterion.** sum f(n)/n = 0  iff  (a) g(a) = 0 for all a in (Z/q)^*  and  (b) c_p = 0 for all p in P.
This is the form the helpers quote from Chatterjee-Murty 2015 (Prop 2.1); the second helper checked that it
has the same solution space as Okada's Theorem 10 read in the original. Logical form: necessary and
sufficient, for rational f (for algebraic f an irreducibility hypothesis is needed; not used here).

Derivation (mine). For s > 1 write n = mk uniquely with m in M(q), gcd(k,q) = 1:
L(s,f) = sum_{a unit} F_s(a) q^(-s) zeta(s,a/q), F_s(a) = sum_m f(am) m^(-s) (analytic for Re s > 0).
With zeta(s,x) = 1/(s-1) - psi(x) + O(s-1) and sum_a F_1(a) = sum_r f(r) = 0 (both are q times the residue),
letting s -> 1+ gives the formula; the log p terms come from F_1'(a) = -sum_m f(am) (log m)/m and the identity
sum_a sum_m f(am) v_p(m)/m = sum_r f(r) lam(r,p) (count the pairs (a,m) with am = r; a geometric series).
"If" is then clear. "Only if": by Gauss's formula psi(a/q) = -gamma - log 2q - (pi/2) cot(pi a/q)
+ 2 sum_{0<j<q/2} cos(2 pi a j/q) log sin(pi j/q), the relation is a linear form with coefficients in Q(zeta_q)
in log(-1), log sin(pi j/q), log p. Baker's theorem (logarithms of algebraic numbers that are linearly
independent over Q are so over the algebraic numbers) implies that the relation survives every Galois
conjugation of its coefficients (Baker-Birch-Wirsing lemma). Conjugating by zeta -> zeta^h replaces g by
g(h^-1 .) and fixes the rational c_p: T(h) + C = 0 for all h, T(h) = sum_a g(h^-1 a) psi(a/q), C = sum c_p log p.
Summing over h: sum_h T(h) = 0, so C = 0, so every c_p = 0 (unique factorization). Then T(h) = 0 for all h;
pairing with a character chi gives (sum_b chibar(b) g(b)) * (-q L(1,chi)) = 0, and L(1,chi) != 0 for
chi != 1, so g = 0 on the units.
Taken on trust [T]: Baker's theorem, Gauss's digamma formula, L(1,chi) != 0, the Laurent expansion of the
Hurwitz zeta function. Only the direction "sum = 0 implies (a) and (b)" is used in the Theorem.

**Solution space [P].** With (T_p h)(n) = h(pn) and Mop = prod_p (1 - T_p/p)^(-1) one has g = (Mop f) on the
units and c_p = sum over {n: gcd(n,q) = p^i, 1<=i<=k_p} of (Mop f)(n). So, for f(0) = 0, the solutions are
f = prod_p (1 - T_p/p) h with h = 0 on the units and at 0 and, for each p, sum of h over the set above = 0;
dimension q - 1 - phi(q) - t, t = |P| (Okada's count, as transcribed by the second helper).

## 2. Tests of the criterion (`criterion`, `lll`)

- [N] q = 9, 15, 21, 25, 27, 33, 35, 45, 49, 63, 75, 81, 99, 105, 135, 147, 165, 225: a random rational f in
  the solution space (values not +-1) has |sum f(n)/n| < 2e-70 (70-digit digamma arithmetic), and (a), (b)
  hold exactly.
- [N] the formula for sum f(n)/n holds to 60 digits for random integer-valued f with sum 0 outside the
  solution space; their sums are far from 0 (e.g. -6.77 for q = 9, 15.01 for q = 105).
- [N] random f satisfying (a) but not (b): the sum is non-zero and equals -(1/q) sum c_p log p.
- [N] completeness: for q = 9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 63, LLL (300 digits) finds exactly
  q - 1 - phi(q) - t integer relations of small height among {psi(r/q), 1}; the next lattice vector has
  squared norm above 10^14 (10^99 for q = 9). So no vanishing function of small height outside the space.

## 3. Computations

"Parity test for q": is there f in the solution space with every f(r), r != 0, odd (a 2-adic unit)?
(By duality this is the helpers' test "the 2-saturated row lattice has no vector of odd coordinate sum".)

- Method A (direct, `direct LO HI`) [C]. Unknowns 2^63 h on the non-units; the test is a linear system
  modulo 2^64 (the 2-adic denominators of h are at most 2^D0, D0 = sum_p v_2(p^(n_p) - 1) <= 63, checked for
  each q), decided by elimination with pivots of least valuation. Independent of sections 4-5.
  Result (`direct 9 2100`): all 733 odd composite q <= 2100: the survivors are exactly the 22 perfect
  squares 9, 25, ..., 2025. Also q = 4389 = 3*7*11*19: killed.
- Method B (reduced system: (M) of Lemma 2 plus (b), on 2-groups; `reduced 9 20000`) [C]. Agrees with
  method A on every q <= 400 (self-test). Of the 7738 odd composite q <= 20000, 7700 were tested (38 have
  systems with more than 1500 unknowns, because some v_2(p-1) is large; the 16 of these below 12000 were
  run separately, the 22 others not): survivors = squares, no exception. Beyond the range: the squares
  11025, 27225, 99225, 1002001 survive; 15015 = 3*5*7*11*13, 33075, 45045, 69745 = 5*13*29*37, 143325 are
  killed. Theorem A was also checked on explicit functions for q = 1105, 1225, 1365, 1921, 2465.
- Method C (brute force, `brute`) [C]. All sign patterns on the non-units, exact integers, no parity argument:
  q = 9, 15, 21, 25, 27, 33, 35, 39, 45 (2^20 patterns), 49, 51, 55, 57, 65, 77, 85, 91: no +-1 solution.
  For q = 9, 25, 49 the parity test survives (odd-valued solutions exist) but there is no +-1 solution.
- Theorem A on explicit functions (`theoremA`) [C]. For 24 values of q (21 ... 765, up to 174 distinct values
  of f) an explicit odd-valued rational f satisfying (a) (verified exactly for q <= 120) has
  sum_{r != 0, p^k | r} f(r) = (p-1)k mod 2^(s+1) for every p | q.
- Lemmas 1, 2 (`mainequation`) [C]. For q = 15, 21, 45, 63, 75, 105, 117, 135, 165, 225, 273, 315, 495, 525
  the identity (M) holds exactly for a random rational solution of (a) and fails for a random f; Lemma 1
  holds for the odd-valued solutions. Theorem B (self-test): for 135 random odd-valued (f, p),
  (p-1) c_p = ((p-1)k+1) * sum_{r != 0, p^k | r} f(r) mod 2^(s+1).
- Lemmas on random abstract data (`abstract 7 3`) [C]: Lemma D (index equality, 243 instances), Lemma KL
  (243), Theorem A (126), and "no non-square pattern survives" (198), with arbitrary group elements u_p
  (so no reciprocity law is hidden anywhere): no failure.

## 4. Statements

Z_(2) = rationals with odd denominator; "odd" = unit of Z_(2); s_p = v_2(p-1).
**Theorem A [P].** Let f: Z/q -> Q, f(0) = 0, f(r) odd for r != 0, and assume (a). Then for every p in P
    sum_{r != 0, p^(k_p) | r} f(r)  =  (p-1) k_p   (mod 2^(s_p+1) Z_(2)).
**Theorem B [P].** If f(0) = 0, f(r) is odd for r != 0 and (b) holds for p, then the same sum is 0 mod 2^(s_p+1).
**Corollary.** (a) and (b) together force (p-1) k_p = 0 mod 2^(s_p+1), i.e. k_p even, for every p: the Theorem.
For f = +-1 Theorem A says: (q/p^k - 1) - 2 #{r != 0 : p^k | r, f(r) = -1} = (p-1)k mod 2^(s+1).
Simplest instance (f = +-1, p = 3 mod 4 dividing q exactly once): (a) forces the number of r prime to p with
f(r) = -1 to be even; (b) says sum_{p | r} f(r) = 0, hence sum_{p not | r} f(r) = 0, which makes that number
(q/p)(p-1)/2, odd. Example q = 21 [C]: f = 1/3 on the multiples of 3, 1 on {7, 14}, -1/3 on the units satisfies
(a) with odd values; its sums over the multiples of 3 and of 7 are 2 and 2 (= p-1 mod 4), so (b) fails:
c_3 = 3, c_7 = 7/3 and sum f(n)/n = -(3 log 3 + (7/3) log 7)/21 = -0.37315685145079651362...

## 5. Proofs

### 5.1 Notation
C_p = (Z/p)^* modulo its subgroup of odd order (cyclic of order 2^(s_p), generator c_p). For n subset P:
S_n = prod_{p in n} C_p; [u]_n in S_n is the class of an integer u prime to n; s_n = sum s_p;
phi(n) = prod (p-1); o(n) = phi(n)/2^(s_n) (odd); nu(n) = prod_{p in n} k_p. Group rings Z_(2)[S_n] inside
Z_(2)[S_P]; N_p = sum of the elements of C_p, N_n = prod_{p in n} N_p; eps = sum of coefficients; a function
phi on S_n is the element sum_x phi(x) x. For r in Z/q: N(r) = q/gcd(r,q), n(r) = set of primes dividing N(r),
cl(r) = [r/gcd(r,q)]_{n(r)}. For non-empty n put
    g_n = o(n)^(-1) sum_{r : n(r) = n} f(r) cl(r)  in Q[S_n].
u_p in S_{P - p} has C_{p'}-component [p]_{p'}^(-1) (p' != p);  a_n = prod_{p in n} (p - u_p).

### 5.2 Two lemmas on f
**Lemma 1.** If f(r) is odd for all r != 0 then g_n = nu(n) N_n + 2 e_n with e_n in Z_(2)[S_n].
Proof. Fix N | q with prime set n and sigma in S_n. The r with N(r) = N, cl(r) = sigma correspond to the
units mod N in the class sigma: phi(N)/2^(s_n) = (N/rad N) o(n) of them, an odd number. So their f-sum is
odd; there are nu(n) such N; and o(n) is odd.

**Lemma 2 (main equation).** If f(0) = 0 and (a) holds then
    (M)   sum_{n non-empty} a_n N_{P - n} g_n = 0   in Q[S_P].
Proof. Each m in M(q) is uniquely m = d * prod_{p not in n} p^(j_p) with d = gcd(m,q), N = q/d, n = primes of
N, j_p >= 0. For a unit a: N(am) = N and cl(am) = [a]_n prod_{p not in n} [p]_n^(j_p). Fix x in S_P and let
A_x = {a unit : [a]_P = x} (a coset of the odd part, |A_x| = phi(q)/2^(s_P)). As a runs over A_x, a mod N
runs uniformly over the units mod N of class x_n (the image of x in S_n). With Phi_N(sigma) = sum of f(r)
over N(r) = N, cl(r) = sigma, and (tau_p F)(sigma) = F(sigma [p]_n) for functions on S_n:
    sum_{a in A_x} g(a) = sum_N (|A_x| 2^(s_n) / (d phi(N))) [prod_{p not in n} (1 - tau_p/p)^(-1) Phi_N](x_n)
                        = o(P) sum_n [D_n^(-1) g_n](x_n),      D_n = prod_{p not in n} (p - tau_p),
because |A_x| 2^(s_n)/(d phi(N)) = 2^(-s_{P-n}) prod_{p not in n} (1 - 1/p), and the term n = empty is f(0) = 0.
So (a) gives sum_n (D_n^(-1) g_n) o pi_n = 0 on S_P (pi_n: S_P -> S_n). Apply prod_{p in P} (p - T_p),
(T_p F)(x) = F(x ubar_p), ubar_p = ([p]_{p'})_{p' != p}: for p not in n, T_p acts on functions of x_n as
tau_p, so these factors cancel D_n^(-1). In group-ring language F o pi_n is N_{P-n} F and T_p is multiplication
by u_p = ubar_p^(-1). QED

### 5.3 Lemma D (an ideal described by divisibility conditions)
Setting: O a commutative ring that is torsion-free over Z_(2); Gamma a finite subgroup of O^x; m a finite
set; for p in m a finite cyclic group C_p with generator c_p, an integer pi_p not in {0, 1, -1}, and
u_p in Gamma x S_{m - p}. Lambda = O[S_m], a_p = pi_p - u_p, a_n = prod_{p in n} a_p, Delta_n = prod_{p in n}
(1 - c_p).
**Lemma D.**  I_m := sum_{n subset m} a_n N_{m - n} Lambda  equals  I_m^# := {x in Lambda : x Delta_n in a_n
Lambda for all n subset m}.
Proof. (F1) a_n is a non-zero-divisor on Lambda and on O[S_{m'}] for m' subset m: if u has order e then
(pi - u) sum_{j<e} pi^(e-1-j) u^j = pi^e - 1, a non-zero integer. (F2) For r in m, m' = m - r, Lambda' = O[S_m']:
Lambda = Lambda'[C_r]; the kernel of 1 - c_r is N_r Lambda; Lambda/(1 - c_r) = Lambda'; and Lambda/N_r Lambda =
O'[S_m'] with O' = O[C_r]/(N_r), which is free over O, so of the same kind (Gamma' = image of Gamma x C_r).
I_m subset I_m^#: N_p (1 - c_p) = 0, so a_k N_{m - k} Delta_n = 0 unless n subset k, and then it is in a_n Lambda.
I_m^# subset I_m by induction on |m| for all O at once (m empty: both are O). Let x in I_m^#, r in m.
Write abar for the image of a under c_r -> 1 (Lambda -> Lambda'); a_r = abar_r has no c_r.
(1) The condition for n = {r}: x (1 - c_r) = a_r z. Modulo 1 - c_r: a_r zbar = 0 in Lambda', so
    z = (1 - c_r) y by (F1); then (x - a_r y)(1 - c_r) = 0, so x = a_r y + N_r w with w in Lambda'.
(2) For n subset m', the condition for n + r: x Delta_n (1 - c_r) = a_r y Delta_n (1 - c_r) lies in
    a_n a_r Lambda, so y Delta_n (1 - c_r) = a_n z_n (a_r is a non-zero-divisor), and as in (1) there is t_n
    with y Delta_n - a_n t_n in N_r Lambda. So the image of y in Lambda/N_r Lambda = O'[S_m'] is in the #-ideal
    for (O', m'), which by induction is the I-ideal: y = y_1 + N_r y_2 with y_1 in sum_{n subset m'} a_n
    N_{m' - n} Lambda. Then a_r y_1 is in I_m, and x - a_r y_1 = N_r w_1 with w_1 in Lambda'.
(3) N_r w_1 = x - a_r y_1 is in I_m^#. For n subset m': N_r w_1 Delta_n = a_n z; then (1 - c_r) a_n z = 0, so
    z = N_r z' with z' in Lambda'; and N_r a_n = N_r abar_n. So N_r (w_1 Delta_n - abar_n z') = 0, i.e.
    w_1 Delta_n = abar_n z' in Lambda': w_1 is in the #-ideal for (O, m') with the elements ubar_p, hence
    in sum_{n subset m'} abar_n N_{m' - n} Lambda', and N_r w_1 = sum a_n N_{m - n} (...) is in I_m. QED

### 5.4 Lemma KL (invariant elements have full augmentation)
**Lemma KL.** Let C_0 be a finite abelian group, G = C_0 x S_m with cyclic C_p, |C_p| dividing p - 1, and
u_p in C_0 x S_{m - p} (p in m). Let I = sum_{n subset m} a_n N_{m - n} Z_(2)[G]. If N_0 w is in I for some
w in Z_(2)[S_m] (N_0 = sum of the elements of C_0), then eps(w) = 0 mod |S_m|.
Proof. <x,y> = sum_g x_g y_g = coefficient of 1 in x^* y (^* : g -> g^(-1)). A prime ' denotes the image
under the ring map pi: Q[G] -> Q[S_m], C_0 -> 1. Let gamma_n = prod_{p in n} (p - u_p^(-1))^(-1) (1 - c_p^(-1)),
so gamma_n^* = Delta_n / a_n, and J' = sum_n gamma_n' Z_(2)[S_m].
(i) <x, gamma l> = <x gamma^*, l>, so the dual lattice of J' is {x : x (gamma_n')^* in Z_(2)[S_m] for all n}
    = {x in Z_(2)[S_m] : x Delta_n in a_n' Z_(2)[S_m]} = I'^# = I' (Lemma D with O = Z_(2), Gamma = 1).
    Both are lattices of full rank, so J' is the dual lattice of I'.
(ii) e = N_m/|S_m| is in the dual of I': <e,x> = eps(x)/|S_m|, and eps(a_n' N_{m-n}) = prod_{p in n}(p-1)
    prod_{p not in n} |C_p| is divisible by |S_m|. So e = sum_n gamma_n' l_n with l_n in Z_(2)[S_m].
(iii) xi := sum_n gamma_n l_n in Q[G] has pi(xi) = e, and <xi, I> subset Z_(2): for subsets n, k of m,
    gamma_n^* a_k N_{m - k} = Delta_n N_{m - k} a_k/a_n is 0 unless n subset k, and then lies in Z_(2)[G].
(iv) Z_(2) contains <xi, N_0 w> = sum_{(c,y) in C_0 x S_m} xi(c,y) w(y) = <pi(xi), w> = <e, w> = eps(w)/|S_m|. QED

### 5.5 Proof of Theorem A
Fix p_0 in P, m = P - p_0, C_0 = C_{p_0}, s_0, k_0. Split (M) according to p_0 in n or not:
    N_0 Z + (p_0 - u_0) B = 0,   Z = sum_{non-empty n subset m} a_n' N_{m - n} g_n  in Z_(2)[S_m],
                                 B = sum_{n subset m} a_n N_{m - n} g_{n + p_0}      in Z_(2)[S_P]
(N_0 a_n = N_0 a_n'; u_0 lies in S_m). p_0 - u_0 is a non-zero-divisor, so (1 - c)(p_0 - u_0)B = 0 for c in
C_0 gives (1 - c)B = 0: B = N_0 w with w in Z_(2)[S_m], and then Z = -(p_0 - u_0) w. Taking eps:
    2^(s_m) ell = eps(Z) = -(p_0 - 1) eps(w),   ell := sum_{non-empty n subset m} o(n) eps(g_n)
                                                     = sum_{r != 0, p_0^(k_0) | r} f(r)
(eps(a_n' N_{m-n}) = phi(n) 2^(s_{m-n}); o(n) eps(g_n) is the sum of f over n(r) = n; p_0 not in n(r) iff
p_0^(k_0) | r). By Lemma 1, g_{n+p_0} = nu(n + p_0) N_0 N_n + 2 e_n, and a_n N_{m-n} N_0 N_n = phi(n) N_P, so
    B = c_0 N_P + 2 B_e,  c_0 = k_0 prod_{p in m} (1 + (p-1)k_p) = k_0 mod 2,  B_e = sum_n a_n N_{m-n} e_n in I.
Comparing coefficients in B = N_0 w: w = c_0 N_m + 2 w_e with w_e in Z_(2)[S_m] and N_0 w_e = B_e in I.
Lemma KL (|C_p| = 2^(s_p) divides p - 1): eps(w_e) = 0 mod 2^(s_m). Hence eps(w) = k_0 2^(s_m) mod 2^(s_m + 1)
and ell = -(p_0 - 1) eps(w)/2^(s_m) = (p_0 - 1) k_0 mod 2^(s_0 + 1). QED

### 5.6 Proof of Theorem B
Multiply (b) by p - 1 (f(q) = f(0) = 0):  sum_{v_p(r) < k} (p-1) v_p(r) f(r) + ((p-1)k + 1) ell = 0.
Since f(r) = 1 mod 2, (p-1) v_p(r) f(r) = (p-1) v_p(r) mod 2^(s+1); the number of r with v_p(r) = j (1 <= j < k)
is (q/p^k) p^(k-j-1) (p-1); and (p-1)^2 = 0 mod 2^(s+1). So the first sum is 0 mod 2^(s+1), and (p-1)k + 1
is odd: ell = 0 mod 2^(s+1). QED

## 6. Where the hypotheses enter; known cases; squares

6.1 "Not a square" is exactly "some k_p is odd", the only thing used. "q = 1 mod 4" does not enter the
Theorem. It only decides whether condition (b) (the log p coefficients) is needed: [C, for all odd q <= 20000
that are not prime powers and have small systems; not proved beyond two primes] condition (a) alone has no
odd-valued solution iff the number of p | q with v_2(p-1) minimal and k_p odd is odd. That holds for every
q = 3 mod 4 (the minimum is 1 and the count is odd), which is presumably the mechanism behind Murty-Saradha
2010 (not read). For q = 1 mod 4 with a prime factor = 3 mod 4 (e.g. 21, 105, 165) condition (a) HAS odd-valued
solutions; the new input is Theorem A: for them the coefficient of log p cannot vanish. (The second report
quotes Bharadwaj asking whether +-1 functions with value in the Q-span of the log p exist; Theorem A shows
that for such a function no c_p with k_p odd vanishes.) "Not a prime power" is not needed either:
for q = p^k, g(a) = sum_{j<k} f(a p^j)/p^j is a sum of k odd numbers, so k is even.

6.2 Known cases. The Theorem contains q = 3 mod 4 and all prime powers p^k with k odd. It does NOT
contain Okada's condition 2 phi(q)+1 > q for squares (9, 25, 225, 441, ...): that is a size argument.

6.3 Squares: the 2-adic method must fail [P, N]. For an odd square q put, for r != 0, N = q/gcd(r,q) and
    f(r) = (-1)^Omega(N) (rad N / N) theta(r),  theta(r) = Legendre symbol (r/gcd(r,q) | p) if N is a power
    of a single prime p, theta(r) = 1 otherwise;  f(0) = 0.
All values are +-1/d with d odd, and sum f(n)/n = 0: verified with 70-digit arithmetic for q = 9, 25, 49, 81,
225, 441, 1225, 2025, 11025 (|sum| < 3e-72; `squares`). Proof: f depends only on (N(r), cl(r)), so g(a)
depends only on the class of a and Lemma 2's computation gives g(a) = sum_n [D_n^(-1) g_n](x_n) up to an odd
factor; here g_n = (sum over exponents j_p = 1..k_p of (-1)^(sum j_p)) theta_n = 0 because every k_p is even:
(a) holds. For (b): the sum of f over N(r) = N is 0 if N is a prime power (a full character sum) and
(-1)^Omega(N) phi(rad N) otherwise, and c_p = sum_N lam_p(N) (that sum) vanishes because for each set n of at
least two primes the alternating sum over the exponent of a prime of n other than p is 0.
These values are units at every prime not dividing q, so no congruence argument modulo such a prime can
settle squares; one needs |f| = 1 (as Okada and Chatterjee-Murty do) or information at the primes dividing q.
Status of squares: 225 and 441 are true by Okada's condition; 11025 = 105^2 and 27225 = 165^2 are covered by
nothing in the reports and not by this note.

## 7. Comparison with the known results listed in the reports (`known 30000`) [C]

Encoded as stated by the helpers: q prime; 2 phi(q)+1 > q (Okada); q = 3 mod 4 (Murty-Saradha);
sum_{d | q, d >= 3} 1/phi(d) < 1 (Chatterjee-Murty Prop 3.1); least prime factor >= d(q) (their Cor 3.3);
q = pN, N = 3 mod 4 squarefree, p > 2^omega(N) prod_{l | N} ((l+1)^2+1) (Bharadwaj Cor 1; adds nothing below
37000 beyond products of two primes). Not encodable: the 82 percent density statement and Bharadwaj's
Theorem 2 (needs "Property U").
Composite q = 1 mod 4 up to 30000: 5888; covered by a listed result: 5711; not covered and not a square
(new by the Theorem): 175; not covered and square (open): 11025, 27225.
First twenty new q: 105, 165, 525, 585, 825, 945, 1365, 1485, 1785, 2145, 2205, 2625, 2805, 2925, 3045,
3465, 3705, 3885, 4125, 4305. (The first six agree with both helpers' lists.)
Is the class "non-square" a known theorem in disguise? Not any of the listed ones: each of these q fails
every listed condition, and the Theorem is uniform in q, which the reports say the printed methods are not
(Chatterjee-Murty: their inequality fails on a set of positive density).

## 8. Doubts, and what is not checked

1. Papers not read. The criterion is derived here and agrees with the helpers' transcription; my derivation
   uses the homogeneous qualitative Baker theorem for logarithms of -1, sin(pi j/q) and primes.
2. Novelty not verified, and this is the main doubt about "new": a theorem this short for a case the
   specialists call open is suspicious. Not seen by me or the helpers: Murty-Saradha 2010, Murty-Pathak 2022
   ("Okada space", an explicit basis: the description at the end of section 1 may well be theirs),
   Bharadwaj-Murty-Pathak 2025, Okada 1986, Saradha-Tijdeman 2003, Tijdeman 2002/2008. The reports say Chatterjee-Murty 2015,
   Pathak 2019 and Bharadwaj 2022 call q = 1 mod 4 open, and that a parity argument is in print only for
   the coefficient of log 2 (even period). Theorem A is the analogue for odd p; it needs all character
   equations at once (Lemma KL), which fits the helpers' remark that printed proofs use one equation.
3. The proof has not been read by anyone else and is not formalized. Mitigation: every step was tested
   separately (section 3), the final statement was confirmed by a method that uses none of the lemmas
   (method A, q <= 2100), and squares behave as predicted (6.3). The natural next step is a Lean proof of
   Lemma D, Lemma KL and Theorems A, B (pure algebra over Z_(2)), with the criterion as a hypothesis.
4. Not proved: the "(a) alone" classification in 6.1 for three or more primes (computed only; not needed).
5. Method A needs D0 <= 63 (true for all q tested; the program stops otherwise). Method B skips systems
   with more than 1500 unknowns unless asked.
6. Numerical tests of the criterion cannot exclude vanishing functions of very large height; that
   direction rests on Baker's theorem.
