from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical153
from sympy import cos, pi, Matrix, simplify
import math
from itertools import combinations
import csv
#parameter to choose, what type of nonnegative matrix to compute
matrix = 'ngon'
rrc = True
if matrix == 'corr':
    m = 5
    t = 24

    n = 2 ** m

    M = [[(i // (2 ** (m - j - 1))) % 2 for j in range(m)] for i in range(n)]

    A = [[(1 - sum(M[n - i - 1][k] * M[n - j - 1][k] for k in range(m))) ** 2 for j in range(n)] for i in range(n)]

    B = [[int(A[i][j] > 0) for j in range(n)] for i in range(n)]

elif matrix == 'ngon':
    #Number of vertices
    n = 19
    #xc to check
    t = 8
    # initialize Slack matrix (fp)
    A = [[0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for l in range(int((n + 1) / 2)):
            A[i][(i + l) % n] = math.cos(math.pi / n) - math.cos(math.pi / n * (2 * l + 1))
            A[i][(i - 1 - l) % n] = math.cos(math.pi / n) - math.cos(math.pi / n * (2 * l + 1))
    if rrc:
        #initialize exact Slack matrix
        Aex = [[0 for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for l in range(int((n+1)/2)):
                value = cos(pi/n)-cos(pi/n*(2*l+1))
                Aex[i][(i+l)%n] = value
                Aex[i][(i-1-l)%n] = value
        Aex = Matrix(Aex)
        positive_det_pairs = []
        with open(f"positive_det_pairs_n{n}.csv", "r", newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                positive_det_pairs.append(tuple(int(row[key]) for key in ("i1", "i2", "j1", "j2")))
        print("Anzahl der Paare:", len(positive_det_pairs))
        print(positive_det_pairs[:10])
    else:
        Aint = [[0 for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for l in range(int((n+1)/2)):
                Aint[i][(i+l)%n] = l
                Aint[i][(i-1-l)%n] = l
elif matrix == 'ledm':
    n = 18
    t = 7
    A = [[(i-j)*(i-j) for j in range(n)] for i in range(n)]

B = [[1 if A[i][j] > 0 else 0 for j in range(n)] for i in range(n)]

# management of variables

vpool = IDPool()
#row and column indices u and v from notes
def U(i,k):
    return vpool.id(f"u_{i}_{k}")
def V(j,k):
    return vpool.id(f"v_{j}_{k}")
#support variables x from notes
def X(i,j,k):
    return vpool.id(f"x_{i}_{j}_{k}")
#lexicographic a from notes
def ALEX(i,k):
    return vpool.id(f"a_{i}_{k}")

#object to gather the conditions in
cnf = CNF()

#some logical functions used later
#not used often, but more readable
# x <-> (a AND b)
def equiv_and(cnf, x, a, b):
    # x -> a
    cnf.append([-x, a])
    # x -> b
    cnf.append([-x, b])
    # (a AND b) -> x
    cnf.append([x, -a, -b])
# x <-> (a AND NOT b)
def equiv_and_not(cnf, x, a, b):
    # x -> a
    cnf.append([-x, a])
    # x -> not b
    cnf.append([-x, -b])
    # (a AND NOT b) -> x
    cnf.append([x, -a, b])
# ============================================================
# CONSTRAINT 1a: maximal rectangles and redundant condition
# v[j,k] <-> forall(i)(not u[i,k] \/ B[i,j])
# Equivalent:
# v[j,k] <-> AND_i( not u[i,k] \/ B[i,j] )
# ============================================================
for j in range(n):
    for k in range(t):
        lits = []
        for i in range(n):
            if B[i][j] == 1:
                # (not u OR 1) = true
                continue
            else:
                # (not u OR 0) = not u
                lits.append(-U(i,k))
        # If all clauses are trivially true
        if len(lits) == 0:
            # force v[j,k] = true
            cnf.append([V(j,k)])
        else:
            # v -> all literals
            for lit in lits:
                cnf.append([-V(j,k), lit])
            # all literals -> v
            cnf.append([V(j,k)] + [-lit for lit in lits])
# ============================================================
# CONSTRAINT 1b: maximal rectangles and redundant condition
# u[i,k] <-> forall(j)(not v[j,k] \/ B[i,j])
# Equivalent:
# u[i,k] <-> AND_j( not v[j,k] \/ B[i,j] )
# ============================================================
for i in range(n):
    for k in range(t):
        lits = []
        for j in range(n):
            if B[i][j] == 1:
                # (not v OR 1) = true
                continue
            else:
                # (not v OR 0) = not v
                lits.append(-V(j,k))
        # all clauses trivially true
        if len(lits) == 0:
            # force u[i,k] = true
            cnf.append([U(i,k)])
        else:
            # u -> all literals
            for lit in lits:
                cnf.append([-U(i,k), lit])
            # all literals -> u
            cnf.append([U(i,k)] + [-lit for lit in lits])
# ============================================================
# CONSTRAINT 2: definition of support variable
# x[i,j,k] <-> (u[i,k] /\ v[j,k])
# ============================================================
for i in range(n):
    for j in range(n):
        for k in range(t):
            equiv_and(cnf,X(i,j,k),U(i,k),V(j,k))
# ============================================================
# CONSTRAINT 3: every element has to be covered
# If A[i,j] > 0:
# exists(k)(x[i,j,k])
# ============================================================
for i in range(n):
    for j in range(n):
        if A[i][j] > 0:
            cnf.append([X(i,j,k) for k in range(t)])
# ============================================================
# CONSTRAINT 4: zero elements can not be covered
# If A[i,j] == 0:
# not x[i,j,k]
# ============================================================
for i in range(n):
    for j in range(n):
        for k in range(t):
            if A[i][j] == 0:
                cnf.append([-X(i,j,k)])
# ============================================================
# CONSTRAINT 5: two element fooling sets
# forall(
#   i < i1,
#   j != j1,
#   (B[i][j1] == 0 OR B[i1][j] == 0)
# ):
#   not x[i,j,k] OR not x[i1,j1,k]
# ============================================================
for i, i1 in combinations(range(n), 2):
    for j, j1 in combinations(range(n), 2):
        # filtering condition from MiniZinc
        if B[i][j1] == 0 or B[i1][j] == 0:
            for k in range(t):
                cnf.append([-X(i, j, k),-X(i1, j1, k)])
# ============================================================
# REFINED RECTANGLE CONSTRAINT 6
#
# forall(k_remove)(
#     exists(k != k_remove)(
#         x[i,j,k] OR x[i1,j1,k]
#     )
# )
# ============================================================
if rrc:
    if matrix=='ngon':
        for (i, i1, j, j1) in positive_det_pairs:
            for k_remove in range(t):
                clause = []
                for k in range(t):
                    if k == k_remove:
                        continue
                    clause.append(X(i, j, k))
                    clause.append(X(i1, j1, k))
                cnf.append(clause)
    else:
        #for rational entries, we can check the condition directly
        for i, i1 in combinations(range(n), 2):
            for j, j1 in combinations(range(n), 2):
                        if (B[i][j] == 0 or B[i1][j1] == 0 or B[i1][j] == 0 or B[i][j1] == 0):
                            continue
                        if A[i][j] * A[i1][j1] - A[i][j1] * A[i1][j] > 0:
                            for k_remove in range(t):
                                clause = []
                                for k in range(t):
                                    if k == k_remove:
                                        continue
                                    clause.append(X(i, j, k))
                                    clause.append(X(i1, j1, k))
                                cnf.append(clause)
                        elif A[i][j] * A[i1][j1] - A[i][j1] * A[i1][j] < 0:
                            for k_remove in range(t):
                                clause = []
                                for k in range(t):
                                    if k == k_remove:
                                        continue
                                    clause.append(X(i, j1, k))
                                    clause.append(X(i1, j, k))
                                cnf.append(clause)
# ============================================================
# CONSTRAINT 7: definition of lexicographic variables
#
# a[i,k] <-> (u[i,k] /\ not u[i,k+1])
# ============================================================
for i in range(n-1):
    for k in range(0,t-1):
        equiv_and_not(cnf,ALEX(i,k),U(i,k),U(i,k+1))
# ============================================================
# CONSTRAINT 8: lexicographic ordering
#
# exists(j < i)(a[j,k]) OR (u[i,k] OR not u[i,k+1])
# ============================================================
for i in range(n):
    for k in range(0,t-1):
        clause = []
        # exists(j < i)(a[j,k])
        for j in range(i):
            clause.append(ALEX(j,k))
        # (u[i,k] OR not u[i,k+1])
        clause.append(U(i,k))
        clause.append(-U(i,k+1))
        cnf.append(clause)
# ============================================================
# STATS
# ============================================================
#exclude:
print("Variables:", vpool.top)
print("Clauses:", len(cnf.clauses))

# ============================================================
# EXPORT DIMACS
# ============================================================
if rrc:
    r = 'refined_'
else:
    r = ''
cnf.to_file(f"CNF/{r}rectangle_cover_{matrix}_n{n}r{t}.cnf")

print(f"DIMACS written to CNF/refined_rectangle_cover_{matrix}_n{n}r{t}.cnf")

# ============================================================
# SOLVE WITH CADICAL
# ============================================================

with Cadical153(bootstrap_with=cnf) as solver:

    sat = solver.solve()

    print("SAT:", sat)

    if sat:

        model = set(solver.get_model())

        print("\nU MATRIX")
        for i in range(n):
            row = []
            for k in range(t):
                row.append(
                    1 if U(i,k) in model else 0
                )
            print(row)

        print("\nV MATRIX")
        for j in range(n):
            row = []
            for k in range(t):
                row.append(
                    1 if V(j,k) in model else 0
                )
            print(row)