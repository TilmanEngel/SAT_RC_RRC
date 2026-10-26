from sage.all import *
P = polytopes.icosidodecahedron()

V = P.vertices()
H = [h for h in P.Hrepresentation() if h.is_inequality()]

K = P.base_ring()

S = matrix(K, len(V), len(H))

for i, v in enumerate(V):
    x = vector(K, v.vector())
    for j, h in enumerate(H):
        S[i, j] = h.A() * x + h.b()

import csv
from itertools import combinations

m = S.nrows()
n = S.ncols()

k = 0
l = 0

with open("positive_det_pairs.csv", "w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["i1", "i2", "j1", "j2"])

    for i, i1 in combinations(range(m), 2):
        for j, j1 in combinations(range(n), 2):
            k += 1

            a = S[i, j]
            b = S[i, j1]
            c = S[i1, j]
            d = S[i1, j1]

            # skipping trivial cases
            if a == 0 or b == 0 or c == 0 or d == 0:
                continue
            # calculating the determinant
            det = a * d - b * c
            # deciding for which pair the condition is active
            if det > 0:
                l += 1
                writer.writerow([i, i1, j, j1])
            elif det < 0:
                l += 1
                writer.writerow([i1, i, j, j1])
print("Number of checked 2x2 matrices: ", k)
print("Number of 2x2 matrices with non zero determinant: ", l)
