import csv
from itertools import combinations
from sage.all import *
n = 12
# calculating the regular ngon slack matrix
Aex = matrix(SR, n, n, 0)

for i in range(n):
    for l in range(int((n + 1) / 2)):
        value = cos(pi/n) - cos(pi/n * (2*l + 1))
        Aex[i, (i+l) % n] = value
        Aex[i, (i-1-l) % n] = value

k = 0
count = 0

filename = f"positive_det_pairs_n{n}.csv"

with open(filename, "w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["i1", "i2", "j1", "j2"])

    for i, i1 in combinations(range(n), 2):
        for j, j1 in combinations(range(n), 2):
            k += 1

            a = Aex[i, j]
            b = Aex[i, j1]
            c = Aex[i1, j]
            d = Aex[i1, j1]
            # skipping trivial cases
            if a == 0 or b == 0 or c == 0 or d == 0:
                continue
            # calculating the determinant
            det = a*d - b*c

            # deciding for which pair the condition is active
            if det > 0:
                count += 1
                writer.writerow([i, i1, j, j1])
            elif det < 0:
                count += 1
                writer.writerow([i1, i, j, j1])
print("Number of checked 2x2 matrices: ", k)
print("Number of 2x2 matrices with non zero determinant: ", count)

