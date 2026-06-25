# A small script to generate new data files for LMFDB processing
# Initialises everything with Nones (\N)

# Number of transitive permutation groups of degree n (OEIS A002106),
# equivalently NumberOfTransitiveGroups(n) in Magma. Degree 32 omitted for now.
num_transitive = {
    1: 1,  2: 1,  3: 2,  4: 5,  5: 5,  6: 16,  7: 7,  8: 50,
    9: 34, 10: 45, 11: 8, 12: 301, 13: 9, 14: 63, 15: 104,
    16: 1954, 17: 10, 18: 983, 19: 8, 20: 1117, 21: 164,
    22: 59, 23: 7, 24: 25000, 25: 211, 26: 96, 27: 2392,
    28: 1854, 29: 8, 30: 5712, 31: 12, 33: 162, 34: 115,
    35: 407, 36: 121279, 37: 11, 38: 76, 39: 306, 40: 315842,
    41: 10, 42: 9491, 43: 10, 44: 2113, 45: 10923, 46: 56, 47: 6,
}

header = ("label|malle_b|malle_turkelli_b|malle_wang_b|malle_b_status|"
          "malle_b_prp|malle_turkelli_b_prp|malle_wang_b_prp|malle_b_status_prp")
types  = "text|" + "|".join(["smallint"] * 8)
null_row = "|".join([r"\N"] * 8)   # the 8 data columns

for n, count in num_transitive.items():
    with open(f"degree{n}.txt", "w") as f:
        f.write(header + "\n")
        f.write(types + "\n\n")
        for k in range(1, count + 1):
            f.write(f"{n}T{k}|{null_row}\n")
