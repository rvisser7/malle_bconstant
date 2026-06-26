# Data of $b$-constants

_This folder is work-in-progress_

Data on the computed $b$-constants is given in this folder.

There is one file per degree, `degree<n>.txt`,  containing exactly one row for each transitive group of degree $n$ (labels nT1, nT2, etc.) contained in the LMFDB database.

Each file is formatted to be easily uploadable into a PostgreSQL database using [psycodict](https://github.com/roed314/psycodict). The first line always consists of the column headers, the second line is the postgres data type for each corresponding column, and the third line is empty.  The fourth line onwards contains the $b$-constant data, given in the same order as the column headers (separated by `|`).  Data which could not be computed is recorded as `\N` (PostgreSQL null marker).

| Column | Type | Description |
| --- | --- | --- |
| `label` | text | the LMFDB label nTt of the Galois group G |
| `malle_b` | smallint | Malle's original conjectured $b$ (for discriminant ordering) |
| `malle_turkelli_b` | smallint | Turkelli's conjectured $b$ (for discriminant ordering) |
| `malle_wang_b` | smallint | Wang's conjectured $b$ (for discriminant ordering) |
| `malle_b_status` | smallint | An integer which encodes the relationship between the three $b$ above |
| `malle_b_prp` | smallint | Malle's original conjectured $b$ (for product of ramified primes ordering) |
| `malle_turkelli_b_prp` | smallint | Turkelli's conjectured $b$ (for product of ramified primes ordering) |
| `malle_wang_b_prp` | smallint | Wang's conjectured $b$ (for product of ramified primes ordering) |
| `malle_b_status_prp` | smallint | An integer which encodes the relationship between the three $b$ above  |       


For a fixed ordering write $b_M$, $b_W$, $b_T$ for Malle's, Wang's, and Türkelli's constants. These always satisfy $b_M \le b_W \le b_T$, and the status column records which of the inequalities are strict:
 
| Value | Meaning |
| --- | --- |
| `0` | $b_M = b_W = b_T$ |
| `1` | $b_M < b_W = b_T$ |
| `2` | $b_M = b_W < b_T$ |
| `3` | $b_M < b_W < b_T$ |
| `\N` | the relationship could not be determined |
