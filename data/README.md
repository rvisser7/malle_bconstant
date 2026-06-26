# Data of $b$-constants

_This folder is work-in-progress_

Data on the computed $b$-constants is given in this folder.

Each file is formatted to be easily uploadable into a PostgreSQL database using [psycodict](https://github.com/roed314/psycodict). The first line always consists of the column headers, the second line is the postgres data type for each corresponding column, and the third line is empty.  The fourth line onwards contains the indecomposables data, given in the same order as the column headers (separated by `|`).

| Column | Type | Description |
| --- | --- | --- |
| label | text | the LMFDB label of the Galois group G |
| malle_b | smallint | Malle's original conjectured $b$ (for discriminant ordering) |
| malle_turkelli_b | smallint | Turkelli's conjectured $b$ (for discriminant ordering) |
| malle_wang_b | smallint | Wang's conjectured $b$ (for discriminant ordering) |
| malle_b_status | smallint | An integer which encodes the following: |
| malle_b_prp | smallint | Malle's original conjectured $b$ (for product of ramified primes ordering) |
| malle_turkelli_b_prp | smallint | Turkelli's conjectured $b$ (for product of ramified primes ordering) |
| malle_wang_b_prp | smallint | Wang's conjectured $b$ (for product of ramified primes ordering) |
| malle_b_status_prp | smallint | An integer which encodes the following:  |       
                                                        
