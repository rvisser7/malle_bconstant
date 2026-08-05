// =====================================================================
// Permutation index -- DISCRIMINANT ordering
// =====================================================================
//
// Extracted verbatim from compute_all_fast.m. The code below is unchanged
// byte-for-byte, so the split cannot alter any computed value.
//
// Requires (load first): nothing
//
// This is the ONLY file that differs between the two orderings.
// It must define ind(g) before orbits.m is loaded, because MinIndex
// closes over ind at definition time.
// 
// ind(g) = deg - #cycles(g), i.e. the usual discriminant index.

ind := function(g)
    return Degree(Parent(g)) - &+[ c[2] : c in CycleStructure(g) ];
end function;
