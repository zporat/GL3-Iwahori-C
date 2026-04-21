// hecke_matrices.m
// Version 1.0
// April 2026

// Zachary Porat

/* 
================================================================================
FUNCTION: mod_abs_value

INPUT: 
# int: an integer x
# modulus: a modulus m

GOAL:
Ensure |x| <= 1/2 |m| as needed in vGvdKTV reduction algorithm. 
================================================================================
*/
function mod_abs_value(int, modulus)
    Zm := Integers(modulus);
    value := Zm!int;
    if Integers()!value le ( modulus / 2 ) then
        return Integers()!value;
    else
        return ( Integers()!value - modulus );
    end if;
end function;

/* 
================================================================================
FUNCTION: modform_reduction

INPUT: 
# mod_symbol: a 3x3 modular symbol (matrix)

GOAL:
Reduce mod_symbol to a collection of unimodular symbols whose sum is mod_symbol.
================================================================================
*/
function modform_reduction(mod_symbol)
// -----------------------------------------------------------------------------
// Establishing default information about the modular symbol to be reduced.
// -----------------------------------------------------------------------------
    nonzero_det_symbols := [];
    
    Q_T := Transpose(mod_symbol);
    Q_T_ref := EchelonForm(Q_T);
    Q_cef := Transpose(Q_T_ref);
    
    m1 := Q_cef[1, 1];
    m2 := Q_cef[2, 2];
    m3 := Q_cef[3, 3];
    
    a := Q_cef[2, 1];
    b := Q_cef[3, 1];
    c := Q_cef[3, 2];
    
// -----------------------------------------------------------------------------
// Case 1: m = m1
// -----------------------------------------------------------------------------
    if (m1 ne 1) and (m1 ne -1) then
        m := m1;
        x := [1, 0, 0];
    
// -----------------------------------------------------------------------------
// Case 2: m = m2
// -----------------------------------------------------------------------------
    elif (m2 ne 1) and (m2 ne -1) then
        m := m2;
        if m1 eq 1 then
            x := [mod_abs_value(-a, m), 1, 0];
        elif m1 eq -1 then
            x := [mod_abs_value(a, m), 1, 0];
        end if;

// -----------------------------------------------------------------------------
// Case 3: m = m3
// -----------------------------------------------------------------------------
    elif (m3 ne 1) and (m3 ne -1) then
        m := m3;
        if m1 eq 1 and m2 eq 1 then
            x := [mod_abs_value(a*c - b, m), mod_abs_value(-c, m), 1];
        elif m1 eq 1 and m2 eq -1 then
            x := [mod_abs_value(-a*c - b, m), mod_abs_value(c, m), 1];
        elif m1 eq -1 and m2 eq 1 then
            x := [mod_abs_value(-a*c + b, m), mod_abs_value(-c, m), 1];
        elif m1 eq -1 and m2 eq -1 then
            x := [mod_abs_value(a*c + b, m), mod_abs_value(c, m), 1];
        end if;
    end if;
    
// -----------------------------------------------------------------------------
// Building the vector v. 
// -----------------------------------------------------------------------------
    x1 := x[1];
    x2 := x[2];
    x3 := x[3];
    
    t1 := x1/m;
    t2 := x2/m;
    t3 := x3/m;
    
    q1 := mod_symbol[1];
    q2 := mod_symbol[2];
    q3 := mod_symbol[3];
    
    v1 := t1*Vector(Rationals(), q1);
    v2 := t2*Vector(Rationals(), q2);
    v3 := t3*Vector(Rationals(), q3);
    
    v := v1 + v2 + v3;

// -----------------------------------------------------------------------------
// Determining which modular symbols to return after the reduction is complete.
// -----------------------------------------------------------------------------
    Q1 := Matrix(Integers(), [Eltseq(v), Eltseq(q2), Eltseq(q3)]);
    Q2 := Matrix(Integers(), [Eltseq(q1), Eltseq(v), Eltseq(q3)]);
    Q3 := Matrix(Integers(), [Eltseq(q1), Eltseq(q2), Eltseq(v)]);
    
    for test_matrix in [Q1, Q2, Q3] do
        if Determinant(test_matrix) ne 0 then
            Append(~nonzero_det_symbols, test_matrix);
        end if;
    end for;
    
    return nonzero_det_symbols;
end function;

/*
================================================================================
FUNCTION: BuildHeckeMatrices

INPUT: 
# l: a rational prime

GOAL:
Take a collection of single coset representatives for diag(l, 1, 1) and 
diag(l, l, 1) and reduce to a collection of unimodular symbols. 
================================================================================
*/
function BuildHeckeMatrices(l)   
// -----------------------------------------------------------------------------
// Builds a list of single coset representatives for matrix diag(l, 1, 1).
// -----------------------------------------------------------------------------
    Reps_E := [];
    for i in [0..l-1] do
        for j in [0..l-1] do
            v1 := [1, 0, 0];
            v2 := [0, 1, 0];
            v3 := [i, j, l];
            Bi := Transpose(Matrix(Integers(), [v1, v2, v3]));
            Append(~Reps_E, Bi);
        end for;
    end for;

    for k in [0..l-1] do
        v1 := [1, 0, 0];
        v2 := [k, l, 0];
        v3 := [0, 0, 1];
        Bi := Transpose(Matrix(Integers(), [v1, v2, v3]));
        Append(~Reps_E, Bi);
    end for;

    v1 := [l, 0, 0];
    v2 := [0, 1, 0];
    v3 := [0, 0, 1];
    Bi := Transpose(Matrix(Integers(), [v1, v2, v3]));
    Append(~Reps_E, Bi);

// -----------------------------------------------------------------------------
// Builds a list of single coset representatives for matrix diag(l, l, 1).
// -----------------------------------------------------------------------------
    Reps_F := [];
    for i in [0..l-1] do   
        for j in [0..l-1] do   
            v1 := [1, 0, 0];
            v2 := [i, l, 0];
            v3 := [j, 0, l];
            Bi := Transpose(Matrix(Integers(), [v1, v2, v3]));
            Append(~Reps_F, Bi);
        end for;
    end for;

    for c in [0..l-1] do 
        v1 := [l, 0, 0];
        v2 := [0, 1, 0];
        v3 := [0, c, l];
        Bi := Transpose(Matrix(Integers(), [v1, v2, v3]));
        Append(~Reps_F, Bi);
    end for;

    v1 := [l, 0, 0];
    v2 := [0, l, 0];
    v3 := [0, 0, 1];
    Bi := Transpose(Matrix(Integers(), [v1, v2, v3]));
    Append(~Reps_F, Bi);

// -----------------------------------------------------------------------------
// For each represenative in Reps_E, computes a collection of unimodular symbols 
// M_ij such that [B_i^-1] = SUM [M_ij].
// -----------------------------------------------------------------------------
    E_Unis := [];
    for B_i in Reps_E do
        Rational_Mat := Matrix(Rationals(), B_i);
        symbol_to_reduce := (Rational_Mat)^(-1);

// -----------------------------------------------------------------------------
// Ensures that the modular symbol being reduced has integer entries as required 
// by the reduction algorithm. 
// -----------------------------------------------------------------------------
        for i in [1..NumberOfRows(symbol_to_reduce)] do
            row := symbol_to_reduce[i];
            row_denoms := [];
            for j in [1..NumberOfColumns(symbol_to_reduce)] do
                Append(~row_denoms, Denominator(row[j]));
            end for;
            row_multiple := LCM(row_denoms[1], LCM(row_denoms[2], row_denoms[3]));
            for k in [1..NumberOfColumns(symbol_to_reduce)] do
                row_entry := row[k]*row_multiple;
                symbol_to_reduce[i, k] := row_entry;
            end for;
        end for;

        symbol_to_reduce := ChangeRing(symbol_to_reduce, Integers());

// -----------------------------------------------------------------------------
// Performs the reduction algorithm.
// -----------------------------------------------------------------------------
        if Determinant(symbol_to_reduce) eq 1 then
            M_jk_List := [symbol_to_reduce];
        elif Determinant(symbol_to_reduce) eq -1 then
            sign_swap_matrix := Matrix(Integers(), 3, [-1, 0, 0, 0, 1, 0, 0, 0, 1])*symbol_to_reduce;
            M_jk_List := [sign_swap_matrix];
        else
            M_jk_List := [];
            starting_list := modform_reduction(symbol_to_reduce);
            working_symbols := starting_list;

            while #starting_list ne 0 do
                for test_matrix in starting_list do
                    if Determinant(test_matrix) eq 1 then
                        Append(~M_jk_List, test_matrix);
                        index_to_remove := Index(working_symbols, test_matrix);
                        Remove(~working_symbols, index_to_remove);
                    elif Determinant(test_matrix) eq -1 then
                        index_to_remove := Index(working_symbols, test_matrix);
                        Remove(~working_symbols, index_to_remove);
                        sign_swap_matrix := Matrix(Integers(), 3, [-1, 0, 0, 0, 1, 0, 0, 0, 1])*test_matrix;
                        Append(~M_jk_List, sign_swap_matrix);
                    else
                        output := modform_reduction(test_matrix);
                        index_to_replace := Index(working_symbols, test_matrix);
                        working_symbols := working_symbols[1..index_to_replace-1] cat output cat working_symbols[index_to_replace+1..#working_symbols];
                    end if;
                end for;
                starting_list := working_symbols;
            end while;
        end if;

// -----------------------------------------------------------------------------
// Writes the output to a list. 
// -----------------------------------------------------------------------------
        output_E := [];
        for M_jk in M_jk_List do 
            Append(~output_E, M_jk*B_i);
        end for;

        Append(~E_Unis, output_E);

    end for;

// -----------------------------------------------------------------------------
// For each represenative in Reps_F, computes a collection of unimodular symbols 
// M_ij such that [B_i^-1] = SUM [M_ij].
// -----------------------------------------------------------------------------
    F_Unis := [];
    for B_i in Reps_F do
        Rational_Mat := Matrix(Rationals(), B_i);
        symbol_to_reduce := (Rational_Mat)^(-1);

// -----------------------------------------------------------------------------
// Ensures that the modular symbol being reduced has integer entries as required 
// by the reduction algorithm. 
// -----------------------------------------------------------------------------
        for i in [1..NumberOfRows(symbol_to_reduce)] do
            row := symbol_to_reduce[i];
            row_denoms := [];
            for j in [1..NumberOfColumns(symbol_to_reduce)] do
                Append(~row_denoms, Denominator(row[j]));
            end for;
            row_multiple := LCM(row_denoms[1], LCM(row_denoms[2], row_denoms[3]));
            for k in [1..NumberOfColumns(symbol_to_reduce)] do
                row_entry := row[k]*row_multiple;
                symbol_to_reduce[i, k] := row_entry;
            end for;
        end for;

        symbol_to_reduce := ChangeRing(symbol_to_reduce, Integers());

// -----------------------------------------------------------------------------
// Performs the reduction algorithm.
// -----------------------------------------------------------------------------
        if Determinant(symbol_to_reduce) eq 1 then
            M_jk_List := [symbol_to_reduce];
        elif Determinant(symbol_to_reduce) eq -1 then
            sign_swap_matrix := Matrix(Integers(), 3, [-1, 0, 0, 0, 1, 0, 0, 0, 1])*symbol_to_reduce;
            M_jk_List := [sign_swap_matrix];
        else
            M_jk_List := [];
            starting_list := modform_reduction(symbol_to_reduce);
            working_symbols := starting_list;

            while #starting_list ne 0 do
                for test_matrix in starting_list do
                    if Determinant(test_matrix) eq 1 then
                        Append(~M_jk_List, test_matrix);
                        index_to_remove := Index(working_symbols, test_matrix);
                        Remove(~working_symbols, index_to_remove);
                    elif Determinant(test_matrix) eq -1 then
                        index_to_remove := Index(working_symbols, test_matrix);
                        Remove(~working_symbols, index_to_remove);
                        sign_swap_matrix := Matrix(Integers(), 3, [-1, 0, 0, 0, 1, 0, 0, 0, 1])*test_matrix;
                        Append(~M_jk_List, sign_swap_matrix);
                    else
                        output := modform_reduction(test_matrix);
                        index_to_replace := Index(working_symbols, test_matrix);
                        working_symbols := working_symbols[1..index_to_replace-1] cat output cat working_symbols[index_to_replace+1..#working_symbols];
                    end if;
                end for;
                starting_list := working_symbols;
            end while;
        end if;

// -----------------------------------------------------------------------------
// Writes the output to a list. 
// -----------------------------------------------------------------------------
        output_F := [];
        for M_jk in M_jk_List do 
            Append(~output_F, M_jk*B_i);
        end for;

        Append(~F_Unis, output_F);

    end for;
    
return Flat(E_Unis), Flat(F_Unis);
end function;