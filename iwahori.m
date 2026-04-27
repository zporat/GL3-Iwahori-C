// iwahori.m
// Version 1.0
// April 2026

// Zachary Porat

/* 
================================================================================
PREAMBLE: Loading the packages necessary for this file and defining global 
parameters.  Note, you might need to change the file path, depending on where 
'hecke_matrices.m' lives in your directory. 
================================================================================
*/
load "hecke_matrices.m";
PolyRing<T> := PolynomialRing(Rationals());

/* 
================================================================================
FUNCTION: CanonicalKey

INPUT: 
# gamma: an arbitrary 3x3 matrix to put into canonical form
# p: a rational prime to check level I(3, p)

GOAL:
Standardizes any matrix gamma into a unique pair of vectors <v1, v2>.  
================================================================================
*/
function CanonicalKey(gamma, p)
    V := VectorSpace(GF(p), 3);

    // Normalizes the first column as a vector, corresponding to lines in V.
    v1 := V ! [gamma[1][1], gamma[2][1], gamma[3][1]];
    p1 := 0;
    for i in [1..3] do 
        if v1[i] ne 0 then 
            p1 := i; 
            break; 
        end if; 
    end for;

    if p1 ne 0 then 
        v1 := (v1[p1]^-1) * v1; 
    end if;

    // Normalizes the first and second columns, corresponding to planes in V.
    v2 := V ! [gamma[1][2], gamma[2][2], gamma[3][2]];
    if p1 ne 0 then 
        v2 := v2 - v2[p1]*v1; // Manual Gram-Schmidt
    end if; 

    p2 := 0;
    for i in [1..3] do 
        if v2[i] ne 0 then 
            p2 := i; 
            break; 
        end if; 
    end for;

    if p2 ne 0 then 
        v2 := (v2[p2]^-1) * v2; 
    end if;

    return <v1, v2>;
end function;

/* 
================================================================================
FUNCTION: CanonicalReps

INPUT:
# p: a rational prime to check level I(3, p)

GOAL:
Generates a canonical list of coset representatives for SL(3, Z) / Iwahori(3, p)
using Schubert cells.
================================================================================
*/
function CanonicalReps(p)
    V := VectorSpace(GF(p), 3);
    
    A := [];
    Keys := {@ @};

    // Cell 1: v1=[1,x,y], v2=[0,1,z] (Size: p^3)
    for x, y, z in [0..p-1] do
        Rep := Matrix(GF(p), 3, [1,0,0, x,1,0, y,z,1]);
        Append(~A, Rep);
        Include(~Keys, CanonicalKey(Rep, p));
    end for;

    // Cell 2: v1=[1,x,y], v2=[0,0,1] (Size: p^2)
    for x, y in [0..p-1] do
        Rep := Matrix(GF(p), 3, [1,0,0, x,0,1, y,1,0]);
        Append(~A, Rep);
        Include(~Keys, CanonicalKey(Rep, p));
    end for;

    // Cell 3: v1=[0,1,x], v2=[1,0,0] (Size: p^2)
    for x, y in [0..p-1] do
        Rep := Matrix(GF(p), 3, [0,1,0, 1,0,0, x,y,1]);
        Append(~A, Rep);
        Include(~Keys, CanonicalKey(Rep, p));
    end for;

    // Cell 4: v1=[0,1,x], v2=[0,0,1] (Size: p)
    for x in [0..p-1] do
        Rep := Matrix(GF(p), 3, [0,0,1, 1,0,0, x,1,0]);
        Append(~A, Rep);
        Include(~Keys, CanonicalKey(Rep, p));
    end for;

    // Cell 5: v1=[0,0,1], v2=[1,x,0] (Size: p)
    for x in [0..p-1] do
        Rep := Matrix(GF(p), 3, [0,1,0, 0,x,1, 1,0,0]);
        Append(~A, Rep);
        Include(~Keys, CanonicalKey(Rep, p));
    end for;

    // Cell 6: v1=[0,0,1], v2=[0,1,0] (Size: 1)
    Rep := Matrix(GF(p), 3, [0,0,1, 0,1,0, 1,0,0]);
    Append(~A, Rep);
    Include(~Keys, CanonicalKey(Rep, p));

    N := #A;
    if N ne (1+p)*(1+p+p^2) then 
        error "ERROR: Coset generation incomplete!"; 
    end if;

    return A, Keys;
end function;

/* 
================================================================================
FUNCTION: IwahoriMatrix

INPUT:
# p: a rational prime to check level I(3, p)

GOAL:
Constructs the matrix M, whose kernel is W(I(3, p)).
================================================================================
*/
function IwahoriMatrix(p)
    iwahoriIndex := (1+p) * (1+p+p^2);
    V := VectorSpace(GF(p), 3);
    A, Keys := CanonicalReps(p);

// ----------------------------------------------------------------------------
// Computes the action of h on the coset representatives. 
// ----------------------------------------------------------------------------
    "Now building the h portion of the matrix...";
    h := Matrix(Integers(), 3, [0,-1,0, 1,-1,0, 0,0,1]);
    hList := [];

    for i in [1..iwahoriIndex] do
        target := h * A[i];
        key := CanonicalKey(target, p);
        indx := Index(Keys, key);
        
        if indx eq 0 then 
            error "ERROR: Hash lookup failed!"; 
        end if;

        Append(~hList, <i, indx, 1>);

    end for;

    hMatrix := SparseMatrix(Integers(), iwahoriIndex, iwahoriIndex, hList);

// ----------------------------------------------------------------------------
// Computes the action of sigma1 on the coset representatives.
// ----------------------------------------------------------------------------
    "Now building the sigma1 portion of the matrix...";
    sigma1 := Matrix(Integers(), 3, [0,-1,0, 1,0,0, 0,0,1]);
    sigma1List := [];

    for i in [1..iwahoriIndex] do
        target := sigma1 * A[i];
        key := CanonicalKey(target, p);
        indx := Index(Keys, key);
        
        if indx eq 0 then 
            error "ERROR: Hash lookup failed!"; 
        end if;

        Append(~sigma1List, <i, indx, 1>);

    end for;

    sigma1Matrix := SparseMatrix(Integers(), iwahoriIndex, iwahoriIndex, sigma1List);

// ----------------------------------------------------------------------------
// Computes the action of sigma2 on the coset representatives. 
// ----------------------------------------------------------------------------
    "Now building the sigma2 portion of the matrix...";
    sigma2 := Matrix(Integers(), 3, [0,0,1, 1,0,0, 0,1,0]);
    sigma2List := [];

    for i in [1..iwahoriIndex] do
        target := sigma2 * A[i];
        key := CanonicalKey(target, p);
        indx := Index(Keys, key);
        
        if indx eq 0 then 
            error "ERROR: Hash lookup failed!"; 
        end if;

        Append(~sigma2List, <i, indx, 1>);

    end for;

    sigma2Matrix := SparseMatrix(Integers(), iwahoriIndex, iwahoriIndex, sigma2List);

// ----------------------------------------------------------------------------
// Clears some memory and builds the final matrix. 
// ----------------------------------------------------------------------------
    A := [];
    Keys := {@@};
    hList := [];
    sigma1List := [];
    sigma2List := [];

    "Now building final matrix...";
    I := IdentitySparseMatrix(Integers(), iwahoriIndex);
    M_H := I + hMatrix + hMatrix^2;
    M_Sigma1 := I + sigma1Matrix;
    M_Sigma2 := I - sigma2Matrix;
    M_Kernel := VerticalJoin([M_H, M_Sigma1, M_Sigma2]);

    return M_Kernel;
end function;

/* 
================================================================================
FUNCTION: IwahoriDimension

INPUT:
# p: a rational prime to check level I(3, p)

GOAL:
Computes the dimension of W(I(3, p)) = H_3(I(3, p), C). 
================================================================================
*/
function IwahoriDimension(p)
    iwahoriIndex := (1+p) * (1+p+p^2);
    "Now building matrix...";
    M_Kernel := IwahoriMatrix(p);
    rank := Rank(M_Kernel);
    dim_full := iwahoriIndex - rank;
    dim_cusp := dim_full - (1 + 6*Dimension(CuspForms(Gamma0(p))));
    "Now computing dimension...";
    if p in [53, 61, 79, 89, 223, 521, 953] then
        dim_new := dim_cusp - (Dimension(CuspForms(Gamma0(p))) + 6);
    else 
        dim_new := dim_cusp - Dimension(CuspForms(Gamma0(p)));
    end if;
    output := IntegerToString(p) cat " : " cat IntegerToString(dim_full) cat " : " cat IntegerToString(dim_cusp) cat " : " cat IntegerToString(dim_new); 
    return output;
end function;

/* 
================================================================================
FUNCTION: IwahoriHeckeFull

INPUT:
# p: a rational prime to check level I(3, p)
# l_list: a list of Hecke primes \ell 

GOAL:
Computes the action of Hecke operators E_\ell on H_3(I(3, p), C). 
================================================================================
*/
function IwahoriHeckeFull(p, l_list)
    iwahoriIndex := (1+p) * (1+p+p^2);
    M_Kernel := IwahoriMatrix(p);
    kernelBasis := Transpose(KernelMatrix(Transpose(M_Kernel)));
    A, Keys := CanonicalReps(p);
    EDict := AssociativeArray();

    for l in l_list do
        E_Unis, F_Unis := BuildHeckeMatrices(l);
// ----------------------------------------------------------------------------
// Computes the characteristic polynomial of E_\ell on H_3(I(3, p), C).
// ----------------------------------------------------------------------------
        runningSumE := ZeroMatrix(Integers(), NumberOfRows(kernelBasis), NumberOfColumns(kernelBasis));
        
        "Now computing the action of Hecke operator T(l, 1) for l = " cat IntegerToString(l) cat "...";
        for i in [1..#E_Unis] do
            tempE := Matrix(Integers(), E_Unis[i]);
            row_indicies := [0 : k in [1..iwahoriIndex]]; 
            for j in [1..iwahoriIndex] do
                target := tempE * A[j];
                key := CanonicalKey(target, p);
                indx := Index(Keys, key);
                        
                if indx eq 0 then 
                    error "ERROR: Hash lookup failed!"; 
                end if;

                row_indicies[j] := indx;

            end for;
            
            tempRes := Matrix([ kernelBasis[indx] : indx in row_indicies ]);
            runningSumE := runningSumE + tempRes;
        end for;

        E := Solution(Transpose(kernelBasis), Transpose(runningSumE));
        Char_Poly_E := PolyRing!CharacteristicPolynomial(E);
        EDict[l] := Factorization(Char_Poly_E);
        "The factored characteristic polynomial of T(l, 1) is...";
        Factorization(Char_Poly_E);
    end for;

    return EDict;
end function;

/* 
================================================================================
FUNCTION: IwahoriHeckeNew

INPUT:
# p: a rational prime to check level I(3, p)
# l_list: a list of Hecke primes \ell 
# first_l: the first l in l_list with non-real roots for \varphi_\ell
# K: the splitting field generated by the Hecke eigenvalues 
# f: \varphi_\ell corresponding to first_l

GOAL:
Computes the action of Hecke operators E_\ell on H^3_new(I(3, p), C). 
================================================================================
*/
function IwahoriHeckeNew(p, l_list, first_l, K, f)
    iwahoriIndex := (1+p) * (1+p+p^2);
    M_Kernel := IwahoriMatrix(p);
    kernelBasis := Transpose(KernelMatrix(Transpose(M_Kernel)));
    A, Keys := CanonicalReps(p);
    EDict := AssociativeArray();

    currentBasis := kernelBasis;
    for l in l_list do
        E_Unis, F_Unis := BuildHeckeMatrices(l);
// ----------------------------------------------------------------------------
// Computes the characteristic polynomial of E_\ell on H_3(I(3, p), C).
// ----------------------------------------------------------------------------
        runningSumE := ZeroMatrix(Integers(), iwahoriIndex, NumberOfColumns(currentBasis));
        
        "Now computing the action of Hecke operator T(l, 1) for l = " cat IntegerToString(l) cat "...";
        for i in [1..#E_Unis] do
            tempE := Matrix(Integers(), E_Unis[i]);
            row_indicies := [0 : k in [1..iwahoriIndex]]; 
            for j in [1..iwahoriIndex] do
                target := tempE * A[j];
                key := CanonicalKey(target, p);
                indx := Index(Keys, key);
                        
                if indx eq 0 then 
                    error "ERROR: Hash lookup failed!"; 
                end if;

                row_indicies[j] := indx;

            end for;
            
            tempRes := Matrix([ currentBasis[indx] : indx in row_indicies ]);
            runningSumE := runningSumE + tempRes;
        end for;

        if l eq first_l then
            E := Solution(Transpose(currentBasis), Transpose(runningSumE));
            rationalE := Matrix(Rationals(), E);
            M := Evaluate(f, Transpose(rationalE));
            kerM := KernelMatrix(Transpose(M)); 
            V_T := Matrix(Rationals(), kerM); 
            V := Transpose(kerM);             
            currentBasis := currentBasis * V;    
            runningSumE := runningSumE * V;    
            C := Solution(Transpose(currentBasis), Transpose(runningSumE));
        else
            C := Solution(Transpose(currentBasis), Transpose(runningSumE));
        end if;
                    
        Char_Poly := CharacteristicPolynomial(C);
        K<w> := K;
        extC := Matrix(K, C);

        results := <>;
        for eigenpair in Eigenvalues(extC) do
            lambda := eigenpair[1];
            eigenspace := Eigenspace(extC, lambda);
            eigenbasis := Basis(eigenspace);
            Append(~results, <lambda, eigenbasis[1]>);
        end for;

        if #results eq 1 then
            result_string := Sprintf("%o : %o : %o : %o : NONE : NONE", l, Char_Poly, results[1][2], results[1][1]);
            printf(result_string cat "\n");
        else
            sortedEV := Sort( [ results[1][2], results[2][2] ] );
            if results[1][2] eq sortedEV[1] then
                result_string := Sprintf("%o : %o : %o : %o : %o : %o", l, Char_Poly, "v1", results[1][1], "v2", results[2][1]);
            else 
                result_string := Sprintf("%o : %o : %o : %o : %o : %o", l, Char_Poly, "v1", results[2][1], "v2", results[1][1]);
            end if;
            printf(result_string cat "\n");
        end if;    

        EDict[l] := result_string;       
    end for;

    return EDict;
end function;

// IwahoriHeckeNew(19, [2,3,5], 2, NumberField(T^2 - T + 4), T^2 + T + 4)