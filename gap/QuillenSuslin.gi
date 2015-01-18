#############################################################################
##
##  QuillenSuslin.gi                                  LessGenerators package
##
##  Copyright 2007-2012, Mohamed Barakat, University of Kaiserslautern
##                       Anna Fabiańska, RWTH-Aachen University
##                       Vinay Wagh, Indian Institute of Technology Guwahati
##
##  Implementations for core procedures for Quillen-Suslin.
##
#############################################################################

####################################
#
# global functions and operations:
#
####################################


##
InstallMethod( QuillenSuslin,
        "for a homalg matrix",
        [ IsHomalgMatrix ],
        
  function( row )
    local S, noether, row_monic, l, monic, u, U, monic_var_index, y, R, baseR,
          Delta1, I, o, H, m, R_m, row_m, H_m, V, new_row, T, c, P, UV;
    
    if not NrRows( row ) = 1 then
        TryNextMethod( );
    elif not IsRightInvertibleMatrix( row ) then
        Error( "the matrix is not right invertible\n" );
    fi;
    
    S := HomalgRing( row );
    
    noether := NoetherNormalization( row );
    
    row_monic := noether[1];
    l := noether[2];
    
    monic := l[1];
    
    u := LeadingCoefficient( monic ) / S;
    
    Assert( 4, IsUnit( u ) );
    
    U := HomalgMatrix( [ u^-1 ], 1, 1, S );
    
    ## this gives the index of the variable w.r.t. which
    ## the new row has a monic upto a unit
    monic_var_index := l[3];
    
    if HasRelativeIndeterminatesOfPolynomialRing( S ) then
        y := RelativeIndeterminatesOfPolynomialRing( S )[monic_var_index];
    elif HasIndeterminatesOfPolynomialRing( S ) then
        y := IndeterminatesOfPolynomialRing( S )[monic_var_index];
    else
        Error( "the ring is not a polynomial ring\n" );
    fi;
    
    row := U * row_monic;
    
    Assert( 4, IsRightInvertibleMatrix( row ) );
    SetIsRightInvertibleMatrix( row, true );
    
    # l[1] is the monic (upto a unit) element in a univariate polynomial ring over a base ring
    R := HomalgRing( monic );
    baseR := BaseRing( R );
    
    Delta1 := Zero( baseR );
    
    I := ZeroLeftSubmodule( baseR );
    
    # l[2][2] gives the position of the monic (upto a unit) l[1] in the row.
    o := l[2][2];
    H := [ ];
    
    repeat
        
        m := AMaximalIdealContaining( LeftSubmodule( Delta1 ) );
        
        m := EntriesOfHomalgMatrix( MatrixOfSubobjectGenerators( m ) );
        
        R_m := LocalizeBaseRingAtPrime( R, m );
        
        row_m := R_m * row;
        
        Assert( 0, IsRightInvertibleMatrix( row_m ) );
        
        H_m := Horrocks( row_m, o );
        
        Add( H, H_m );
        
        Delta1 := Denominator( H_m[1] ) / baseR;
        
        I := I + LeftSubmodule( Delta1 );
        
    until IsOne( I );
    
    H := TransposedMatMutable( H );
    
    V := Patch( row, H[1], H[2] );
    
    V := S * V;
    
    new_row := row * V;
    
    Assert( 4, new_row = Value( row, y, Zero( y ) ) );
    
    l := GetMonicUptoUnit( new_row );
    
    if l = fail then
        Error ( "need Noether Normalization\n" );
    fi;
    
    T := CleanRowUsingMonicUptoUnit( new_row, l[2][2] );
    V := V * T[2];
    row := T[1];
    
    if HasIsSubidentityMatrix( row ) and IsSubidentityMatrix( row ) then
        
        if IsHomalgRingMap( noether[4] ) then
            U := Pullback( noether[4], U );
            V := Pullback( noether[4], V );
        fi;
        
        c := NrColumns( row );
        P := HomalgIdentityMatrix( c, S );
        
        o := NonZeroColumns( row )[1];
        
        if not o = 1 then
            P := CertainColumns( P, ListPerm( (1,o), c ) );
        fi;
        
        u := MatElm( U, 1, 1 );
        IsOne( u );
        IsMinusOne( u );
        
        return u * V * P;
    fi;
    
    ## at least one less variable
    V := V * QuillenSuslin( row );
    
    if IsHomalgRingMap( noether[4] ) then
        V := Pullback( noether[4], V );
    fi;
    
    Assert( 4, row * V = CertainRows( HomalgIdentityMatrix( NrColumns( row ), S ), [ 1 ] ) );
    
    return V;
    
end );

#! @Code QuillenSuslin_code:matrix
InstallMethod( QuillenSuslin,
        "for a homalg matrix",
        [ IsHomalgMatrix ],
        
  function( M )
    local R, m, n, V, i, UV, j, E;
    
    if NrRows( M ) = 1 then
        TryNextMethod( );
    fi;
    
    if not IsRightInvertibleMatrix( M ) then
        Error( "the matrix is not right invertible\n" );
    fi;
    
    R := HomalgRing( M );
    
    m := NrRows( M );
    n := NrColumns( M );
    
    V := [ ];
    
    for i in [ 1 .. m ] do
        
        if n = 2 then
            V[i] := RightInverse( CauchyBinetCompletion( M ) );
        elif n = 1 then
            V[i] := RightInverse( M );
        else
            V[i] := QuillenSuslin( CertainRows( M, [ 1 ] ) );
        fi;
        
        M := M * V[i];
        
        E := HomalgIdentityMatrix( i - 1, R );
        V[i] := DiagMat( [ E, V[i] ] );
        
        M := CertainRows( CertainColumns( M, [ 2 .. n ] ), [ 2 .. m ] );
        
        m := NrRows( M );
        n := NrColumns( M );
        
    od;
    
    V := Product( V );
    
    return V;
    
end );
#! @EndCode


# @Description
#  This method is invoked when NrColumns = NrRows + 1 -- (n-1) x n size 
# @Arguments M
# @Returns a list of two &homalg; matrices <A>U,V</A>, where U*V = [ ID  0 ]
# @Label For maxtrix of size $n-1 \times n$
InstallMethod( QuillenSuslin,
        "for a homalg matrix",
        [ IsHomalgMatrix ],
        
  function( M )
    
    if not NrColumns( M ) - NrRows( M ) = 1 then
        TryNextMethod( );
    fi;
    
    return CauchyBinetCompletion( M );
        
end );

#! @Description
#!  This method is invoked if gcd( N_i, N_j)=1 for some i,j,
#!  where N is the right inverse of M
#!  Assumes that M is a row matrix.
InstallMethod( QuillenSuslin,
        "for a homalg matrix",
        [ IsHomalgMatrix ],

        function( M )
    local N, n, pos, i, j, R, W, g1, g2, H;

    if not NrRows( M ) = 1 then
        TryNextMethod( );
    fi;

    N := RightInverseLazy( M );

    n := NrColumns( M );

    pos := [ ];

    for i in [ 1 .. n-1 ] do
        for j in [ i+1 .. n ] do
            if Gcd_UsingCayleyDeterminant( MatElm( N, 1, i ), MatElm( N, 1, j ) ) = 1 then
                pos := [ i, j ];
            fi;
        od;
    od;

    if pos = [ ] then
        TryNextMethod( );
    fi;

    R := HomalgRing( M );
    W := HomalgInitialIdentityMatrix( n, R );
    
    g1 := MatElm( N, 1, pos[ 1 ] );
    g1 := MatElm( N, 1, pos[ 2 ] );
    H := RightInverseLazy( HomalgMatrix( g1, g2, 1, 2, R ) );
    
    # Singular may throw an error here, as n+1 is out of bounds.
    CopyColumnToIdentityMatrix( W, i, N, n + 1 ); 
    
    SetMatElm( W, pos[ 1 ], pos[ 2 ], MatElm( H, 2, 1 ), R );
    SetMatElm( W, pos[ 2 ], pos[ 2 ], MatElm( H, 1, 1 ), R );
    
    MakeImmutable( W );
    
    
    
end );


#! @Description
#!  This method is invoked if gcd of some n-1 elements 
#!  of N is 1, where N is the right inverse of M
#!  Assumes that M is a row matrix.
InstallMethod( QuillenSuslin,
        "for a homalg matrix",
        [ IsHomalgMatrix ],
        
  function( M )
    local i, j, t, n, U, V, pos, N, NN;
    
    if not NrRows( M ) = 1 then
        TryNextMethod( );
    fi;
    
    n := NrColumns( M );
    
    for i in [ 1 .. n ] do
        r := Remove( [ 1 .. n ], i );
        MM := CertainColumns( M, r );
        L := List( [ 1 .. n - 1 ], j -> MatElm( MM, 1, j ) );
        if Gcd_UsingCayleyDeterminant( L ) = 1 then
            fi := MatElm( M, 1, i );
            break;
        fi;
    od;
    
    ## Note that at this stage MM is the required submatrix.
    N := RightInverseLazy( MM );
    
    R := HomalgRing( M );
    W := HomalgInitialIdentityMatrix( n, R );
    
    
    for i in r do
        SetMatElm( W, t, 1, ( 1 - fi ) * MatElm( N, t, 1 ), R );
    od;
    
    
end );
