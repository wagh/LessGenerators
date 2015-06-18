#############################################################################
##
##  ToolsForRows.gi                                   LessGenerators package
##
##  Copyright 2012-2015, Mohamed Barakat, University of Kaiserslautern
##                  Vinay Wagh, Indian Institute of Technology Guwahati
##
##  Implementations for tools for rows.
##
#############################################################################

####################################
#
# methods for operations:
#
####################################

##
InstallMethod( CleanRowUsingMonicUptoUnit,
        "for a homalg matrix and a positive integer",
        [ IsHomalgMatrix, IsPosInt ],
        
  function( row, o )
    local R, c, cols, a1, s, T, TI, a, row_old, t, o_new, l;
    
    if NrRows( row ) > 1 then
        Error( "only for row matrices\n" );
    fi;
    
    R := HomalgRing( row );
    
    c := NrColumns( row );
    
    cols := [ 1 .. c ];
    Remove( cols, o );
    
    a1 := MatElm( row, 1, o );
    
    Assert( 4, IsMonicUptoUnit( a1 ) );
    
    s := Degree( MatElm( row, 1, o ) );
    
    if s = 0 then
        
        T := HomalgInitialIdentityMatrix( c, R );
        Perform( cols, function( j ) SetMatElm( T, o, j, -MatElm( row, 1, j ) / a1 ); end );
        SetMatElm( T, o, o, 1 / a1 );
        MakeImmutable( T );
        
        TI := HomalgInitialIdentityMatrix( c, R );
        Perform( cols, function( j ) SetMatElm( TI, o, j, MatElm( row, 1, j ) / a1 ); end );
        SetMatElm( TI, o, o, 1 / a1 );
        MakeImmutable( TI );
        
        row := row * T;
        
        SetIsSubidentityMatrix( row, true );
        
        Assert( 4, NonZeroColumns( row ) = [ o ] );
        SetNonZeroColumns( row, [ o ] );
        
        return [ row, T, TI, o ];
        
    fi;
    
    a := EntriesOfHomalgMatrix( row );
    
    if ForAll( a{ cols }, a -> Degree( a ) < s ) then
        
        T := HomalgIdentityMatrix( c, R );
        TI := HomalgIdentityMatrix( c, R );
        return [ row, T, TI, o ];
        
    fi;
    
    row_old := row;
    
    a1 := CertainColumns( row, [ o ] );
    
    t := HomalgVoidMatrix( 1, c, R );
    
    row := DecideZeroColumnsEffectively( row, a1, t );
    row := UnionOfColumns(
                   UnionOfColumns( CertainColumns( row, [ 1 .. o - 1 ] ), a1 ),
                   CertainColumns( row, [ o + 1 .. c ] ) );
    
    cols := [ 1 .. c ];
    Remove( cols, o );
    
    T := HomalgInitialIdentityMatrix( c, R );
    Perform( cols, function( j ) SetMatElm( T, o, j, MatElm( t, 1, j ) ); end );
    MakeImmutable( T );
    
    TI := HomalgInitialIdentityMatrix( c, R );
    Perform( cols, function( j ) SetMatElm( TI, o, j, -MatElm( t, 1, j ) ); end );
    MakeImmutable( TI );
    
    Assert( 4, row = row_old * T );
    
    o_new := GetFirstMonicOfSmallestDegreeInRow( row, o );
    
    if o = o_new then
        return [ row, T, TI, o ];
    fi;
    
    l := CleanRowUsingMonicUptoUnit( row, o_new );
    
    return [ l[1], T * l[2], l[3] * TI, l[4] ];
    
end );

##
InstallMethod( CleanRowUsingMonicUptoUnit,
        "for a matrix over fake local ring and a positive integer",
        [ IsMatrixOverHomalgFakeLocalRingRep, IsPosInt ],
        
  function( row, o )
    local bool_inv, R, l, bool_id;
    
    if HasIsRightInvertibleMatrix( row ) then
        bool_inv := IsRightInvertibleMatrix( row );
    fi;
    
    R := HomalgRing( row );
    
    l := CleanRowUsingMonicUptoUnit( Eval( row ), o );
    
    if HasIsSubidentityMatrix( l[1] ) then
        bool_id := IsSubidentityMatrix( l[1] );
    fi;
    
    row := R * l[1];
    
    if IsBound( bool_id ) then
        SetIsSubidentityMatrix( row, bool_id );
    elif IsBound( bool_inv ) then
        SetIsRightInvertibleMatrix( row, bool_inv );
    fi;
    
    return [ row, R * l[2], R * l[3], l[4] ];
    
end );

##
## Given row, and given list of n positions, checks whether any 
## (n-1) elements of row at these positions generate unit ideal.
##
InstallMethod( GetAllButOneGcd1ColumnPosition,
        "for homalg row matrices",
        [ IsHomalgMatrix, IsList ],
        
  function( row, unclean_cols )
    local lc, j, r, f, h;
    
    if not NrRows( row ) = 1 then 
        TryNextMethod( );
    fi;
    
    lc := Length( unclean_cols );
    
    for j in [ 1 .. lc ] do
        r := ShallowCopy( unclean_cols );
        Remove( r, j );
        f := CertainColumns( row, r );
        h := RightInverse( f );
        
        ## Eval(h) throws an error, if h = fail.
        if not h = fail then
            ## j = Except j-th entry, all other elements generate 1
            ## r = list of positions of entries that generate 1
            ## h = the right inverse of r-column
            return [ j, r, h ];
        fi;
    od;

    return fail;
    
end );

##
## For each row in unclean_rows, apply GetAllButOneGcd1ColumnPosition
##
InstallMethod( GetAllButOneGcd1ColumnPosition,
        "for homalg matrices",
        [ IsHomalgMatrix, IsList, IsList ],
        
  function( M, unclean_rows, unclean_cols )
    local l, i;
    
    if Length( unclean_rows ) = 1 then
        l := GetAllButOneGcd1ColumnPosition( CertainRows( M, unclean_rows ), unclean_cols );
        if not l = fail then
            return [ l[1], l[2], l[3], unclean_rows[1] ];
        fi;
    fi;
    
    if Length( unclean_cols ) = 1 then
        l := GetAllButOneGcd1RowPosition( CertainColumns( M, unclean_cols ), unclean_rows );
        if not l = fail then
            return [ l[1], l[2], l[3], unclean_cols[1] ];
        fi;
    fi;
    
    for i in unclean_rows do
        l := GetAllButOneGcd1ColumnPosition( CertainRows( M, [ i ] ), unclean_cols );
        
        if not l = fail then            
            ## i = the position of the row
            ## j = Excet j-th entry, all other elements generate 1
            ## r = list of positions of entries that generate 1
            ## h = the right inverse of r-column of the i-th row
            return [ l[1], l[2], l[3], i ];            
        fi;
    od;
    
    return fail;
    
end );

##
InstallMethod( GetAllButOneGcd1ColumnPosition,
        "for homalg matrices",
        [ IsHomalgMatrix ],
        
  function( M )
    
    return GetAllButOneGcd1ColumnPosition( M, [ 1 .. NrRows( M ) ], [ 1 .. NrColumns( M ) ] );
    
end );

##
InstallMethod( GetAllButOneGcd1ColumnPosition,
        "for homalg matrices",
        [ IsHomalgMatrix ],
        
  function( row )
    
    if not NrRows( row ) = 1 then
        TryNextMethod( );
    fi;
    
    return GetAllButOneGcd1ColumnPosition( row, [ 1 .. NrColumns( row ) ] );
    
end );

##
InstallMethod( GetAllButOneGcd1ColumnPosition,
        "for homalg matrices",
        [ IsHomalgMatrix and IsZero ],
        
  function( M )
    
    return fail;
    
end );

##
InstallMethod( GetFirstMonicOfSmallestDegreeInRow,
        "for a homalg row matrix and positive integer",
        [ IsHomalgMatrix, IsInt ],
  function( row, o )
    local c, cols, deg_h, l, min;
    
    if NrRows( row ) > 1 then
        Error( "only for row matrices\n" );
    fi;
    
    c := NrColumns( row );
    cols := [ 1 .. c ];
    
    deg_h := Degree( MatElm( row, 1, o ) );

    l := List( cols, function( i )
        local a, deg_a;
        a := MatElm( row, 1, i );
        deg_a := Degree( a );
        
        if deg_a < deg_h and IsMonic( a ) then
            return deg_a;
        fi;
        return deg_h;
    end );
    
    min := Minimum( l );
    if min < deg_h then
        o := Position( l, min );
    fi;
    
    return o;
    
end );

##
InstallMethod( EliminateAllButOneGcd1Columns,
        "for homalg matrices",
        [ IsHomalgMatrix ],
        
  function( row )
    local l, R, n, W, WI, fj, rowinv, i, gi, T, P, V, VI;
    
    Info( InfoQuillenSuslin, 4, "Entering Eliminate-All-But-1-Gcd-1-Column" );
    
    if not NrRows( row ) = 1 then 
        TryNextMethod( );
    fi;
    
    l := GetAllButOneGcd1ColumnPosition( row );
    
    if l = fail then
        return fail;
    fi;
    
    R := HomalgRing( row );
    
    n := NrColumns( row );
    
    W := HomalgInitialIdentityMatrix( n, R );
    WI := HomalgInitialIdentityMatrix( n, R );
    
    fj := MatElm( row, 1, l[1] );
    rowinv := l[3];
    
    for i in [ 1 .. n ] do
        if i < l[1] then
            gi := MatElm( rowinv, i, 1 ) * (1 - fj);
            SetMatElm( W, i, l[1], gi );
            SetMatElm( WI, i, l[1], -gi );
        elif i > l[1] then
            gi := MatElm( rowinv, i - 1, 1 ) * (1 - fj);
            SetMatElm( W, i, l[1], gi );
            SetMatElm( WI, i, l[1], -gi );
        fi;
    od;
    MakeImmutable( W );
    MakeImmutable( WI );
    
    row := row * W;
    Assert( 4, IsOne( MatElm( row, 1, l[1] ) ) );
    
    T := CleanRowUsingMonicUptoUnit( row, l[1] );
    
    P := HomalgIdentityMatrix( n, R );
    if not l[1] = 1 then
        P := CertainRows( P, ListPerm( ( 1, l[1] ), n ) );
    fi;
    
    row := row * T[2] * P;
    Assert( 4, IsOne( MatElm( row, 1, 1 ) ) );
    Assert( 4, ZeroColumns( row ) = [ 2 .. n ] );
    
    V := W * T[2] * P;
    VI := P * T[3] * WI;
    
    Info( InfoQuillenSuslin, 4, "Leaving Eliminate-All-But-1-Gcd-1-Column" );
    
    return [ V, VI ];
    
end );
