#############################################################################
##
##  ToolsForRow.gd                                    LessGenerators package
##
##  Copyright 2012, Mohamed Barakat, University of Kaiserslautern
##                  Vinay Wagh, Indian Institute of Technology Guwahati
##
##  Declarations for tools for rows.
##
#############################################################################

#! @Chapter Tools

####################################
#
# global functions and operations:
#
####################################

##
#! @Section Tools for rows
##

#! @Description
#!   Checks whether there is any other monic of smaller degree than
#!   <A>o</A>-th position element. If found, returns the position of
#!   new monic, else returns <A>o</A>.
#!   It returns the position of the monic.
#! @Arguments row, o
#! @Returns a positive integer
DeclareOperation( "GetFirstMonicOfSmallestDegreeInRow",
        [ IsHomalgMatrix, IsInt ] );

#! @Description
#!   Cleans <A>row</A> using a monic at <A>o</A>-th position.
#!   It returns a list with the modified row and the transformation matrices.
#! @Arguments row, o
#! @Returns a list
DeclareOperation( "CleanRowUsingMonicUptoUnit",
        [ IsHomalgMatrix, IsInt ] );

#! @Description
#!   Checks whether any $(n-1)$ elements among the $n$ <A>unclean_cols</A>
#!   positions of <A>row</A> generate a unit ideal.
#!   It returns a list [ <C>j</C>, <C>r</C>, <C>h</C> ] where
#!   * <C>j</C> = Except <C>j</C>-th entry, all other elements generate $1$
#!   * <C>r</C> = list of positions of entries that generate $1$
#!   * <C>h</C> = the right inverse of <C>r</C>-subrow
#! @Arguments row, unclean_cols
#! @Returns a list
DeclareOperation( "GetAllButOneGcd1ColumnPosition",
        [ IsHomalgMatrix, IsList ] );

#! @Description
#!   Checks whether any $(n-1)$ elements among the $n$ <A>unclean_cols</A>
#!   positions of one of the rows among <A>unclean_rows</A> generate a
#!   unit ideal.
#!   It returns a list [ <C>j</C>, <C>r</C>, <C>h</C>, <C>i</C> ] where
#!   * <C>j</C> = Except <C>j</C>-th entry, all other elements of the <C>i</C>-th
#!                row generate $1$
#!   * <C>r</C> = list of positions of entries that generate $1$
#!   * <C>h</C> = the right inverse of <C>r</C>-subrow
#!   * <C>i</C> = <C>i</C>-th row
#! @Arguments M, unclean_rows, unclean_cols
#! @Returns a list
DeclareOperation( "GetAllButOneGcd1ColumnPosition",
        [ IsHomalgMatrix, IsList, IsList ] );

#! @Description
#!   Checks whether any $(n-1)$ elements of some row of <A>M</A>
#!   generate a unit ideal.
#!   It returns a list [ <C>j</C>, <C>r</C>, <C>h</C>, <C>i</C> ] where
#!   * <C>j</C> = Except <C>j</C>-th entry, all other elements of the <C>i</C>-th
#!                row generate $1$
#!   * <C>r</C> = list of positions of entries that generate $1$
#!   * <C>h</C> = the right inverse of <C>r</C>-subcolumn
#!   * <C>i</C> = <C>i</C>-th row
#! @Arguments M
#! @Returns a list
DeclareOperation( "GetAllButOneGcd1ColumnPosition",
        [ IsHomalgMatrix ] );

#! @Description
#!   If any $(n-1)$ elements of the row generate $1$, then this function
#!   cleans the <A>row</A> and returns the transformation matrix and its
#!   inverse.
#!   It returns a list of two matrices <C>V</C> and <C>VI</C> such that
#!   <A>row</A> * <C>V</C> = [ 1 0 0 ... 0 ] and the first row
#!   of <C>VI</C> is the given row.
#! @InsertSystem Eliminate-All-But-One-Gcd-1-Columns
#! @Arguments row
#! @Returns a list
DeclareOperation( "EliminateAllButOneGcd1Columns",
        [ IsHomalgMatrix ] );

#! @Description
#!   Checks whether any two elements of <A>row</A> are coprime.
#!   It returns a list [ <C>l</C>, [ <C>i</C>, <C>j</C> ] ] where
#!   * <C>i</C> and  <C>j</C>-th elements are coprime with each other
#!   * <C>l</C> is the syzygy of these two elements.
#! @Arguments row
#! @Returns a list
DeclareOperation( "GetPairOfGcd1PositionPerRow",
        [ IsHomalgMatrix ] );

#! @Description
#!   If any two elements of <A>row</A> are coprime, then this function
#!   cleans the <A>row</A> and returns the transformation matrix and
#!   its inverse.
#!   It returns a list of two matrices <C>V</C> and <C>VI</C> such that
#!   <A>row</A> * <C>V</C> = [ 1 0 0 ... 0 ] and the first row
#!   of <C>VI</C> is the given row.
#! @InsertSystem Eliminate-Pair-Of-Gcd-1-Position-Per-Row
#! @Arguments row
#! @Returns a list
DeclareOperation( "EliminatePairOfGcd1PositionPerRow",
        [ IsHomalgMatrix ] );

#! @Description
#!   The <A>row</A> contains a unit, then this function cleans 
#!   the <A>row</A> using this unit and return the transformation
#!   matrices.
#!   It returns a list of two matrices <C>V</C> and <C>VI</C> such that
#!   <A>row</A> * <C>V</C> = [ 1 0 0 ... 0 ] and the first row
#!   of <C>VI</C> is the given row.
#! @Arguments row
#! @Returns a list
DeclareOperation( "EliminateUnitInARow",
        [ IsHomalgMatrix ] );