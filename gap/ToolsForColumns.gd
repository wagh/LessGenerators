#############################################################################
##
##  ToolsForColumns.gd                                LessGenerators package
##
##  Copyright 2012, Mohamed Barakat, University of Kaiserslautern
##                  Vinay Wagh, Indian Institute of Technology Guwahati
##
##  Declarations for tools for columns.
##
#############################################################################

#! @Chapter Tools

####################################
#
# global functions and operations:
#
####################################

##
#! @Section Tools for columns
##

#! @Description
#!   Checks whether any $(n-1)$ elements among the $n$ <A>unclean_rows</A>
#!   positions of <A>col</A> generate a unit ideal.
#!   It returns a list [ <C>j</C>, <C>r</C>, <C>h</C> ] where
#!   * <C>j</C> = Except <C>j</C>-th entry, all other elements generate $1$
#!   * <C>r</C> = list of positions of entries that generate $1$
#!   * <C>h</C> = the left inverse of <C>r</C>-subcolumn
#! @Arguments col, unclean_rows
#! @Returns a list
DeclareOperation( "GetAllButOneGcd1RowPosition",
        [ IsHomalgMatrix, IsList ] );

#! @Description
#!   Checks whether any $(n-1)$ elements of some column of <A>M</A>
#!   generate a unit ideal.
#!   It returns a list [ <C>j</C>, <C>r</C>, <C>h</C>, <C>i</C> ] where
#!   * <C>j</C> = Except <C>j</C>-th entry, all other elements of the <C>i</C>-th
#!                column generate $1$
#!   * <C>r</C> = list of positions of entries that generate $1$
#!   * <C>h</C> = the right inverse of <C>r</C>-subcolumn
#!   * <C>i</C> = <C>i</C>-th column
#! @Arguments M
#! @Returns a list
DeclareOperation( "GetAllButOneGcd1RowPosition",
        [ IsHomalgMatrix ] );

#! @Description
#!   Checks whether there is any other monic of smaller degree than
#!   <A>o</A>-th position element. If found, returns the position of
#!   new monic, else returns <A>o</A>.
#!   It returns the position of the monic.
#! @Arguments col, o
#! @Returns a positive integer
DeclareOperation( "GetFirstMonicOfSmallestDegreeInColumn",
        [ IsHomalgMatrix, IsInt ] );

#! @Description
#!   Cleans <A>col</A> using a monic at <A>o</A>-th position.
#!   It returns a list with the modified column and transformation matrices.
#! @Arguments col, o
#! @Returns a list
DeclareOperation( "CleanColumnUsingMonicUptoUnit",
        [ IsHomalgMatrix, IsInt ] );
