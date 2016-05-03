<h1>Access based global variable analysis</h1>
An access based interprocedural analysis tries to partition the data space for procedures based on the variables accessed
within a procedure and its callees. The idea is to exclude the information about variables that are not accessed by a
procedure or its callees. The project seeks to implement this module in gcc 4.7.2. The idea is to discover them locally and
then propagate information over the call graph.

In a nutshell, the project uses the intermediate representation of a C program to find out accesses of global variables in different functions. 
