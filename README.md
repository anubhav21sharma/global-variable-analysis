An access based interprocedural analysis tries to partition the data space for procedures based on the variables accessed
within a procedure and its callees. The idea is to exclude the information about variables that are not accessed by a
procedure or its callees. The project seeks to implement this module in gcc 4.7.2. The idea is to discover them locally and
then propagate information over the call graph.